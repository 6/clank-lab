#!/usr/bin/env python3
"""Build a small paper website from public Zenodo records (Python 3.9+)."""

import argparse
from datetime import date
from email.utils import parsedate_to_datetime
import hashlib
import html
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import shutil
import sys
import time
from urllib.error import HTTPError
from urllib.parse import urlencode, urlsplit
from urllib.request import Request, urlopen

from figures import FIGURES, FIGURE_FILE, read_figure
from maths import render_html
from releases import paper_release_links
from summaries import paper_summaries

API = "https://zenodo.org/api/records"
DOI_BASE = "https://doi.org/"
ORCID = "0009-0007-8493-1505"
BASE_URL = "https://clanklab.org/"
MAX_PDF = 5_000_000  # Decimal MB, conservatively below 5 MiB.
PDF_LINK_LABEL = "Read the paper (PDF) →"
AI_CREDIT = "Produced by AI models under the author's direction."
AI_CREDIT_HTML = html.escape(AI_CREDIT)
AI_CREDIT_LINE = re.compile(r"<p>\s*" + re.escape(AI_CREDIT_HTML) + r"\s*</p>|\s*"
                            + re.escape(AI_CREDIT_HTML) + r"(?=\s*(?:</p>|$))")
# Require a disclosure about the paper itself before removing the short credit.
AUTHOR_AI_ATTRIBUTION = re.compile(
    r"\b(?:(?:were|was) (?:produced|generated|written|developed) by AI (?:models?|systems?)\b"
    r"[^.!?]*\bunder the author['’]s direction"
    r"|this (?:paper|work|study) (?:was|is) (?:assisted by AI"
    r"|(?:produced|generated|written|developed) (?:by AI|with AI assistance)))\b", re.IGNORECASE)
STYLE = """:root{color-scheme:light dark;--bg:#fff;--text:#18202b;--muted:#596270;--link:#245e91;--line:#dce1e7}
*{box-sizing:border-box}html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--text);font:17px/1.7 -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}
main{max-width:40rem;margin:0 auto;padding:2.5rem 1.125rem 4rem}
h1{font-size:clamp(1.65rem,5vw,2.2rem);line-height:1.25;letter-spacing:-.025em;margin:0 0 1rem}
h1,p,li,code,a{overflow-wrap:anywhere}a{color:var(--link);text-underline-offset:.18em}
a:focus-visible{outline:2px solid currentColor;outline-offset:3px}
.papers{list-style:none;margin:1.5rem 0;padding:0}.papers li{border-top:1px solid var(--line);padding:1.3rem 0}
.paper-title{display:flex;align-items:center;min-height:44px;font-size:1.1rem;line-height:1.45;font-weight:600;text-decoration:none}
math[display="block"]{display:block;overflow-x:auto;padding:.25em 0}
time,.authors{color:var(--muted)}time{font-size:.9rem}
.links{display:flex;flex-wrap:wrap;align-items:center;gap:.25rem 1rem;margin:.15rem 0 0}
.links a{display:inline-flex;align-items:center;min-height:44px;max-width:100%;font-size:.9rem}
@media(prefers-color-scheme:dark){:root{--bg:#111418;--text:#e8edf3;--muted:#aab4c3;--link:#91bfff;--line:#333e4d}}"""


PAPER_STYLE = """
.publication-date{margin:0}
.update-date{margin:0;color:var(--muted);font-size:.8125rem}
.publication-date time,.update-date time{font:inherit;color:inherit}
.paper-summary{margin:1rem 0 1.5rem;padding:clamp(.75rem,4vw,1rem);border:1px solid var(--line);border-radius:.5rem;background:#f4f7fa}
.paper-summary h2{font-size:1rem;line-height:1.35;margin:0 0 .4rem}
.summary-text{font-size:1.125rem;line-height:1.6;margin:0}
.links .paper-pdf{padding:.45rem .875rem;border:1px solid var(--link);border-radius:.375rem;background:var(--link);color:var(--bg);font-size:.9375rem;font-weight:600;text-decoration:none}
.paper-pdf:hover{text-decoration:underline}
.paper-pdf:focus-visible{outline-color:var(--link)}
#paper-abstract-heading{font-size:1.25rem;line-height:1.35;margin:0 0 .65rem}
.abstract-text>p:first-child{margin-top:0}
@media(prefers-color-scheme:dark){.paper-summary{background:#1a2129}}"""

FIGURE_STYLE = """
.paper-figure{margin:1.5rem 0}
.paper-figure img{display:block;max-width:100%;height:auto;background:white;margin:0 auto}
.paper-figure figcaption{color:var(--muted);font-size:.9rem;margin-top:.5rem}"""


def public_url(url):
    parsed = urlsplit(url)
    if parsed.scheme != "https" or parsed.netloc != "zenodo.org":
        raise ValueError("Download/API URL must be on https://zenodo.org")
    return url


def fetch(url, destination=None, *, landing_record=None):
    """Read Zenodo metadata or files, or verify a DOI's Zenodo landing page."""
    if landing_record is None:
        public_url(url)
    elif not re.fullmatch(r"https://doi\.org/10\.5281/zenodo\.\d+", url):
        raise ValueError(f"Invalid Zenodo DOI URL: {url}")
    for attempt in range(5):
        try:
            request = Request(url, headers={"User-Agent": "ZenodoPaperSite/1.0"})
            with urlopen(request, timeout=60) as response:
                public_url(response.url)
                if landing_record is not None:
                    path = urlsplit(response.url).path.rstrip("/")
                    if response.status != 200 or path not in {f"/records/{landing_record}", f"/record/{landing_record}"}:
                        raise ValueError(f"{url} resolved to {response.url}, expected Zenodo record {landing_record}")
                    return
                if destination is None:
                    return json.load(response)
                with destination.open("wb") as stream:
                    while chunk := response.read(128 * 1024):
                        stream.write(chunk)
            return
        except HTTPError as error:
            if error.code not in (429, 500, 502, 503, 504) or attempt == 4:
                raise
            delay = 60 if error.code == 429 else 2 ** attempt
            retry_after = error.headers.get("Retry-After")
            if retry_after:
                try:
                    delay = max(delay, float(retry_after))
                except ValueError:
                    delay = max(delay, parsedate_to_datetime(retry_after).timestamp() - time.time())
            print(f"Retrying HTTP {error.code} in {delay:.0f}s ({attempt + 1}/4)", file=sys.stderr)
            # Bound each pause so the caller can interrupt long server backoffs.
            while delay > 0:
                pause = min(delay, 60)
                time.sleep(pause)
                delay -= pause


def records(url):
    seen = set()
    while url:
        result = fetch(url)
        hits = result["hits"]["hits"]
        for record in hits:
            if record["id"] in seen:
                raise ValueError("Repeated record while paging Zenodo; retry the build")
            seen.add(record["id"])
            yield record
        total = result["hits"]["total"]
        if isinstance(total, dict):
            total = total["value"]
        url = result.get("links", {}).get("next")
        if not url and len(seen) == total:
            return
        if not hits or not url:
            raise ValueError("Zenodo pagination ended before the reported total")


def public_papers():
    params = dict(q="creators.orcid:" + ORCID, all_versions="false", size=25, page=1, sort="-mostrecent")
    seen = set()
    for record in records(API + "?" + urlencode(params)):
        metadata = record["metadata"]
        if metadata["resource_type"]["type"] != "publication":
            continue
        if not any(person.get("orcid") == ORCID for person in metadata["creators"]):
            raise ValueError("Search returned a record without the requested author")
        if not version_relation(record)["is_last"]:
            raise ValueError("Search returned an old version")
        if record["conceptdoi"] in seen:
            raise ValueError("Duplicate concept DOI")
        seen.add(record["conceptdoi"])
        yield record


def version_relation(record):
    return record["metadata"]["relations"]["version"][0]


def versions_of(record):
    relation = version_relation(record)
    if relation["index"] == 0 and relation["is_last"]:
        return [record]
    return list(records(record["links"]["versions"]))


def displayed_versions(record, versions):
    concept = record["conceptdoi"]
    if any(item["conceptdoi"] != concept for item in versions):
        raise ValueError(f"Unrelated Zenodo version returned for {concept}")
    first = [item for item in versions if version_relation(item)["index"] == 0]
    latest = [item for item in versions if version_relation(item)["is_last"]]
    if len(first) != 1 or [item["id"] for item in latest] != [record["id"]]:
        raise ValueError(f"Cannot identify first and latest Zenodo versions for {concept}")
    selected = first if first[0]["id"] == latest[0]["id"] else first + latest
    display = []
    for item in selected:
        doi = item["doi"]
        if doi == concept or not re.fullmatch(r"10\.5281/zenodo\.\d+", doi):
            raise ValueError(f"Invalid Zenodo version DOI for record {item['id']}")
        # Display Zenodo's metadata.publication_date for every version.
        day = date.fromisoformat(item["metadata"]["publication_date"]).isoformat()
        display.append(dict(number=version_relation(item)["index"] + 1, date=day, doi=doi, record_id=item["id"]))
    return display


def version_date(day):
    published = date.fromisoformat(day)
    months = ("Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec")
    return f"{months[published.month - 1]} {published.day}, {published.year}"


def version_date_line(version, *, updated=False, show_number=False):
    day = version["date"]
    published = f'<time datetime="{day}">{version_date(day)}</time>'
    if updated:
        return f'<p class="update-date">Updated {published} (version {version["number"]})</p>'
    number = f' (version {version["number"]})' if show_number else ""
    return f'<p class="publication-date">Published {published}{number}</p>'


def match_results(checkout, papers, identities, previous):
    """Use retained folder identities, exact PDF hashes, then public DOI references.

    The individual result folders' README files are used only for matching.
    """
    root = checkout / "results"
    if not root.is_dir() or root.is_symlink():
        raise ValueError("Checkout must contain a results directory")
    retained = {p["slug"]: p["concept_doi"] for p in previous}
    old_slugs = {p["concept_doi"]: p["slug"] for p in previous}
    by_doi = {p["concept_doi"]: p for p in papers}
    assigned, sources, failures = set(), {}, []
    for folder in sorted(root.iterdir()):
        if not folder.is_dir():
            continue
        slug = folder.name
        if folder.is_symlink() or not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", slug):
            raise ValueError("Invalid or linked result folder")
        readme, pdf = folder / "README.md", folder / "paper" / "paper.pdf"
        if readme.is_symlink() or (folder / "paper").is_symlink() or pdf.is_symlink():
            raise ValueError("Linked source file in result " + slug)
        digest = hashlib.md5(pdf.read_bytes()).hexdigest() if pdf.is_file() else None
        paper = by_doi.get(retained.get(slug))
        if paper is None:
            matches = [p for p in papers if p["pdf_md5"] == digest]
            if len(matches) == 1:
                paper = matches[0]
        if paper is None:
            references = set(re.findall(r"10\.5281/zenodo\.\d+", readme.read_text(encoding="utf-8"))) if readme.is_file() else set()
            matches = [p for p in papers if identities[p["concept_doi"]] & references]
            if len(matches) == 1:
                paper = matches[0]
        if paper is None:
            failures.append("Cannot uniquely match result " + slug + " to a public Zenodo paper")
            continue
        doi = paper["concept_doi"]
        old_slug = old_slugs.get(doi)
        if old_slug and old_slug != slug:
            failures.append("Stable result slug changed for " + doi)
        if doi in assigned:
            failures.append("Multiple result folders match " + doi)
            continue
        assigned.add(doi)
        paper["slug"] = slug
        sources[doi] = pdf if pdf.is_file() else None
        if digest is not None and (digest != paper["pdf_md5"] or pdf.stat().st_size != paper["pdf_size"]):
            failures.append(f"PDF mismatch for {slug}: local MD5={digest}, size={pdf.stat().st_size}; "
                            f"latest Zenodo MD5={paper['pdf_md5']}, size={paper['pdf_size']}")
    failures += ["No result folder matches " + doi for doi in sorted(set(by_doi) - assigned)]
    if failures:
        raise ValueError("\n".join(failures))
    return sources


class AbstractHTML(HTMLParser):
    """Keep basic public abstract formatting, without attributes or assets."""
    allowed = {"p", "br", "em", "strong", "b", "i", "sub", "sup", "ul", "ol", "li", "code"}
    blocked = {"script", "style", "iframe", "object", "svg"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.hidden = 0

    def handle_starttag(self, tag, attrs):
        if tag in self.blocked:
            self.hidden += 1
        elif not self.hidden and tag in self.allowed:
            self.parts.append("<" + tag + ">")

    def handle_endtag(self, tag):
        if tag in self.blocked:
            self.hidden = max(0, self.hidden - 1)
        elif not self.hidden and tag in self.allowed and tag != "br":
            self.parts.append("</" + tag + ">")

    def handle_data(self, text):
        if not self.hidden:
            self.parts.append(html.escape(text))


def abstract_html(source):
    parser = AbstractHTML()
    parser.feed(source)
    parser.close()
    return "".join(parser.parts)


def paper_abstract(source):
    abstract = abstract_html(source)
    without_credit, count = AI_CREDIT_LINE.subn("", abstract)
    text = html.unescape(re.sub(r"<[^>]+>", "", without_credit))
    text = " ".join(text.split())
    if not text and not count:
        raise ValueError("Missing Zenodo abstract")
    if AUTHOR_AI_ATTRIBUTION.search(text):
        return without_credit, False
    return (abstract if count else abstract + f"<p>{AI_CREDIT_HTML}</p>"), True


def document(title, body, tags=(), extra_style=""):
    meta = "\n".join(f'<meta name="{name}" content="{html.escape(value, quote=True)}">'
                     for name, value in tags)
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8">\n'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">\n'
            f'<title>{html.escape(title)}</title>\n{meta}\n'
            f'<style>{STYLE}{extra_style}</style>\n'
            f'</head><body><main>{render_html(body)}</main></body></html>\n')


def download(paper, url, destination, source=None):
    temporary = destination.with_suffix(".part")
    try:
        if source is None:
            fetch(url, temporary)
        else:
            shutil.copyfile(source, temporary)
        digest = hashlib.md5()
        with temporary.open("rb") as stream:
            if stream.read(5) != b"%PDF-":
                raise ValueError("Downloaded file is not a PDF")
            stream.seek(0)
            while chunk := stream.read(128 * 1024):
                digest.update(chunk)
        if temporary.stat().st_size != paper["pdf_size"]:
            raise ValueError(f"PDF size mismatch for {paper['slug']}: expected {paper['pdf_size']}, got {temporary.stat().st_size}")
        if digest.hexdigest() != paper["pdf_md5"]:
            raise ValueError(f"PDF checksum mismatch for {paper['slug']}: expected {paper['pdf_md5']}, got {digest.hexdigest()}")
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)


def paper_figure(checkout, slug, folder):
    entry = FIGURES.get(slug)
    if entry is None:
        return ""
    try:
        data = read_figure(checkout, slug, entry)
    except (OSError, ValueError) as error:
        print(f"WARNING: Skipping figure for {slug}: {error}", file=sys.stderr)
        return ""
    (folder / FIGURE_FILE).write_bytes(data)
    alt, caption = html.escape(entry["alt"], quote=True), html.escape(entry["caption"])
    return (f'<figure class="paper-figure"><img src="{FIGURE_FILE}" alt="{alt}">'
            f'<figcaption>{caption}</figcaption></figure>')


def build(checkout, output, base_url, manifest):
    parsed = urlsplit(base_url)
    if (parsed.scheme not in ("http", "https") or not parsed.hostname
            or parsed.username or parsed.password or parsed.query or parsed.fragment
            or re.search(r"[\s<>\"\\]", base_url)):
        raise ValueError("--base-url must be an absolute HTTP(S) URL without query or fragment")
    base_url = base_url.rstrip("/") + "/"
    if output.exists() and any(output.iterdir()):
        raise ValueError("Output directory must be empty (use a fresh output directory)")
    previous = json.loads(manifest.read_text(encoding="utf-8")) if manifest.exists() else []
    papers, urls, identities, paper_versions = [], {}, {}, {}
    for record in public_papers():
        metadata = record["metadata"]
        doi = record["conceptdoi"]
        pdfs = [item for item in record.get("files", []) if item["key"].lower().endswith(".pdf")]
        if len(pdfs) != 1:
            raise ValueError(f"Expected exactly one paper PDF in record {record['id']}")
        pdf = pdfs[0]
        if not re.fullmatch(r"md5:[0-9a-f]{32}", pdf["checksum"]):
            raise ValueError("Missing or unsupported Zenodo PDF checksum")
        versions = versions_of(record)
        display = paper_versions[doi] = displayed_versions(record, versions)
        identities[doi] = {doi} | {v["doi"] for v in versions}
        paper = dict(title=metadata["title"], authors=[p["name"] for p in metadata["creators"]],
                     first_version_date=display[0]["date"], concept_doi=doi,
                     latest_record_id=record["id"], pdf_filename=pdf["key"],
                     pdf_md5=pdf["checksum"][4:], pdf_size=pdf["size"], abstract=metadata["description"])
        papers.append(paper)
        urls[doi] = pdf["links"]["self"]
    if not papers:
        raise ValueError("No public papers found; refusing to replace the manifest")
    sources = match_results(checkout, papers, identities, previous)
    release_links = paper_release_links(checkout, (paper["slug"] for paper in papers))
    summaries = paper_summaries(checkout, (paper["slug"] for paper in papers))
    papers.sort(key=lambda p: (p["first_version_date"], p["slug"]), reverse=True)
    output.mkdir(parents=True, exist_ok=True)
    listing, locations, warnings = [], [base_url], []
    credits = 0
    for paper in papers:
        slug, title = paper["slug"], paper["title"]
        folder = output / "papers" / slug
        folder.mkdir(parents=True)
        source = sources[paper["concept_doi"]]
        if source is None:
            print("Local PDF missing for " + slug + "; downloading the verified latest Zenodo PDF", file=sys.stderr)
        download(paper, urls[paper["concept_doi"]], folder / (slug + ".pdf"), source)
        page_url = base_url + "papers/" + slug + "/"
        tags = [("citation_title", title)]
        tags += [("citation_author", author) for author in paper["authors"]]
        tags += [("citation_publication_date", paper["first_version_date"].replace("-", "/")),
                 ("citation_pdf_url", page_url + slug + ".pdf"),
                 ("citation_doi", paper["concept_doi"]), ("citation_publisher", "Zenodo")]
        doi_url = DOI_BASE + paper["concept_doi"]
        figure = paper_figure(checkout, slug, folder)
        release_url = release_links.get(slug)
        code_link = f'<a href="{release_url}">Code and proofs</a>' if release_url else ""
        versions = paper_versions[paper["concept_doi"]]
        multiple_versions = len(versions) > 1
        published = version_date_line(versions[0], show_number=multiple_versions)
        updated = version_date_line(versions[1], updated=True) if multiple_versions else ""
        doi_link = f'<a class="paper-doi" href="{doi_url}">DOI</a>'
        pdf_link = f'<a class="paper-pdf" href="{slug}.pdf">{PDF_LINK_LABEL}</a>'
        abstract, kept_credit = paper_abstract(paper["abstract"])
        credits += kept_credit
        body = ('<nav class="links" aria-label="Site"><a href="../../">All papers</a></nav>'
                f'<h1>{html.escape(title)}</h1><p class="authors">{html.escape("; ".join(paper["authors"]))}</p>'
                f'{published}{updated}<p class="links">{pdf_link}</p><p class="links">{doi_link}{code_link}</p>'
                '<section class="paper-summary" aria-labelledby="paper-summary-heading">'
                '<h2 id="paper-summary-heading">In short</h2>'
                f'<p class="summary-text">{html.escape(summaries[slug])}</p></section>'
                '<section aria-labelledby="paper-abstract-heading">'
                '<h2 id="paper-abstract-heading">Abstract</h2>'
                f'<div class="abstract-text">{abstract}</div></section>{figure}')
        extra_style = PAPER_STYLE + (FIGURE_STYLE if figure else "")
        (folder / "index.html").write_text(document(title, body, tags, extra_style), encoding="utf-8")
        listing.append(f'<li><a class="paper-title" href="papers/{slug}/"><span>{html.escape(title)}</span></a>'
                       f'<div class="links"><time datetime="{paper["first_version_date"]}">{paper["first_version_date"]}</time>'
                       f'<a href="{doi_url}">DOI</a><a href="papers/{slug}/{slug}.pdf">PDF</a></div></li>')
        locations.append(page_url)
        if paper["pdf_size"] > MAX_PDF:
            warnings.append(f"PDF exceeds 5 MB: {slug} ({paper['pdf_size']} bytes)")
    index = f'<h1>Papers</h1><p>{AI_CREDIT_HTML}</p><ul class="papers">' + "\n".join(listing) + "</ul>"
    (output / "index.html").write_text(document("Papers", index), encoding="utf-8")
    (output / "robots.txt").write_text(f"User-agent: *\nAllow: /\nSitemap: {base_url}sitemap.xml\n", encoding="utf-8")
    sitemap = '<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
    sitemap += "".join("<url><loc>" + html.escape(url) + "</loc></url>\n" for url in locations) + "</urlset>\n"
    (output / "sitemap.xml").write_text(sitemap, encoding="utf-8")
    manifest.write_text(json.dumps(papers, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    largest = max(papers, key=lambda p: p["pdf_size"])
    local = sum(source is not None for source in sources.values())
    print(f"PDF sources: {local} local; {len(papers) - local} Zenodo downloads")
    print(f"Standalone AI credit: {credits} kept; {len(papers) - credits} omitted")
    print(f"Built {len(papers)} papers; largest PDF: {largest['pdf_size']:,} bytes ({largest['slug']}); warnings: {len(warnings)}")
    for warning in warnings:
        print("WARNING: " + warning)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="Public clank-lab checkout containing results/*/paper/paper.pdf")
    parser.add_argument("output", type=Path, help="Empty output directory")
    parser.add_argument("--base-url", default=BASE_URL, help="Public site root (default: %(default)s)")
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("papers.json"))
    args = parser.parse_args()
    try:
        build(args.checkout, args.output, args.base_url, args.manifest)
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"Build failed: {error}\n")


if __name__ == "__main__":
    main()
