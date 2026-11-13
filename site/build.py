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

API = "https://zenodo.org/api/records"
ORCID = "0009-0007-8493-1505"
BASE_URL = "https://6.github.io/clank-lab/"
MAX_PDF = 5_000_000  # Decimal MB, conservatively below 5 MiB.
STYLE = """:root{color-scheme:light dark;--bg:#fff;--text:#18202b;--muted:#596270;--link:#245e91;--line:#dce1e7}
*{box-sizing:border-box}html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--text);font:17px/1.7 -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}
main{max-width:40rem;margin:0 auto;padding:2.5rem 1.125rem 4rem}
h1{font-size:clamp(1.65rem,5vw,2.2rem);line-height:1.25;letter-spacing:-.025em;margin:0 0 1rem}
h1,p,li,code,a{overflow-wrap:anywhere}a{color:var(--link);text-underline-offset:.18em}
a:focus-visible{outline:2px solid currentColor;outline-offset:3px}
.papers{list-style:none;margin:1.5rem 0;padding:0}.papers li{border-top:1px solid var(--line);padding:1.3rem 0}
.paper-title{display:flex;align-items:center;min-height:44px;font-size:1.1rem;line-height:1.45;font-weight:600;text-decoration:none}
time,.authors{color:var(--muted)}time{font-size:.9rem}
.links{display:flex;flex-wrap:wrap;align-items:center;gap:.25rem 1rem;margin:.15rem 0 0}
.links a{display:inline-flex;align-items:center;min-height:44px;max-width:100%;font-size:.9rem}
@media(prefers-color-scheme:dark){:root{--bg:#111418;--text:#e8edf3;--muted:#aab4c3;--link:#91bfff;--line:#333e4d}}"""


def public_url(url):
    parsed = urlsplit(url)
    if parsed.scheme != "https" or parsed.netloc != "zenodo.org":
        raise ValueError("Download/API URL must be on https://zenodo.org")
    return url


def fetch(url, destination=None):
    """Retry transient HTTP errors; stream files and verify them separately."""
    public_url(url)
    for attempt in range(5):
        try:
            request = Request(url, headers={"User-Agent": "ZenodoPaperSite/1.0"})
            with urlopen(request, timeout=60) as response:
                public_url(response.url)
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


def records(query, all_versions=False):
    page = 1
    seen = set()
    while True:
        params = dict(q=query, all_versions=str(all_versions).lower(),
                      size=25, page=page, sort="-mostrecent")
        result = fetch(API + "?" + urlencode(params))
        hits = result["hits"]["hits"]
        for record in hits:
            if record["id"] in seen:
                raise ValueError("Repeated record while paging Zenodo; retry the build")
            seen.add(record["id"])
            yield record
        total = result["hits"]["total"]
        if isinstance(total, dict):
            total = total["value"]
        if not result.get("links", {}).get("next") and len(seen) >= total:
            return
        if not hits:
            raise ValueError("Zenodo pagination ended before the reported total")
        page += 1


def version_index(record):
    versions = record["metadata"].get("relations", {}).get("version", [])
    return versions[0].get("index") if versions else None


def versions_of(record):
    return [record] if version_index(record) == 0 else list(records("conceptrecid:" + str(record["conceptrecid"]), True))


def first_date(record, versions=None):
    if version_index(record) == 0:
        first = record
    else:
        versions = versions if versions is not None else versions_of(record)
        first = next((item for item in versions if version_index(item) == 0), None)
        if first is None:
            raise ValueError(f"Cannot identify first version of {record['id']}")
    return date.fromisoformat(first["metadata"]["publication_date"]).isoformat()


def match_results(checkout, papers, identities, previous):
    """Use retained folder identities, exact PDF hashes, then public DOI references.

    README text is used only for matching; it never becomes site content.
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


def document(title, body, tags=()):
    meta = "\n".join(f'<meta name="{name}" content="{html.escape(value, quote=True)}">'
                     for name, value in tags)
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8">\n'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">\n'
            f'<title>{html.escape(title)}</title>\n{meta}\n<style>{STYLE}</style>\n'
            f'</head><body><main>{body}</main></body></html>\n')


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
    papers, urls, identities = [], {}, {}
    for record in records("creators.orcid:" + ORCID):
        metadata = record["metadata"]
        if metadata["resource_type"]["type"] != "publication":
            continue
        if not any(person.get("orcid") == ORCID for person in metadata["creators"]):
            raise ValueError("Search returned a record without the requested author")
        relations = metadata.get("relations", {}).get("version", [])
        if relations and not relations[0]["is_last"]:
            raise ValueError("Search returned an old version")
        doi = record["conceptdoi"]
        if doi in urls:
            raise ValueError("Duplicate concept DOI")
        pdfs = [item for item in record.get("files", []) if item["key"].lower().endswith(".pdf")]
        if len(pdfs) != 1:
            raise ValueError(f"Expected exactly one paper PDF in record {record['id']}")
        pdf = pdfs[0]
        if not re.fullmatch(r"md5:[0-9a-f]{32}", pdf["checksum"]):
            raise ValueError("Missing or unsupported Zenodo PDF checksum")
        versions = versions_of(record)
        identities[doi] = {doi} | {v["doi"] for v in versions}
        paper = dict(title=metadata["title"], authors=[p["name"] for p in metadata["creators"]],
                     first_version_date=first_date(record, versions), concept_doi=doi,
                     latest_record_id=record["id"], pdf_filename=pdf["key"],
                     pdf_md5=pdf["checksum"][4:], pdf_size=pdf["size"], abstract=metadata["description"])
        papers.append(paper)
        urls[doi] = pdf["links"]["self"]
    if not papers:
        raise ValueError("No public papers found; refusing to replace the manifest")
    sources = match_results(checkout, papers, identities, previous)
    papers.sort(key=lambda p: (p["first_version_date"], p["slug"]), reverse=True)
    output.mkdir(parents=True, exist_ok=True)
    listing, locations, warnings = [], [base_url], []
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
        doi_url = "https://doi.org/" + paper["concept_doi"]
        body = ('<nav class="links" aria-label="Site"><a href="../../">All papers</a></nav>'
                f'<h1>{html.escape(title)}</h1><p class="authors">{html.escape("; ".join(paper["authors"]))}</p>'
                f'<p><time datetime="{paper["first_version_date"]}">{paper["first_version_date"]}</time></p>'
                f'<section aria-label="Abstract">{abstract_html(paper["abstract"])}</section>'
                f'<p class="links"><a href="{doi_url}">{paper["concept_doi"]}</a>'
                f'<a href="{slug}.pdf">PDF</a></p>')
        (folder / "index.html").write_text(document(title, body, tags), encoding="utf-8")
        listing.append(f'<li><a class="paper-title" href="papers/{slug}/">{html.escape(title)}</a>'
                       f'<div class="links"><time datetime="{paper["first_version_date"]}">{paper["first_version_date"]}</time>'
                       f'<a href="{doi_url}">DOI</a><a href="papers/{slug}/{slug}.pdf">PDF</a></div></li>')
        locations.append(page_url)
        if paper["pdf_size"] > MAX_PDF:
            warnings.append(f"PDF exceeds 5 MB: {slug} ({paper['pdf_size']} bytes)")
    (output / "index.html").write_text(document("Papers", '<h1>Papers</h1><ul class="papers">' + "\n".join(listing) + "</ul>"), encoding="utf-8")
    (output / "robots.txt").write_text("User-agent: *\nAllow: /\n", encoding="utf-8")
    sitemap = '<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
    sitemap += "".join("<url><loc>" + html.escape(url) + "</loc></url>\n" for url in locations) + "</urlset>\n"
    (output / "sitemap.xml").write_text(sitemap, encoding="utf-8")
    manifest.write_text(json.dumps(papers, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    largest = max(papers, key=lambda p: p["pdf_size"])
    local = sum(source is not None for source in sources.values())
    print(f"PDF sources: {local} local; {len(papers) - local} Zenodo downloads")
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
