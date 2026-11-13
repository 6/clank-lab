#!/usr/bin/env python3
"""Check a generated paper site against its manifest (Python 3.9+)."""

import argparse
from collections import defaultdict
from datetime import date
import hashlib
import html
from html.parser import HTMLParser
import ipaddress
import json
from pathlib import Path
import re
import shutil
import subprocess
import unicodedata
from urllib.parse import unquote, urlsplit
import xml.etree.ElementTree as ET

MAX_PDF = 5_000_000
BASE_URL = "https://6.github.io/clank-lab/"
FORBIDDEN = {
    "run identifier": r"\b(?=[0-9a-f]{12}\b)(?=[0-9a-f]*[a-f])[0-9a-f]{12}\b|\b[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}\b|\brun[_ -]?id\s*[:=]\s*\S+",
    "private path": r"(?:/(?:home|Users|root|tmp|private|var|mnt|opt|workspace|workspaces)/|[a-z]:[\\/](?:Users|Windows)[\\/]|file://|~/)",
    "private hostname": r"\b(?:localhost|[\w-]+(?:\.[\w-]+)*\.(?:internal|local|lan|private|intranet))\b",
    "email address": r"[\w.!#$%&'*+/=?^`{|}~-]+@[\w-]+(?:\.[\w-]+)+",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Page(HTMLParser):
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.in_head = False
        self.in_body = False
        self.headings = []
        self.in_heading = False
        self.meta = defaultdict(list)
        self.links = []
        self.dates = []
        self.body = []
        self.text = []
        self.attributes = []
        self.styles = 0
        self.unsafe = False
        self.feed(source)
        self.close()

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        self.attributes.extend(value for _, value in attrs if value)
        if tag == "head":
            self.in_head = True
        if tag == "body":
            self.in_body = True
        if tag == "h1":
            self.in_heading = True
            self.headings.append("")
        if tag == "meta" and self.in_head:
            self.meta[attributes.get("name", "")].append(attributes.get("content", ""))
        if tag == "a" and self.in_body:
            self.links.append(attributes.get("href", ""))
        if tag == "time":
            self.dates.append(attributes.get("datetime", ""))
        self.styles += tag == "style"
        if (tag in {"script", "iframe", "object", "embed", "img", "link", "form", "video", "audio", "source"}
                or any(name.startswith("on") or name in {"src", "srcset"} for name in attributes)):
            self.unsafe = True

    def handle_endtag(self, tag):
        if tag == "head":
            self.in_head = False
        if tag == "body":
            self.in_body = False
        if tag == "h1":
            self.in_heading = False

    def handle_data(self, text):
        self.text.append(text)
        if self.in_body:
            self.body.append(text)
        if self.in_heading:
            self.headings[-1] += text


def normal(text):
    # Ignore layout, accents, TeX punctuation, and PDF ligatures; keep every letter/digit.
    text = unicodedata.normalize("NFKD", text).casefold()
    return "".join(char for char in text if char.isalnum())


def read_deny(path):
    # One regex per line; blank lines and lines starting with # are ignored.
    patterns = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if line.strip() and not line.lstrip().startswith("#"):
            patterns.append((f"{path.name} line {number}", re.compile(line.strip(), re.IGNORECASE)))
    require(bool(patterns), "Deny file has no patterns")
    return patterns


def scan(text, label, deny=()):
    decoded = unquote(html.unescape(text))
    for kind, pattern in FORBIDDEN.items():
        require(not re.search(pattern, decoded, re.IGNORECASE), f"Privacy scan: {kind} in {label}")
    for kind, pattern in deny:
        require(not pattern.search(decoded), f"Privacy scan: {kind} in {label}")
    for value in re.findall(r"(?<![\d.])(?:\d{1,3}\.){3}\d{1,3}(?![\d.])", decoded):
        try:
            address = ipaddress.ip_address(value)
        except ValueError:
            continue
        require(address.is_global, f"Privacy scan: private IP address in {label}")
    for value in re.findall(r"\[([0-9a-f:]+)\]", decoded, re.IGNORECASE):
        try:
            address = ipaddress.ip_address(value)
        except ValueError:
            continue
        require(address.is_global, f"Privacy scan: private IP address in {label}")


def pdf_text(tool, path, first_page=False):
    args = [tool, "-enc", "UTF-8"]
    if first_page:
        args += ["-f", "1", "-l", "1"]
    result = subprocess.run(args + [str(path), "-"], capture_output=True, timeout=60)
    require(result.returncode == 0, "pdftotext failed for " + path.name)
    return result.stdout.decode("utf-8")


def check(output, base_url, manifest, screenshots=None, deny=()):
    base_url = base_url.rstrip("/") + "/"
    base = urlsplit(base_url)
    require(base.scheme in {"http", "https"} and base.hostname and not base.query
            and not base.fragment and not base.username and not base.password,
            "Invalid --base-url")
    papers = json.loads(manifest.read_text(encoding="utf-8"))
    require(bool(papers), "Manifest has no papers")
    slugs = [paper["slug"] for paper in papers]
    require(len(set(slugs)) == len(slugs), "Duplicate manifest slug")
    require(len({p["concept_doi"] for p in papers}) == len(papers), "Duplicate concept DOI")
    expected_pages = {"index.html"} | {f"papers/{slug}/index.html" for slug in slugs}
    expected_pdfs = {f"papers/{slug}/{slug}.pdf" for slug in slugs}
    expected_files = expected_pages | expected_pdfs | {"robots.txt", "sitemap.xml"}
    actual_files = {p.relative_to(output).as_posix() for p in output.rglob("*") if p.is_file()}
    require(actual_files == expected_files, "Generated file inventory differs from manifest")
    tool = shutil.which("pdftotext")
    warnings = [] if tool else ["pdftotext unavailable: PDF title and extracted full-text privacy checks skipped"]
    pages = {}
    for path in sorted(output.rglob("*")):
        label = path.relative_to(output).as_posix()
        require(not path.is_symlink(), "Unexpected symlink in output")
        scan(label, "output filename", deny)
        if not path.is_file() or path.suffix == ".pdf":
            continue
        source = path.read_text(encoding="utf-8")
        scan(source, label, deny)
        if path.suffix == ".html":
            page = Page(source)
            scan(" ".join(page.text + page.attributes), label, deny)
            require(not page.unsafe and page.styles == 1, "Unexpected assets, script, or stylesheet in " + label)
            require(page.meta["viewport"] == ["width=device-width,initial-scale=1"], "Missing mobile viewport in " + label)
            require(not re.search(r"@import|url\s*\(", source, re.IGNORECASE), "External stylesheet asset in " + label)
            pages[label] = page
    index = pages["index.html"]
    ordered = sorted(papers, key=lambda p: (p["first_version_date"], p["slug"]), reverse=True)
    links = [link for p in ordered for link in (f"papers/{p['slug']}/", "https://doi.org/" + p["concept_doi"],
                                                f"papers/{p['slug']}/{p['slug']}.pdf")]
    require(index.links == links, "Index title, DOI, or PDF links missing or not newest first")
    require(index.dates == [p["first_version_date"] for p in ordered], "Incorrect index dates")
    largest = (0, "")
    for paper in papers:
        slug, title = paper["slug"], paper["title"]
        label = f"papers/{slug}/index.html"
        require(re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", slug), "Invalid result folder slug")
        doi_match = re.fullmatch(r"10\.5281/zenodo\.(\d+)", paper["concept_doi"])
        require(doi_match, "Invalid Zenodo concept DOI")
        day = date.fromisoformat(paper["first_version_date"]).isoformat()
        page_url = base_url + f"papers/{slug}/"
        pdf_url = page_url + slug + ".pdf"
        page = pages[label]
        wanted = {"citation_title": [title], "citation_author": paper["authors"],
                  "citation_publication_date": [day.replace("-", "/")],
                  "citation_pdf_url": [pdf_url], "citation_doi": [paper["concept_doi"]],
                  "citation_publisher": ["Zenodo"]}
        require(bool(paper["authors"]), "No authors for " + label)
        for name, values in wanted.items():
            require(page.meta[name] == values, f"Incorrect {name} in {label}")
        require(page.headings == [title], "Incorrect visible title in " + label)
        require(page.dates == [day], "Incorrect visible date in " + label)
        visible = normal(" ".join(page.body))
        require(all(normal(author) in visible for author in paper["authors"]), "Missing visible author in " + label)
        abstract = normal(" ".join(Page(paper["abstract"]).text))
        require(bool(abstract) and abstract in visible, "Incomplete abstract in " + label)
        doi_url = "https://doi.org/" + paper["concept_doi"]
        require(page.links == ["../../", doi_url, slug + ".pdf"],
                "Paper index navigation and PDF links must be relative in " + label)
        require(doi_url in page.links and paper["concept_doi"] in " ".join(page.body), "Missing visible DOI in " + label)
        require(slug + ".pdf" in page.links, "Missing visible PDF link in " + label)
        parsed = urlsplit(page.meta["citation_pdf_url"][0])
        require(parsed.scheme == base.scheme and parsed.netloc == base.netloc
                and parsed.path.rsplit("/", 1)[0] == urlsplit(page_url).path.rstrip("/")
                and not parsed.query and not parsed.fragment, "PDF URL must be absolute and in the page directory")
        relative = unquote(parsed.path[len(base.path):])
        pdf = output / relative
        require(pdf.resolve() == (output / "papers" / slug / (slug + ".pdf")).resolve()
                and pdf.is_file(), "PDF URL does not resolve to the adjacent PDF")
        size = pdf.stat().st_size
        require(size <= MAX_PDF, f"PDF exceeds 5 MB: {slug} ({size} bytes)")
        require(size == paper["pdf_size"], "PDF size differs from manifest: " + slug)
        data = pdf.read_bytes()
        require(data.startswith(b"%PDF-"), "Not a PDF: " + slug)
        require(hashlib.md5(data).hexdigest() == paper["pdf_md5"], "PDF MD5 differs from manifest: " + slug)
        if tool:
            first = pdf_text(tool, pdf, first_page=True)
            require(normal(title) in normal(first), "Title absent from PDF page 1: " + slug)
            scan(pdf_text(tool, pdf), "PDF text: " + slug, deny)
        largest = max(largest, (size, slug))
    expected_urls = {base_url} | {base_url + f"papers/{slug}/" for slug in slugs}
    tree = ET.parse(output / "sitemap.xml")
    urls = [node.text for node in tree.findall("{*}url/{*}loc")]
    require(len(urls) == len(expected_urls) and set(urls) == expected_urls, "Sitemap differs from paper inventory")
    robots = (output / "robots.txt").read_text(encoding="utf-8")
    require(robots == "User-agent: *\nAllow: /\n", "robots.txt must allow all crawling without a host URL")
    if screenshots is not None:
        require(output.resolve() != screenshots.resolve() and output.resolve() not in screenshots.resolve().parents,
                "Save screenshots outside the generated site")
        node = shutil.which("node")
        if node is None:
            warnings.append("Node unavailable: mobile render skipped")
        else:
            script = Path(__file__).resolve().with_name("mobile-check.cjs")
            slug = max(papers, key=lambda paper: len(paper["title"]))["slug"]
            result = subprocess.run([node, str(script), str(output.resolve()), slug, str(screenshots.resolve())],
                                    capture_output=True, text=True, timeout=60)
            if result.returncode == 77:
                warnings.append(result.stdout.strip())
            else:
                require(result.returncode == 0, "Mobile render failed: " + result.stderr.strip())
                print(result.stdout.strip())
    print(f"PASS: {len(papers)} papers; largest PDF: {largest[0]:,} bytes ({largest[1]}); warnings: {len(warnings)}")
    for warning in warnings:
        print("WARNING: " + warning)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--base-url", default=BASE_URL)
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("papers.json"))
    parser.add_argument("--deny-file", type=Path, help="Optional extra privacy patterns, one regex per line, kept outside the public copy")
    parser.add_argument("--screenshots", type=Path, help="Optional 375px Chromium check; save screenshots outside the site (Node and Playwright required)")
    args = parser.parse_args()
    try:
        deny = read_deny(args.deny_file) if args.deny_file else ()
        check(args.output, args.base_url, args.manifest, args.screenshots, deny)
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired, ET.ParseError) as error:
        parser.exit(1, f"Check failed: {error}\n")


if __name__ == "__main__":
    main()
