"""Reconstruct the two source inputs locally and check both published count files."""
import argparse
import csv
import hashlib
import html
import re
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

SOURCES = (
    ("table.html", "988aabfc10eb5b31347662df46060fad96ede12ef23932e5b418e91cc445ef16",
     "https://web.archive.org/web/20181105195239id_/http://www.grg.org/Adams/A_files/sheet001.htm"),
    ("nchs.pdf", "353128e491cecbec7ed25777a02a0e99cae6052cd4b1104d74af47028c184b5a",
     "https://ftp.cdc.gov/pub/health_Statistics/nchs/publications/DVD/DVD_3/Misc/usvss.pdf"),
    ("s1.R", "ef4bb49ec662efd6c465d76dfdb8ea62acadce2b9fb5faab5c996a84dca2c6ea",
     "https://www.biorxiv.org/content/biorxiv/early/2025/11/03/704080/DC4/embed/media-4.txt?download=true"),
)


def fetch(work):
    for name, digest, url in SOURCES:
        path = work / name
        if not path.exists():
            tmp = path.with_suffix(".download")
            subprocess.run(["curl", "--fail", "--location", "--silent", "--show-error",
                            "--retry", "3", "--max-time", "120", url, "-o", tmp], check=True)
            tmp.replace(path)
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"source checksum mismatch for {name}")


def records(work):
    source = (work / "table.html").read_text(encoding="latin1")
    header = None
    rows = []
    for row in re.findall(r"<tr\b[^>]*>(.*?)</tr>", source, re.I | re.S):
        cells = [" ".join(html.unescape(re.sub("<[^>]+>", "", cell)).split())
                 for cell in re.findall(r"<td\b[^>]*>(.*?)</td>", row, re.I | re.S)]
        if cells and cells[0] == "Number":
            header = cells
        if cells and cells[0].isdigit():
            if not header or len(cells) != len(header) or int(cells[0]) != len(rows) + 1:
                raise ValueError("Table A record sequence or width changed")
            rows.append(cells)
    if len(rows) != 1739 or header[10:12] != ["Birthplace", "Residence/Place of death"]:
        raise ValueError("Table A roster or birthplace header changed")
    with (work / "GRG_validated_records_2_JUN_2019.csv").open("w", newline="") as out:
        csv.writer(out).writerows([header, *rows])


def registrations(work):
    layout = subprocess.check_output(["pdftotext", "-layout", work / "nchs.pdf", "-"]).decode()
    page, = (p for p in layout.split("\f")
             if re.search(r"Table 1\.01\. Important Dates", p) and "Virgin Islands" in p)
    rows = re.findall(r"^([A-Z][A-Za-z ]+?)\s*(?:\. *)+\s+(\d{4})\s+(\d{4})\s+\d{4}\s+\d{4}", page, re.M)
    if len(rows) != 53 or len({name.strip() for name, _, _ in rows}) != 53:
        raise ValueError("Table 1.01 area count changed")
    with (work / "Hist_and_Org_vital_Stats_Appendix_II_page_58.csv").open("w", newline="") as out:
        writer = csv.writer(out)
        writer.writerow(["State", "Births.all.areas"])
        writer.writerows((name.strip(), births) for name, _, births in rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, help="directory with pinned table.html, nchs.pdf and s1.R")
    parser.add_argument("--bounds", action="store_true", help="also check sharp bounds (requires NetworkX)")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    with TemporaryDirectory() as tmp:
        work = Path(tmp)
        if args.inputs:
            for name, _, _ in SOURCES:
                (work / name).symlink_to((args.inputs / name).resolve(strict=True))
        fetch(work)
        records(work)
        registrations(work)
        command = ["Rscript", "--vanilla", here / "shuffle.R", here.parent / "data"]
        if args.bounds:
            command.append("--bounds")
        subprocess.run(command, cwd=work, check=True)
        if args.bounds:
            from bounds import check
            check(work)


if __name__ == "__main__":
    main()
