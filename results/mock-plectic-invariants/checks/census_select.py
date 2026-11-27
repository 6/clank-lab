"""Regenerate the candidate list for the paper's 'Choice of inputs' (Sage 10.8)."""

import argparse
import csv
import hashlib
import io
import json
from math import gcd
from pathlib import Path
from typing import NamedTuple
from urllib.request import urlopen

from sage.all import ZZ, kronecker, set_random_seed

from arithmetic import admissible_ells, case
from run import flags


DATA = Path(__file__).resolve().parents[1] / "data"
ECDATA_COMMIT = "6fedd3ab463a70e52061ebc0b04832ad19fd2e01"
ECDATA_URL = (f"https://raw.githubusercontent.com/JohnCremona/ecdata/{ECDATA_COMMIT}/"
              "allcurves/allcurves.00000-09999")
ECDATA_SHA256 = "259f3846329395b371e8079c77a6f1097adaebc98a054974573e241416efa968"

ADDED = {("817a1", -7, 19): "proposed example",
         ("1664n1", -7, 13): "repeated tame prime",
         ("2117a1", -20, 73): "initial cyclotomic precision"}


class Candidate(NamedTuple):
    label: str
    D: int
    p: int
    N: int
    Nminus: int
    supported: int
    first_plus_ell_le271: int | None
    raw_flags: int | None
    cost_selected: int
    added_case: str

    @property
    def key(self):
        return self.label, self.D, self.p


def representatives(source):
    if hashlib.sha256(source).hexdigest() != ECDATA_SHA256:
        raise ValueError("Cremona allcurves file differs from the pinned SHA-256")
    for line in source.decode("ascii").splitlines():
        conductor, class_label, number, ainvs, rank, _ = line.split()
        N = int(conductor)
        if N < 5000 and number == "1" and rank == "2":
            yield N, f"{N}{class_label}1", json.loads(ainvs)


def candidates(source):
    fields = [D for D in range(-43, 0) if D not in (-3, -4)
              and ZZ(D).is_fundamental_discriminant()]
    for N, label, ainvs in representatives(source):
        set_random_seed(N)
        for prime, exponent in ZZ(N).factor():
            p = int(prime)
            if p < 5 or exponent != 1:
                continue
            for D in fields:
                if gcd(N, D) != 1 or kronecker(D, p) != -1:
                    continue
                audit = case(ainvs, D, p)
                if audit["N"] != N or audit["status"].startswith("unknown"):
                    raise ValueError(f"unresolved census input {label}, D={D}, p={p}")
                if not audit["eligible"]:
                    continue
                supported = audit["Nminus"] == 1
                # The iterator is increasing and its stop is exclusive.
                first = next(admissible_ells(ainvs, D, p, sign=1, stop=272), None)
                ell = first["ell"] if first else None
                raw = flags(N, ell) if supported and ell is not None else None
                selected = supported and p <= 19 and raw is not None and raw <= 4000
                yield Candidate(label, D, p, N, audit["Nminus"], int(supported), ell, raw,
                                int(selected), ADDED.get((label, D, p), ""))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, help="local copy of the pinned allcurves file")
    parser.add_argument("--output", type=Path, help="write the CSV (default: compare to archive)")
    args = parser.parse_args()
    if args.dataset:
        source = args.dataset.read_bytes()
    else:
        with urlopen(ECDATA_URL, timeout=60) as response:
            source = response.read()

    rows = list(candidates(source))
    keys = [row.key for row in rows]
    supported = sum(row.supported for row in rows)
    selected = {row.key for row in rows if row.cost_selected}
    counts = len(rows), supported, len(selected)
    if len(set(keys)) != len(rows) or counts != (816, 676, 15):
        raise ValueError(f"regenerated {counts}, expected (816, 676, 15) distinct triples")
    cohort = [json.loads(line) for line in (DATA / "cohort.jsonl").read_text().splitlines()]
    recorded = {(r["label"], r["D"], r["p"]) for r in cohort}
    added = {row.key for row in rows if row.supported and row.added_case}
    if (added != ADDED.keys() or selected & added or selected | added != recorded
            or len(cohort) != 18):
        raise ValueError("cost-selected triples and the three added cases differ from the cohort")

    output = io.StringIO()
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(Candidate._fields)
    writer.writerows(rows)
    csv_bytes = output.getvalue().encode("ascii")
    if args.output:
        args.output.write_bytes(csv_bytes)
    elif csv_bytes != (DATA / "candidates.csv").read_bytes():
        raise ValueError("regenerated candidate list differs from data/candidates.csv")
    print(f"{len(rows)} eligible, {supported} supported, {len(selected)} cost-selected, "
          f"{len(added)} explicitly added")


if __name__ == "__main__":
    main()
