#!/usr/bin/env python3
"""Reconstruct and check the exact polynomial transformation certificate."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "data"
# Approximate relative costs assign independent steps to CI parts. Dependencies
# are repeated where necessary; omitting --part runs every obligation once.
STEPS = [
    ("group", "exact reflection group and subgroup model", 1),
    ("inputs", "exhaustive symbolic input identities and corruptions", 3),
    ("primary", "C++/FLINT membership, input reductions and all pairs", 80),
    ("second", "independent Singular arithmetic and complete pair audit", 230),
    ("cover", "two complete monomial covers and cover corruptions", 5),
    ("chain", "all quotient functions by chain intervals", 3),
    ("dfs", "all quotient functions by standard monomial DFS", 3),
    ("coefficient", "both arithmetic implementations reject a basis corruption", 80),
    ("mutations", "input, transformation, order, cover and rank corruptions", 350),
]


def select(part):
    if part is None:
        return STEPS
    k, n = part
    bins = [[] for _ in range(n)]
    costs = [0] * n
    for step in sorted(STEPS, key=lambda step: -step[2]):
        at = min(range(n), key=lambda i: (costs[i], i))
        bins[at].append(step)
        costs[at] += step[2]
    names = {step[0] for step in bins[k - 1]}
    return [step for step in STEPS if step[0] in names]


def parse_part(text):
    try:
        k, n = map(int, text.split("/"))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("use K/N, with 1 <= K <= N <= 8") from exc
    if not 1 <= k <= n <= 8:
        raise argparse.ArgumentTypeError("require 1 <= K <= N <= 8")
    return k, n


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--workers", type=int, default=1,
                    help="number of allocated CPU cores (default: 1)")
    ap.add_argument("--part", type=parse_part, help="run one of up to eight CI parts")
    ap.add_argument("--list", action="store_true", help="list selected checks and exit")
    ap.add_argument("--work", type=Path, help="retain files in this new directory")
    ap.add_argument("--certificate-from", type=Path,
                    help="existing certificate directory; skip reconstruction")
    args = ap.parse_args()
    if args.workers < 1:
        ap.error("--workers must be positive")
    chosen = select(args.part)
    if args.list:
        for name, description, _ in chosen:
            print(f"{name}: {description}")
        return
    if not __debug__:
        raise SystemExit("Run Python without -O: certificate assertions must be enabled.")
    for tool in ("g++", "Singular"):
        if not shutil.which(tool):
            raise SystemExit(f"Missing {tool}; see checks/README.md.")
    if not Path("/usr/bin/time").is_file():
        raise SystemExit("GNU time is required at /usr/bin/time.")
    import sympy  # Check the declared Python dependency before reconstruction.
    if args.work is None:
        with tempfile.TemporaryDirectory(prefix="slp-certificate-") as work:
            verify(Path(work), args.workers, chosen, args.certificate_from)
    else:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=False)
        verify(work, args.workers, chosen, args.certificate_from)


def verify(work, workers, chosen, certificate_from):
    unit = work / "certificate"
    unit.mkdir()
    for name in ("unit-order.txt", "unit-initial.txt", "unit-starts.txt"):
        shutil.copyfile(DATA / name, unit / name)
    env = os.environ.copy()
    env["CFG_INPUT_DIR"] = str(DATA / "inputs")
    env["CFG_CHECK_BIN"] = str(work / "check")
    env["OMP_NUM_THREADS"] = str(workers)
    env.pop("PYTHONOPTIMIZE", None)
    python = sys.executable
    done = set()

    def run(label, command, cwd=HERE):
        log = work / (label + ".log")
        with log.open("w") as output:
            result = subprocess.run([str(x) for x in command], cwd=cwd,
                                    env=env, stdout=output, stderr=subprocess.STDOUT)
        if result.returncode:
            print(log.read_text()[-12000:], file=sys.stderr)
            raise RuntimeError(f"{label} failed (exit {result.returncode}).")

    if certificate_from is None:
        print("Reconstructing the polynomial transformation certificate...", flush=True)
        producer = work / "producer"
        run("generate-script", [python, HERE / "generate.py", producer])
        run("produce-certificate", ["Singular", "-q", "run.sing"],
            cwd=producer / "target")
        output = (work / "produce-certificate.log").read_text()
        assert "DONE_EXPORT" in output and "?" not in output, "certificate production failed"
        transformations = producer / "target/certificate.txt"
    else:
        transformations = certificate_from.resolve() / "certificate.txt"
    # The polynomial and monomial data supplied with the package remain the
    # acceptance target. Only T is reconstructed; no producer result is trusted.
    with (unit / "certificate.txt").open("wb") as out:
        with gzip.open(DATA / "polynomials.txt.gz", "rb") as prefix:
            shutil.copyfileobj(prefix, out)
        started = False
        with transformations.open("rb") as source:
            for line in source:
                if not started and line.startswith(b"T "):
                    started = True
                if started:
                    assert line.startswith(b"T "), "invalid transformation record"
                    out.write(line)
        assert started, "missing transformation certificate"

    def native():
        if "compile" not in done:
            run("compile", ["g++", "-std=c++17", "-O3", "-fopenmp",
                            HERE / "check.cpp", "-lflint", "-lgmp", "-o",
                            work / "check"])
            done.add("compile")

    def primary():
        native()
        if "primary" not in done:
            run("primary", [work / "check", unit / "certificate.txt", workers,
                            unit / "check"])
            receipt = json.loads((unit / "check.json").read_text())
            assert receipt["accepted"] and receipt["unresolved"] == 0
            assert receipt["basis_size"] == receipt["membership_columns"] == 534
            assert receipt["frozen_inputs_bound"] == 6
            assert receipt["T_terms"] == 27280320
            assert (receipt["pairs_total"], receipt["pairs_product"],
                    receipt["pairs_chain"], receipt["pairs_direct"]) == (
                        142311, 1690, 138012, 2609)
            done.add("primary")

    def chains():
        if "chain" not in done:
            run("chain", [python, HERE / "rank_chain.py", unit,
                          unit / "rank-table.json", "--write"])
            done.add("chain")

    for name, description, _ in chosen:
        started = time.monotonic()
        print(f"Checking {description}...", flush=True)
        if name == "group":
            run(name, [python, HERE / "check_groups.py", "--out", work / "group.json"])
        elif name == "inputs":
            run(name, [python, HERE / "check_symbolic_inputs.py", DATA / "inputs",
                       "--out", work / "symbolic-inputs.json"])
        elif name == "primary":
            primary()
        elif name == "second":
            primary()
            run(name, [python, HERE / "check_second.py", unit / "certificate.txt",
                       unit / "check.pairs", unit / "second", workers])
        elif name == "cover":
            run(name, [python, HERE / "check_quotients.py", unit, "target"])
        elif name == "chain":
            chains()
        elif name == "dfs":
            chains()
            run(name, [python, HERE / "rank_dfs.py", unit, unit / "rank-table.json"])
        elif name == "coefficient":
            native()
            run(name, [python, HERE / "corrupt.py", unit, workers])
        elif name == "mutations":
            native()
            chains()
            run(name, [python, HERE / "audit_mutations.py", unit, workers])
        else:
            raise AssertionError(name)
        print(f"PASS {name} ({time.monotonic() - started:.1f} seconds)", flush=True)
    print("All selected certificate checks passed.", flush=True)


if __name__ == "__main__":
    main()
