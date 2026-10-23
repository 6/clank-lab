#!/usr/bin/env python3
"""Run all exact Python proof checks; no third-party packages are required."""

import ast
import contextlib
import io
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True

import attainment
import check_cert

ROOT = Path(__file__).resolve().parents[1]


def certificate_check(path):
    """Use the independent checker unchanged, retaining its explicit rejection."""
    previous = sys.argv
    sys.argv = ["check_cert.py", str(path)]
    output = io.StringIO()
    try:
        with contextlib.redirect_stdout(output):
            try:
                check_cert.main()
            except SystemExit as error:
                return error.code, output.getvalue()
        return 0, output.getvalue()
    finally:
        sys.argv = previous


def check_transcription(path):
    """Compare certificate entries as mathematical data, ignoring source comments."""
    scale, cert = check_cert.read(path)
    assert scale == 15000
    transcribed = {}
    for n in range(128):
        source = (ROOT / "lean/CubelikeSC/Cert/Data" / ("N%03d.lean" % n)).read_text()
        definitions = re.findall(r"^def (e\d+_\d+) : Entry := (.+)$", source, re.MULTILINE)
        names = []
        for name, expression in definitions:
            nn, m, pairs, weights = ast.literal_eval(expression)
            assert nn == n
            key = (nn, m, tuple(pairs))
            assert key not in transcribed, "duplicate transcribed key"
            assert len(weights) == len(dict(weights)), "duplicate transcribed weight"
            transcribed[key] = dict(weights) if weights else "EMPTY"
            names.append(name)
        collector = re.search(r"^def entries\d+ : List Entry := \[(.*)\]$", source, re.MULTILINE)
        assert collector is not None
        assert collector.group(1).split(", ") == names
    assert transcribed == cert, "Lean entries differ from certificate data"
    print("PASS: certificate and Lean transcription agree (3,984 entries)")


def corruptions(path):
    lines = path.read_text().splitlines(keepends=True)
    weighted = next(i for i, line in enumerate(lines) if line.startswith("K ") and "EMPTY" not in line)
    first = next(line for line in lines if line.startswith("K "))
    variants = {}
    variants["deleted entry"] = lines[:weighted] + lines[weighted + 1:]
    changed = lines.copy()
    changed[weighted] = changed[weighted].split(";")[0] + "; EMPTY\n"
    variants["false EMPTY"] = changed
    for name, zero in (("halved weights", False), ("zeroed weights", True)):
        changed = lines.copy()
        for i, line in enumerate(changed):
            if line.startswith("K 69 3 "):
                left, right = line.split(";")
                weights = [tuple(map(int, item.split(":"))) for item in right.split()]
                payload = "0:0" if zero else " ".join("%d:%d" % (v, w // 2) for v, w in weights)
                changed[i] = left + "; " + payload + "\n"
        variants[name] = changed
    changed = lines.copy()
    changed[weighted] = changed[weighted].replace(":", ":-", 1)
    variants["negative weight"] = changed
    variants["duplicated entry"] = lines + [first]
    with tempfile.TemporaryDirectory() as directory:
        for i, (name, changed) in enumerate(variants.items()):
            altered = Path(directory) / ("corrupt-%d.cert" % i)
            altered.write_text("".join(changed))
            code, _ = certificate_check(altered)
            assert code != 0, "corruption accepted: " + name
            print("PASS: rejected", name)


def main():
    path = ROOT / "data/d7k3.cert"
    check_transcription(path)
    code, output = certificate_check(path)
    print(output, end="", flush=True)
    assert code == 0, "certificate rejected"
    corruptions(path)
    # The cache is useful across all corruption checks, then can be released.
    check_cert.brackets.cache_clear()
    check_cert.coset_min.cache_clear()
    attainment.check()
    # The illustration is not a proof premise, but it must reproduce the graph.
    subprocess.run([sys.executable, "-B", str(ROOT / "checks/figure.py"), "--check"], check=True)
    print("PASS: all exact Python proof checks and illustration consistency")


if __name__ == "__main__":
    main()
