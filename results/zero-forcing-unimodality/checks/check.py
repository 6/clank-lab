#!/usr/bin/env python3
"""Check the certificate, coverage, solved controls and deliberate corruptions."""
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent


def run(script, arguments, status, reason=None):
    result = subprocess.run(
        [sys.executable, "-I", str(ROOT / "checks" / script), *map(str, arguments)],
        capture_output=True, text=True, check=False)
    try:
        report = json.loads(result.stdout)
    except (ValueError, TypeError) as error:
        raise RuntimeError(f"{script}: invalid report: {result.stderr}") from error
    expected_exit = 1 if status in ("reject", "rejected") else 0
    if (result.returncode != expected_exit or report.get("status") != status
            or (reason is not None and report.get("reason") != reason)):
        raise RuntimeError(f"{script}: unexpected outcome: {report}; {result.stderr}")
    return report


def main():
    cert = ROOT / "data" / "certificate.json"
    for checker, status in (("a", "ok"), ("b", "accepted"), ("c", "accepted")):
        run(f"checker_{checker}.py", [cert], status)
        print(f"Checker {checker.upper()}: accepted")
    for case in ("K6", "P4", "C4"):
        run("controls.py", [case], "ok", "CONTROL_OK")
    print("Solved controls: K6, P4 and C4 accepted")
    mutations = ROOT / "data" / "corruptions"
    for name, reason_a, reason_b, flags in (
        ("coefficient", "COEFFICIENTS", "B_COEFFICIENT_MISMATCH", []),
        ("inside-edge", "CLIQUE", "B_PAIR_NOT_FORT", []),
        ("left-join", "PATTERN_FORCING", "B_FORCING_MISMATCH", ["--generic-audit"]),
    ):
        args = [mutations / f"{name}.json", *flags]
        run("checker_a.py", args, "reject", reason_a)
        run("checker_b.py", args, "rejected", reason_b)
    run("checker_c.py", [mutations / "cover-gap.json"], "rejected", "C_COVER_GAP")
    print("All seven prescribed corruption rejections passed")
    print("PASS: the 73-vertex graph has coefficients 2096, 1592, 1600, 73, 1")


if __name__ == "__main__":
    main()
