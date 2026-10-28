#!/usr/bin/env python3
"""Exact bounded-replay endpoint guard; historical 138-native guard is separate.

The proposed native sets are independently enumerated from source roles,
never learned from the report being checked. A changed proof needs a new
reviewed freeze, not a broader allowance. This separate guard accepts ONLY
the exact 634 short-check roles and rejects the actual old 138-native report.
The actual author composition and restored typed probe passed this policy
with 54/638/634/692 native facts. Fresh independent RESULT acceptance and
the final freeze remain separate requirements; this parser proves no theorem.
"""
import json
import re
import sys
from pathlib import Path

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
SUFFIX = "._native.native_decide.ax_1_1"
PREFIX = "TightCycleC5.Bridge."
P32_NATIVE = {PREFIX + f"P32Arithmetic.class_group{i:02d}" + SUFFIX for i in range(53)} | {
    PREFIX + "P32RowMatching.multipliers_eq" + SUFFIX,
}
REPLAY_NATIVE = {
    PREFIX + f"P33Arithmetic.checkpoint_shard{i}" + SUFFIX
    for i in range(634)
}
P33_NATIVE = REPLAY_NATIVE | {
    PREFIX + name + SUFFIX for name in (
        "P33Arithmetic.sparse_inequalities_match", "P33Arithmetic.sparse_regularity_match",
        "P33PSD.seed14_gram", "P33PSD.seed23_gram",
    )
}
EXPECTED = {
    PREFIX + "P32ClassBridge.p32": STANDARD | P32_NATIVE,
    PREFIX + "p33_checked": STANDARD | P33_NATIVE,
    PREFIX + "P33Arithmetic.p33_arithmetic_replay": STANDARD | REPLAY_NATIVE,
    PREFIX + "mubayi_rodl_checked": STANDARD | P32_NATIVE | P33_NATIVE,
}
PATTERN = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)


def parse_reports(report):
    records = {}
    for match in PATTERN.finditer(report):
        name, body = match.groups()
        if name in records:
            raise ValueError(f"duplicate theorem report: {name}")
        items = [x.strip() for x in (body or "").split(",") if x.strip()]
        if len(items) != len(set(items)):
            raise ValueError(f"duplicate axiom: {name}")
        records[name] = set(items)
    return records


def check(report):
    records = parse_reports(report)
    if set(records) != set(EXPECTED):
        raise ValueError("theorem reports mismatch: " + str(sorted(set(records) ^ set(EXPECTED))))
    for name, expected in EXPECTED.items():
        # Standard axioms are permitted, not required. Native facts must
        # match exactly; report the actual standard subset for disclosure.
        if records[name] | STANDARD != expected:
            raise ValueError(f"{name}: missing={sorted(expected - records[name] - STANDARD)}; "
                             f"unexpected={sorted(records[name] - expected)}")
    return {
        "status": "PASS_ENDPOINT_GUARD",
        "result_acceptance": "requires the separate frozen full procedure",
        "native_counts": {name: len(actual - STANDARD) for name, actual in sorted(records.items())},
        "axioms": {name: sorted(actual) for name, actual in sorted(records.items())},
    }


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: guard_endpoint.py FINAL-PROBE-REPORT")
    try:
        result = check(Path(sys.argv[1]).read_text())
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    print(json.dumps(result, indent=2, sort_keys=True))
