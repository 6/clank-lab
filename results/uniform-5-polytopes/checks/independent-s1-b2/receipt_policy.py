"""Compare parsed scientific output fields under AGENTS.md.

Output receipts have no byte gate. Certificates, authoritative inputs and
checker dependencies retain their separate runtime identity checks.
"""
import copy
import json
import math
from pathlib import Path

TIMINGS = {
    "stage1-result.json": ("elapsed_seconds",),
    "stage1-verification.json": ("full_stage1_replay", "elapsed_seconds"),
    "comparison.json": ("elapsed_seconds",),
    "b2-comparison.json": ("elapsed_seconds",),
    "b2-full.json": ("elapsed_seconds",),
    "library.json": ("elapsed_seconds",),
    "cycles.json": (),
    "omega.json": (),
}


def read_receipt(path):
    return parse_receipt(Path(path).read_text())


def parse_receipt(raw):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate receipt key: " + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique,
                      parse_constant=lambda value: reject("nonfinite JSON: " + value))


def reject(message):
    raise ValueError(message)


def scientific_receipt(value, name):
    if name not in TIMINGS:
        raise ValueError("no S1 timing policy for " + name)
    result = copy.deepcopy(value)
    location = result
    try:
        for key in TIMINGS[name][:-1]:
            location = location[key]
        if not TIMINGS[name] or TIMINGS[name][-1] not in location:
            return result
        measured = location.pop(TIMINGS[name][-1])
    except (KeyError, TypeError, AttributeError) as exc:
        raise ValueError("missing S1 timing: " + name) from exc
    if type(measured) not in (int, float) or not math.isfinite(measured) or measured < 0:
        raise ValueError("invalid S1 timing: " + name)
    return result


def compare_receipt(actual, expected, name):
    # Compare canonical JSON too: Python equates True, 1 and 1.0 in dicts.
    def canonical(value):
        return json.dumps(scientific_receipt(value, name), sort_keys=True,
                          separators=(",", ":"), allow_nan=False)
    if canonical(actual) != canonical(expected):
        raise ValueError("S1 scientific receipt disagreement: " + name)
