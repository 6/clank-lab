"""Parsed output acceptance under AGENTS.md; input/certificate pins are separate."""
import copy
import gzip
import json
import math
from pathlib import Path

# These paths contain observations or identity-gate metadata, not mathematics.
TIMINGS = {"results.json": [("elapsed_seconds",),
            *(("bounds", p, "elapsed_seconds") for p in ("6", "10", "16"))]}
METADATA = {
    "results.json": ("source_sha256",),
    "fresh-filter-audit-output.json": ("frozen_manifest_sha256", "identity_checks",
                                      "checked_files", "all_hashes_match",
                                      "sources_manifest_equals_frozen_inputs"),
}


def read(path):
    path = Path(path)
    raw = gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes()
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate output key: " + key)
            result[key] = value
        return result
    def nonfinite(value):
        raise ValueError("nonfinite JSON: " + value)
    return json.loads(raw, object_pairs_hook=unique, parse_constant=nonfinite)


def scientific(value, name):
    result = copy.deepcopy(value)
    paths = TIMINGS.get(name, [("elapsed_seconds",)])
    for path in paths:
        parent = result
        for key in path[:-1]:
            parent = parent[key]
        if path[-1] in parent:
            measured = parent.pop(path[-1])
            if type(measured) not in (int, float) or not math.isfinite(measured) or measured < 0:
                raise ValueError("invalid observed output timing: " + name)
    for field in METADATA.get(name, ()):
        result.pop(field, None)
    # Canonicalization is internal: it compares parsed values/types, never file
    # bytes. Array order and every remaining scientific field remain exact.
    return json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False)


def compare(actual, expected, name):
    if scientific(actual, name) != scientific(expected, name):
        raise ValueError("scientific output disagreement: " + name)
