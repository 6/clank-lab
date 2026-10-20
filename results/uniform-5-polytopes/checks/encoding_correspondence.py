"""Explain primary/independent enumeration counts; the relaxed run is diagnostic.

Normal primary searches must pass first. A separate in-memory experiment
bypasses only the cell-patch mismatch rejection, exposing the mirror stars
that the independent route rejects by full-star separation. Its states
are never accepted as realizations. No numerical source is modified.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
PRIMARY = HERE / "primary"
FAMILIES = {
    "snic": [164, 201, 249, 311, 393, 496, 607, 750, 898, 1076, 1278, 1502, 1747, 1979],
    "snid": [906, 966, 1027, 1120, 1215, 1335, 1478, 1637, 1810, 1982, 2153, 2329, 2502, 2661],
}


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def read(path):
    raw = Path(path).read_bytes()
    if str(path).endswith(".gz"):
        raw = gzip.decompress(raw)
    return json.loads(raw)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--primary-report", type=Path,
                    default=HERE.parent / "data/primary-u3-p16.json.gz")
    ap.add_argument("--signatures", type=Path,
                    default=HERE.parent / "data/primary-u2-signatures-p16.json.gz")
    ap.add_argument("--independent", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    os.environ["U5_EXACT_INPUT_ROOT"] = str(PRIMARY)
    sys.path.insert(0, str(PRIMARY / "check_u3"))
    import search
    import canon
    from ivla import I, dist2

    report = read(args.primary_report)
    inputs = {c["index"]: c for c in read(args.signatures)}
    classes = {c["index"]: c for c in report["classes"]}
    require(report["summary"]["search_states"] == 633
            and report["summary"]["realisations"] == 629, "primary inventory")
    duplicates = [(c["index"], vi, r["search_states"])
                  for c in report["classes"] for vi, v in enumerate(c["vfs"])
                  for r in v["realisations"] if r["search_states"] != 1]
    require(duplicates == [(18, 0, 4), (2082, 0, 2)], "duplicate-state accounting")

    def code(s):
        return hashlib.sha256(repr(canon.canonical(s)).encode()).hexdigest()

    def separation(s, family):
        # Inspect actual vertices in the common snub-cell patches. One
        # strict 0<distance^2<1 pair suffices; no witness proves nothing.
        facets = [f for f in s.facets if f.type == "pr-" + family]
        require(len(facets) == 2, "two snub-prism facets required")
        patches = []
        for f in facets:
            cells = [c for c in f.T.cells if c["label"] == family]
            require(len(cells) == 1, "one incident snub cell required")
            patches.append([(t, f.apply(f.T.V[t])) for t in cells[0]["patch"]])
        for i, a in patches[0]:
            for j, b in patches[1]:
                d = dist2(a, b)
                if d.a > 0 and d.b < 1:
                    return {"model_vertices": [i, j], "squared_distance": str(d)}
        return None

    original = search.cell_patch_check
    cuts = []

    def recorded(*a):
        try:
            return original(*a)
        except search.Contradiction as error:
            if str(error) == "cell patch mismatch":
                f, ci, g, cj = a
                cuts.append([f.type, g.type, f.T.cells[ci]["label"], g.T.cells[cj]["label"]])
            raise

    def relaxed(*a):
        try:
            return original(*a)
        except search.Contradiction as error:
            if str(error) != "cell patch mismatch":
                raise

    start = time.monotonic()
    rows = []
    try:
        for family, ids in FAMILIES.items():
            for m, ci in enumerate(ids, 3):
                c = classes[ci]
                require(len(c["vfs"]) == len(inputs[ci]["vfs"]) == 1, "signature inventory")
                names = c["vfs"][0]["realisations"][0]["known_names"]
                require("{" + str(m) + "}x" + family in names, "product-family binding")
                r = I(c["R"])
                sig = search.Signature(inputs[ci]["vfs"][0])
                cuts.clear()
                search.cell_patch_check = recorded
                normal, stats = search.realise(r * r, sig)
                require(not stats["undecided"] and len(normal) == 1, "normal search")
                require(cuts == [["pr-" + family] * 2 + [family] * 2], "normal patch rejection")
                normal_code = code(normal[0][0])
                require(separation(normal[0][0], family) is None, "normal star obstruction")
                search.cell_patch_check = relaxed
                extra, diagnostic_stats = search.realise(r * r, sig)
                by_code = {code(s): s for s, _ in extra}
                require(not diagnostic_stats["undecided"] and len(extra) == len(by_code) == 2
                        and normal_code in by_code, "relaxed diagnostic inventory")
                del by_code[normal_code]
                extra_code, star = next(iter(by_code.items()))
                witness = separation(star, family)
                require(witness is not None, "extra orientation lacks strict separation")
                rows.append({"class": ci, "family": family, "polygon": m,
                             "normal_code_sha256": normal_code,
                             "diagnostic_extra_code_sha256": extra_code,
                             "normal_search": dict(stats),
                             "diagnostic_search": dict(diagnostic_stats),
                             "diagnostic_separation_witness": witness})
    finally:
        search.cell_patch_check = original

    independent = None
    if args.independent:
        independent = [json.loads(line) for line in args.independent.read_text().splitlines()]
        all_rows = [r for c in independent for r in c["realisations"]]
        mirrors = [(c["index"], r) for c in independent for r in c["realisations"]
                   if "separation_witness" in r]
        require(len(all_rows) == 657 and len(mirrors) == 28, "independent inventory")
        require({ci for ci, _ in mirrors} == {r["class"] for r in rows}, "mirror class map")
        for ci, r in mirrors:
            require(r["status"] == "REFUTED"
                    and r["signature"] == inputs[ci]["vfs"][0], "mirror full-signature map")

    result = {
        "status": "PASS", "scope": "Enumeration accounting and rejection diagnostic, not a proof from relaxed search.",
        "primary_completed_states": 633, "primary_canonical_encodings": 629,
        "duplicate_completed_states": duplicates,
        "normal_search_encodings": 28, "diagnostic_encodings": 56,
        "diagnostic_extra_encodings_with_strict_separation": 28,
        "independent_full_signature_map": "PASS" if independent is not None else "not requested",
        "wall_seconds": round(time.monotonic() - start, 3), "rows": rows,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("PASS primary accounting: 633 completions -> 629 encodings; duplicate excess 3+1")
    print("PASS 28 mirror classes: 28 normal encodings; diagnostic 56, extra 28 strictly separation-refuted")
    if independent is not None:
        print("PASS independent 657-group inventory: all 28 mirror classes and full signatures agree")
    print("DIAGNOSTIC only: bypassed cell-patch states are never accepted; %.3fs" % result["wall_seconds"])


if __name__ == "__main__":
    main()
