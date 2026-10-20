"""Reject semantic mutations of the P16 outcome and exact interval handoffs.

Requires an already replayed/audited full P16 S3 result. Does not rerun search.
"""
import argparse
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path

import check_filter as link
import count_convention as outcome


def reject(label, action, expected):
    try:
        with redirect_stdout(io.StringIO()):
            action()
    except ValueError as error:
        if expected not in str(error):
            raise AssertionError(f"{label}: unrelated rejection: {error}") from error
    else:
        raise AssertionError("accepted mutation: " + label)
    print("REJECTED:", label)


def interval_tests():
    base = Path(__file__).resolve().parent
    library = link.f.read_library(link.f.load_json(base / "independent-s1-b2/library.json")["records"])
    counts = {}
    for p in (6, 10, 16):
        actual = link.f.load_json(base / f"independent-merge-filter/results/classes_p{p}.json.gz")["classes"]
        consumer = link.f.load_json(base / f"independent-s23/inputs/u2_classes_p{p}.json.gz")
        counts[p] = link.consumer_intervals(actual, consumer, library)
        if p in (10, 16):
            primary = link.f.load_json(base / f"check_u1/classes_p{p}.json")
            if link.f.class_sets(primary, library) != link.f.class_sets(actual, library):
                raise AssertionError("primary class matching changed")
            for field in ("R", "R_alive"):
                link.strict_disjoint_intervals(primary, field, f"primary P{p}")
        narrowed = copy.deepcopy(consumer)
        narrowed[0]["R"][1] = narrowed[0]["R"][0]
        reject(f"P{p} narrowed consumer", lambda: link.consumer_intervals(actual, narrowed, library),
               "does not cover")
        # Widening preserves containment but violates class uniqueness.
        ordered = sorted(consumer, key=lambda row: link.f.interval(row["R"])[0])
        touching = copy.deepcopy(consumer)
        first = next(row for row in touching if row["index"] == ordered[0]["index"])
        first["R"][1] = ordered[1]["R"][0]
        reject(f"P{p} touching consumer classes",
               lambda: link.consumer_intervals(actual, touching, library), "overlapping or touching")
        overlapping = copy.deepcopy(actual)
        ordered_actual = sorted(overlapping, key=lambda row: link.f.interval(row["R_alive"])[0])
        ordered_actual[0]["R_alive"][1] = ordered_actual[1]["R_alive"][1]
        reject(f"P{p} overlapping S1 hulls",
               lambda: link.consumer_intervals(overlapping, consumer, library), "overlapping or touching")
    print("PASS exact P6/P10/P16 containment and disjointness:", json.dumps(counts, sort_keys=True))


def outcome_tests(results, known_path=None, classes_path=None):
    records = [outcome.parsed_json(line) for line in Path(results).read_text().splitlines() if line]
    known = outcome.authoritative_input(known_path, "u3_known")
    classes = outcome.authoritative_input(classes_path, "u2_classes")
    import models
    regenerated = models.known_names(16)
    outcome.count(records, known, classes, regenerated)

    def changed(class_index, change):
        rows = list(records)
        position = next(i for i, row in enumerate(rows) if row["index"] == class_index)
        rows[position] = copy.deepcopy(rows[position])
        change(rows[position])
        return lambda: outcome.count(rows, known, classes, regenerated)

    first = next(row for row in records if any(r["status"] == "KNOWN" for r in row["realisations"]))
    first_known = lambda row: next(r for r in row["realisations"] if r["status"] == "KNOWN")
    reject("omitted known name", changed(first["index"], lambda row: first_known(row)["names"].pop()),
           "KNOWN names disagree")

    def wrong_name(row):
        real = first_known(row)
        old = real["names"][0]
        real["names"][0] = "A5-not-a-construction"
        next(item for item in row["identification"]["known"] if item["name"] == old)["name"] = real["names"][0]
    reject("same counts, wrong known name", changed(first["index"], wrong_name),
           "every exact known name")

    mirror_row = next(row for row in records if any("separation_witness" in r for r in row["realisations"]))
    mirror = lambda row: next(r for r in row["realisations"] if "separation_witness" in r)
    reject("wrong mirror refutation reason",
           changed(mirror_row["index"], lambda row: mirror(row).__setitem__("reason", "invented")),
           "wrong mirror refutation reason")
    reject("non-strict mirror separation",
           changed(mirror_row["index"], lambda row: mirror(row)["separation_witness"].__setitem__(
               "squared_distance", "[0.5 +/- 0.5]")),
           "does not prove")
    reject("wrong mirror signature",
           changed(mirror_row["index"], lambda row: mirror(row)["signature"]["cycles"].pop()),
           "not the explicit extra candidate")
    extra = lambda row: next(r for r in row["realisations"] if "development" in r)
    reject("wrong extra signature with unchanged facet multiset",
           changed(18, lambda row: extra(row)["signature"]["cycles"].__setitem__(
               0, copy.deepcopy(extra(row)["signature"]["cycles"][-1]))),
           "not the explicit extra candidate")
    reject("unresolved extra development",
           changed(18, lambda row: extra(row)["development"]["statistics"].__setitem__("open", 1)),
           "exhausted, resolved")
    reject("narrowed whole-class ROOT witness",
           changed(18, lambda row: extra(row)["radius"].__setitem__("R", ["1", "1"])),
           "ROOT witness narrows")
    groups = [set(real["names"]) for row in records for real in row["realisations"]
              if real["status"] == "KNOWN"]
    finite_prefixes = ("A5", "B5", "D5", "prism-A4", "prism-B4", "prism-D4",
                       "prism-F4", "prism-H4", "prism-sadi", "prism-gap")
    finite = {i for i, group in enumerate(groups)
              if any(name.startswith(finite_prefixes) for name in group)}
    prisms = {i for i, group in enumerate(groups)
              if any(name.startswith(finite_prefixes[3:]) for name in group)}
    cube = next(i for i, group in enumerate(groups) if "B500001" in group)
    # Interchange two polygon-product aliases without changing total names,
    # class counts, per-class name counts, or the finite-104 calculation.
    swapped = [set(group) for group in groups]
    left = next(i for i, group in enumerate(swapped) if "{3}xP5" in group)
    right = next(i for i, group in enumerate(swapped) if "{3}xP6" in group)
    swapped[left].remove("{3}xP5")
    swapped[right].remove("{3}xP6")
    swapped[left].add("{3}xP6")
    swapped[right].add("{3}xP5")
    reject("same-count wrong polygon-product alias assignment",
           lambda: outcome.family_breakdown(swapped, finite, prisms, cube),
           "merges different family parameters")
    without_grand = [set(group) - {"prism-gap"} for group in groups]
    reject("grand-antiprism prism omitted from finite-list prisms",
           lambda: outcome.family_breakdown(without_grand, finite, prisms, cube),
           "include the grand-antiprism prism")
    print("PASS v2 outcome mutation controls")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path)
    parser.add_argument("--known", type=Path)
    parser.add_argument("--classes", type=Path)
    args = parser.parse_args()
    interval_tests()
    outcome_tests(args.results, args.known, args.classes)
