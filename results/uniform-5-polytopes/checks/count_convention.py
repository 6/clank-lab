"""Extract the finite 104 convention from a fully audited P16 S3 replay.

This is bookkeeping on equivalence classes, not another congruence proof.
Run audit_stage3.py first on the same replay and its input receipts.
"""
import argparse
import json
import gzip
import hashlib
import re
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path


BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE / "independent-s23"))
from provenance import json_digest, parsed_json

# Complete cycle words distinguish this signature from A510001, which has
# the same facet multiset. The primary report bridge independently checks it.
EXTRA_WORDS = [
    (3, [("A40001", "tet"), ("A40001", "tet"), ("pr-tet", "P3"), ("pr-tet", "tet")]),
    (6, [("A40001", "tet"), ("pr-tet", "P3"), ("duoprism-3-3", "P3"), ("pr-tet", "tet")]),
    (6, [("duoprism-3-3", "P3"), ("duoprism-3-3", "P3"), ("pr-tet", "P3"), ("pr-tet", "P3")]),
    (3, [("duoprism-3-3", "P3"), ("duoprism-3-3", "P3"), ("pr-tet", "tet"), ("pr-tet", "P3")]),
    (6, [("duoprism-3-3", "P3"), ("pr-tet", "P3"), ("duoprism-3-3", "P3"), ("pr-tet", "P3")]),
]
MIRROR_NAMES = {"{" + str(p) + "}x" + solid
                for p in range(3, 17) for solid in ("snic", "snid")}
MIRROR_REASON = "separation 0<distance²<1 in full star"


def authoritative_input(path, kind):
    path = Path(path) if path is not None else BASE / f"independent-s23/inputs/{kind}_p16.json.gz"
    raw = path.read_bytes()
    if path.suffix == ".gz":
        raw = gzip.decompress(raw)
    pins = {name: digest for digest, name in
            (line.split() for line in (BASE / "check_u1/current-inputs.sha256").read_text().splitlines())}
    if hashlib.sha256(raw).hexdigest() != pins[f"producer-p16/{kind}_p16.json"]:
        raise ValueError("authoritative P16 input mismatch: " + kind)
    return parsed_json(raw.decode())


def extra_signature(signature):
    expected = Counter(tuple(word) for n, word in EXTRA_WORDS for _ in range(n))
    actual = Counter(tuple(map(tuple, word)) for word in signature["cycles"])
    return (set(signature) == {"facets", "cycles"} and actual == expected and
            Counter(signature["facets"]) == {"A40001": 2, "duoprism-3-3": 6, "pr-tet": 8})


def separation_interval(text):
    # Arb's printed decimal midpoint/radius is outward-rounded. Parse both
    # decimal strings as exact rationals, never as binary64 approximations.
    match = re.fullmatch(r"\[([^ ]+) \+/- ([^ ]+)\]", text)
    if not match:
        raise ValueError("missing explicit separation interval")
    midpoint, error = map(Fraction, match.groups())
    if not error >= 0 or not 0 < midpoint - error <= midpoint + error < 1:
        raise ValueError("mirror witness does not prove 0 < distance² < 1")


def outcomes(records, known, classes, regenerated_names):
    if (not isinstance(known, list) or len(known) != 890 or len(set(known)) != 890 or
            set(known) != set(regenerated_names) or len(regenerated_names) != 890):
        raise ValueError("known-name input differs from the exact construction catalog")
    pins = {row["index"]: row for row in classes}
    if len(pins) != 563 or len(classes) != 563 or {r["index"] for r in records} != set(pins):
        raise ValueError("S3 class identities differ from authenticated input")
    known_digest = json_digest(known)
    total_signatures = known_signatures = wholly_refuted = realisations = 0
    extra_count = 0
    mirror_names = set()
    for record in records:
        pin = pins[record["index"]]
        if (record.get("input_class_sha256") != json_digest(pin) or
                record.get("known_names_sha256") != known_digest or
                list(map(Fraction, record["R"])) != list(map(Fraction, pin["R"]))):
            raise ValueError("S3 changed its authoritative class or known-name input")
        identification = record.get("identification", {})
        catalog = identification.get("known", [])
        if (identification.get("status") != "COMPLETE" or len(catalog) != 890 or
                {item["name"] for item in catalog} != set(known)):
            raise ValueError("class identification does not examine every exact known name")
        identified = {item["name"] for item in catalog if item["status"] == "IDENTIFIED-BY-ELIMINATION"}
        admitted = {name for real in record["realisations"] if real["status"] == "KNOWN"
                    for name in real.get("names", [])}
        if identified != admitted:
            raise ValueError("KNOWN names disagree with identification conclusions")
        if any(item["status"] not in {"OUTSIDE", "OUTSIDE-LIBRARY", "IDENTIFIED-BY-ELIMINATION"}
               for item in catalog):
            raise ValueError("unexpected identification status")
        by_signature = {}
        for real in record["realisations"]:
            realisations += 1
            by_signature.setdefault(json_digest(real["signature"]), []).append(real)
        total_signatures += len(by_signature)
        for group in by_signature.values():
            good = [real for real in group if real["status"] == "KNOWN"]
            bad = [real for real in group if real["status"] == "REFUTED"]
            if len(good) + len(bad) != len(group) or len(good) > 1:
                raise ValueError("unexpected signature outcome multiplicity")
            if good:
                known_signatures += 1
                if len(good[0]["names"]) != len(set(good[0]["names"])):
                    raise ValueError("duplicate name in KNOWN realization")
                if bad:
                    products = set(good[0]["names"]) & MIRROR_NAMES
                    if len(bad) != 1 or len(products) != 1:
                        raise ValueError("refuted orientation is not a listed snub product mirror")
                    mirror = next(iter(products))
                    aliases = {mirror}
                    if mirror in ("{4}xsnic", "{4}xsnid"):
                        aliases.add("prism-pr-" + mirror.split("x", 1)[1])
                    if set(good[0]["names"]) != aliases:
                        raise ValueError("unexpected names on a snub-product mirror signature")
                    if mirror in mirror_names:
                        raise ValueError("duplicate refuted mirror product")
                    mirror_names.add(mirror)
                    real = bad[0]
                    witness = real.get("separation_witness", {})
                    if (real.get("reason") != MIRROR_REASON or witness.get("reason") != MIRROR_REASON or
                            real.get("names") or "development" in real):
                        raise ValueError("wrong mirror refutation reason")
                    facets = witness.get("facets", [])
                    vertices = witness.get("model_vertices", [])
                    if (len(facets) != 2 or len(set(facets)) != 2 or
                            any(type(i) is not int or not 0 <= i < len(real["signature"]["facets"]) for i in facets) or
                            len(vertices) != 2 or any(type(i) is not int or i < 0 for i in vertices)):
                        raise ValueError("malformed mirror vertex witness")
                    separation_interval(witness.get("squared_distance", ""))
                    # Audit_stage3 separately proves full expanded-state coverage.
                    # Here require distinct orientation groups with a shared S2 source.
                    if (set(real["states"]) & set(good[0]["states"]) or
                            not set(real["s2_states"]) & set(good[0]["s2_states"])):
                        raise ValueError("mirror is not a separate orientation of the same S2 source")
            else:
                wholly_refuted += 1
                if len(bad) != 1 or record["index"] != 18 or not extra_signature(bad[0]["signature"]):
                    raise ValueError("wholly refuted signature is not the explicit extra candidate")
                extra_count += 1
                real = bad[0]
                development = real.get("development", {})
                stats = development.get("statistics", {})
                tree = development.get("tree", [])
                if (real.get("names") or real.get("reason") or "separation_witness" in real or
                        development.get("status") != "REFUTED" or stats.get("open") != 0 or
                        not tree or any(node.get("unknown") is not False for node in tree) or
                        not any(node.get("kept") == 0 for node in tree)):
                    raise ValueError("extra candidate lacks exhausted, resolved development")
                if not Fraction(record["R"][0]) < 1 < Fraction(record["R"][1]):
                    raise ValueError("extra candidate is not in the R=1 class")
    if (total_signatures, known_signatures, wholly_refuted, realisations, extra_count) != (629, 628, 1, 657, 1):
        raise ValueError("P16 signature/realisation outcomes differ from 629/628/1/657")
    if mirror_names != MIRROR_NAMES:
        raise ValueError("REFUTED mirrors do not cover exactly the 28 stated snub products")
    print("PASS outcomes: 629 signatures, 628 KNOWN, 1 explicit extra candidate; "
          "28 snub-product mirrors refuted by strict separation")


def family_breakdown(groups, finite, prisms, cube):
    """Partition audited congruence classes, retaining every family parameter."""
    platonic = {"tet", "oct", "doe", "ico"}  # cube is P4, in polygon pairs below
    archimedean = {"tut", "co", "toe", "tic", "sirco", "girco", "id",
                   "tid", "ti", "srid", "grid", "snic", "snid"}
    antiprisms = {"A" + str(n) for n in range(4, 17)}  # A3 is oct
    bases = platonic | archimedean | antiprisms
    expected_products = {(p, base) for p in range(3, 17) for base in bases}
    expected_pairs = {(p, q) for p in range(3, 17) for q in range(p, 17)}
    products, pairs = {}, {}
    for index, names in enumerate(groups):
        product_keys, pair_keys = set(), set()
        for name in names:
            match = re.fullmatch(r"\{(\d+)\}x(.+)", name)
            if not match:
                continue
            p, base = int(match[1]), match[2]
            if base in bases:
                product_keys.add((p, base))
            elif base == "cube" or re.fullmatch(r"P\d+", base):
                q = 4 if base == "cube" else int(base[1:])
                pair_keys.add(tuple(sorted((p, q))))
            else:
                raise ValueError("unclassified polygon-product base: " + base)
        if len(product_keys) > 1 or len(pair_keys) > 1:
            raise ValueError("one audited class merges different family parameters")
        for key in product_keys:
            if key in products:
                raise ValueError("product family parameter occurs in multiple classes")
            products[key] = index
        for key in pair_keys:
            if key in pairs:
                raise ValueError("unordered polygon pair occurs in multiple classes")
            pairs[key] = index
    if set(products) != expected_products or set(pairs) != expected_pairs:
        raise ValueError("audited classes do not cover the exact product/polygon-pair parameter sets")
    product_classes, pair_classes = set(products.values()), set(pairs.values())
    if (len(product_classes) != 420 or len(pair_classes) != 105 or
            product_classes & (pair_classes | finite) or pair_classes & finite != {cube} or
            pairs[(4, 4)] != cube or
            product_classes | pair_classes | finite != set(range(len(groups)))):
        raise ValueError("audited family classes do not give the disjoint 420+105-1 remainder")
    grand = {i for i, names in enumerate(groups) if "prism-gap" in names}
    if len(prisms) != 47 or len(grand) != 1 or not grand <= prisms:
        raise ValueError("47 finite-list prisms must include the grand-antiprism prism")
    if len((product_classes | pair_classes) - finite) != 524:
        raise ValueError("family remainder is not exactly 524")
    print("PASS family partition: 628 = 104 + 420 + 105 - 1; "
          "524 outside the finite list; all 14×30 product parameters and "
          "105 unordered polygon pairs represented exactly once")
    print("PASS 30 product bases: 4 Platonic excluding cube + 13 Archimedean + "
          "13 antiprisms A4...A16; 47 finite-list prisms include grand-antiprism prism")


def count(records, known=None, classes=None, regenerated_names=None):
    if known is None:
        known = authoritative_input(None, "u3_known")
    if classes is None:
        classes = authoritative_input(None, "u2_classes")
    if regenerated_names is None:
        import models
        regenerated_names = models.known_names(16)
    outcomes(records, known, classes, regenerated_names)

    if len(records) != 563 or len({r["index"] for r in records}) != 563:
        raise ValueError("expected all 563 distinct P16 classes")
    groups = []
    names_seen = set()
    root_signatures = 0
    for record in records:
        if record["status"] != "COMPLETE":
            raise ValueError("incomplete class")
        signatures, rooted = set(), set()
        for realization in record["realisations"]:
            signature = json.dumps(realization["signature"], sort_keys=True)
            signatures.add(signature)
            radius = realization.get("radius", {})
            if radius.get("status") == "UNIQUE":
                if list(map(Fraction, radius["R"])) != list(map(Fraction, record["R"])):
                    raise ValueError("ROOT witness narrows the original class")
                rooted.add(signature)
            if realization["status"] == "REFUTED":
                continue
            if realization["status"] != "KNOWN" or not realization.get("names"):
                raise ValueError("unresolved realization")
            names = set(realization["names"])
            if names_seen.intersection(names):
                raise ValueError("construction name assigned to multiple classes")
            names_seen.update(names)
            groups.append(names)
        if signatures != rooted:
            raise ValueError("a retained signature has no whole-class ROOT witness")
        root_signatures += len(rooted)
    if root_signatures != 629:
        raise ValueError("expected ROOT witnesses for all 629 signatures")
    if len(groups) != 628 or names_seen != set(known):
        raise ValueError("P16 known-model coverage mismatch")
    def selected(prefixes):
        return {i for i, group in enumerate(groups)
                if any(name.startswith(prefixes) for name in group)}
    a, b, d = (selected((prefix,)) for prefix in ("A5", "B5", "D5"))
    prisms = selected(("prism-A4", "prism-B4", "prism-D4", "prism-F4",
                       "prism-H4", "prism-sadi", "prism-gap"))
    overlap = prisms.intersection(a | b | d)
    actual = (len(a), len(b), len(d - a - b), len(prisms),
              len(overlap), len(a | b | d | prisms))
    if a & b or actual != (19, 31, 8, 47, 1, 104):
        raise ValueError(f"finite convention mismatch: {actual}")
    aliases = groups[next(iter(overlap))]
    if not {"B500001", "prism-B40001", "{4}xcube"} <= aliases:
        raise ValueError("overlap is not the expected 5-cube")
    family_breakdown(groups, a | b | d | prisms, prisms, next(iter(overlap)))
    print("PASS finite convention: 19 + 31 + 8 + 47 - 1 = 104; "
          "sole finite-list overlap is the 5-cube")
    print("PASS exact known-name coverage: all 890 authenticated and regenerated names matched")
    print("PASS ROOT coverage: all 629 signatures have a whole-class UNIQUE witness")
    print("The Open Problem Garden's reason for 105 is not established by this check.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results", type=Path)
    parser.add_argument("--known", type=Path, help="authenticated P16 known input, plain JSON or gzip")
    parser.add_argument("--classes", type=Path, help="authenticated P16 class input, plain JSON or gzip")
    args = parser.parse_args()
    count([parsed_json(line) for line in args.results.read_text().splitlines() if line],
          authoritative_input(args.known, "u3_known"),
          authoritative_input(args.classes, "u2_classes"))
