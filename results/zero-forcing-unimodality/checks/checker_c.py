#!/usr/bin/env python3
"""Independent exhaustive module-count cover verifier; no forcing dynamics."""

import argparse
import itertools
import json
import math
import sys


LIMIT = 1_999_999


class CoverFailure(Exception):
    def __init__(self, reason, message):
        super().__init__(message)
        self.reason = reason
        self.message = message


def fail(reason, message):
    raise CoverFailure(reason, message)


def object_without_duplicates(items):
    value = {}
    for key, item in items:
        if key in value:
            fail("C_JSON_DUPLICATE_KEY", "JSON repeats key " + key)
        value[key] = item
    return value


def load_manifest(filename):
    with open(filename, "rb") as stream:
        contents = stream.read(LIMIT + 1)
    if len(contents) > LIMIT:
        fail("C_INPUT_SIZE", "certificate must be smaller than 2,000,000 bytes")
    try:
        return json.loads(contents.decode("utf-8"), object_pairs_hook=object_without_duplicates)
    except (ValueError, UnicodeError, RecursionError) as error:
        fail("C_JSON", str(error))


def examine(data):
    if type(data) is not dict or set(data) != {"format", "graph", "modules", "coefficients", "patterns"}:
        fail("C_SCHEMA", "certificate must contain exactly format, graph, modules, coefficients, patterns")
    if data["format"] != "zf-unimodality-v1":
        fail("C_SCHEMA", "unknown format")
    graph = data["graph"]
    if type(graph) is not dict or set(graph) != {"n", "edges"}:
        fail("C_GRAPH_SCHEMA", "graph must contain exactly n and edges")
    order = graph["n"]
    if type(order) is not int or order < 0:
        fail("C_GRAPH_ORDER", "graph order must be a nonnegative integer")
    if type(graph["edges"]) is not list:
        fail("C_GRAPH_SCHEMA", "edge list required")
    neighbors = [set() for _ in range(order)]
    for position, edge in enumerate(graph["edges"]):
        if type(edge) is not list or len(edge) != 2:
            fail("C_EDGE_SCHEMA", "edge %d is not an endpoint pair" % position)
        left, right = edge
        if type(left) is not int or type(right) is not int or not (0 <= left < order and 0 <= right < order):
            fail("C_EDGE_ENDPOINT", "invalid endpoint at edge %d" % position)
        if left == right:
            fail("C_GRAPH_LOOP", "self-loop at %d" % left)
        if right in neighbors[left]:
            fail("C_GRAPH_DUPLICATE_EDGE", "duplicate undirected edge at %d" % position)
        neighbors[left].add(right)
        neighbors[right].add(left)

    blocks = data["modules"]
    if type(blocks) is not list:
        fail("C_PARTITION", "modules must be a list")
    remaining = set(range(order))
    for index, block in enumerate(blocks):
        if type(block) is not list or len(block) == 0:
            fail("C_PARTITION", "module %d is empty or is not a list" % index)
        for vertex in block:
            if type(vertex) is not int or not 0 <= vertex < order:
                fail("C_PARTITION", "module %d has an invalid vertex" % index)
            if vertex not in remaining:
                fail("C_PARTITION", "vertex %d appears in multiple module positions" % vertex)
            remaining.remove(vertex)
    if remaining:
        fail("C_PARTITION", "module partition omits vertex %d" % min(remaining))

    # C checks the shape only. It does not validate forcing or polynomial values.
    coefficients = data["coefficients"]
    if type(coefficients) is not list or len(coefficients) != order + 1:
        fail("C_COEFFICIENT_SCHEMA", "dense coefficients must have length n+1")
    if any(type(number) is not int or number < 0 for number in coefficients):
        fail("C_COEFFICIENT_SCHEMA", "coefficient entries must be nonnegative integers")

    if type(data["patterns"]) is not list:
        fail("C_PATTERN_SCHEMA", "pattern manifest must be a list")
    binary_limit = 2 ** len(blocks)
    by_mask = {}
    for entry in data["patterns"]:
        if type(entry) is not dict or set(entry) != {"mask", "forcing", "multiplicity"}:
            fail("C_PATTERN_SCHEMA", "pattern fields must be exactly mask, forcing, multiplicity")
        mask = entry["mask"]
        if type(mask) is not int or mask < 0 or mask >= binary_limit:
            fail("C_PATTERN_MASK", "binary mask is outside the module range")
        if mask in by_mask:
            fail("C_PATTERN_DUPLICATE", "binary mask %d is listed twice" % mask)
        if type(entry["forcing"]) is not bool:
            fail("C_PATTERN_SCHEMA", "forcing entry must be a boolean")
        if type(entry["multiplicity"]) is not int or entry["multiplicity"] <= 0:
            fail("C_PATTERN_SCHEMA", "multiplicity entry must be a positive integer")
        by_mask[mask] = entry
    # Deliberately no early cardinality-only missing-mask rejection: the exhaustive
    # count-vector walk below must encounter and diagnose a planted cover gap.
    return order, neighbors, blocks, by_mask


def validate_pair_forts(order, neighbors, blocks):
    total_pairs = 0
    for block_index, block in enumerate(blocks):
        for a, b in itertools.combinations(block, 2):
            total_pairs += 1
            for vertex in range(order):
                if vertex in (a, b):
                    continue
                intersection_size = int(a in neighbors[vertex]) + int(b in neighbors[vertex])
                if intersection_size == 1:
                    fail(
                        "C_PAIR_NOT_FORT",
                        "module %d pair (%d,%d) fails fort condition at external vertex %d"
                        % (block_index, a, b, vertex),
                    )
    return total_pairs


def enumerate_cover(order, blocks, by_mask):
    sizes = [len(block) for block in blocks]
    binomials = [[math.comb(size, k) for k in range(size + 1)] for size in sizes]
    vectors_seen = 0
    fort_vectors = 0
    binary_vectors = 0
    fort_weight = 0
    binary_weight = 0
    total_weight = 0
    binary_seen = set()
    for counts in itertools.product(*(range(size + 1) for size in sizes)):
        vectors_seen += 1
        weight = 1
        first_heavy_module = None
        for index, count in enumerate(counts):
            weight *= binomials[index][count]
            if count >= 2 and first_heavy_module is None:
                first_heavy_module = index
        if first_heavy_module is not None:
            # ALL pairs in this module were certified as forts directly above.
            # Thus every labeled white set with these counts contains a fort.
            fort_vectors += 1
            fort_weight += weight
        else:
            mask = 0
            for index, count in enumerate(counts):
                if count == 1:
                    mask += 2 ** index
            if mask not in by_mask:
                fail(
                    "C_COVER_GAP",
                    "uncovered binary count vector %s (mask %d, labeled weight %d): no module has two white vertices and manifest entry is missing"
                    % (list(counts), mask, weight),
                )
            if mask in binary_seen:
                fail("C_COVER_OVERLAP", "binary count vector for mask %d encountered twice" % mask)
            binary_seen.add(mask)
            declared_weight = by_mask[mask]["multiplicity"]
            if declared_weight != weight:
                fail(
                    "C_MULTIPLICITY_MISMATCH",
                    "mask %d declares %d but its count-vector binomial weight is %d"
                    % (mask, declared_weight, weight),
                )
            binary_vectors += 1
            binary_weight += weight
        total_weight += weight

    expected_vectors = 1
    for size in sizes:
        expected_vectors *= size + 1
    if vectors_seen != expected_vectors:
        fail("C_VECTOR_COUNT", "count-vector enumeration did not cover its Cartesian product")
    if binary_seen != set(by_mask) or len(binary_seen) != 2 ** len(blocks):
        fail("C_MANIFEST_COVER", "binary manifest and visited binary vectors do not coincide exactly")
    if total_weight != 2 ** order or fort_weight + binary_weight != total_weight:
        fail("C_WEIGHTED_COVER", "binomial weights do not sum to the entire labeled power set")
    return {
        "count_vectors_checked": vectors_seen,
        "fort_count_vectors": fort_vectors,
        "binary_count_vectors": binary_vectors,
        "fort_excluded_labeled_sets": fort_weight,
        "manifest_labeled_sets": binary_weight,
        "covered_labeled_sets": total_weight,
        "required_labeled_sets": 2 ** order,
        "patterns_checked": len(binary_seen),
    }


def canonical_identity(order, neighbors, blocks):
    fixed_sizes = (32, 33, 2, 2, 2, 2)
    wanted = []
    start = 0
    for width in fixed_sizes:
        wanted.append(list(range(start, start + width)))
        start += width
    if order != start or blocks != wanted:
        fail("C_CANONICAL_PARTITION", "fixed contiguous module partition required")
    membership = {}
    for index, block in enumerate(wanted):
        for vertex in block:
            membership[vertex] = index
    for left in range(order):
        for right in range(left + 1, order):
            p, q = membership[left], membership[right]
            should_be_edge = p == q or (p <= 1 < q) or (q <= 1 < p)
            if (right in neighbors[left]) != should_be_edge:
                fail("C_CANONICAL_EDGE", "explicit edge (%d,%d) disagrees with fixed graph" % (left, right))


def verify(data, generic_audit=False):
    order, neighbors, blocks, by_mask = examine(data)
    pair_count = validate_pair_forts(order, neighbors, blocks)
    report = enumerate_cover(order, blocks, by_mask)
    if not generic_audit:
        canonical_identity(order, neighbors, blocks)
    report.update({
        "checker": "C",
        "status": "accepted",
        "mode": "generic-audit" if generic_audit else "canonical",
        "n": order,
        "modules": len(blocks),
        "pair_forts_checked": pair_count,
        "forcing_labels_validated": False,
        "polynomial_validated": False,
    })
    return report


def main(argv=None):
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("certificate", help="certificate JSON path")
    command.add_argument("--generic-audit", action="store_true", help="cover the supplied graph without fixed-target identity restriction")
    arguments = command.parse_args(argv)
    try:
        report = verify(load_manifest(arguments.certificate), arguments.generic_audit)
    except CoverFailure as error:
        print(json.dumps({"checker": "C", "status": "rejected", "reason": error.reason, "detail": error.message}, sort_keys=True))
        return 1
    except OSError as error:
        print(json.dumps({"checker": "C", "status": "error", "reason": "C_INPUT_IO", "detail": str(error)}, sort_keys=True))
        return 2
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
