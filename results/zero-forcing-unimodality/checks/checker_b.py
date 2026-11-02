#!/usr/bin/env python3
"""Independent labeled-set zero-forcing verifier. Construction-only delivery."""

import argparse
import itertools
import json
import sys


MAX_INPUT_BYTES = 1_999_999


class Rejection(Exception):
    def __init__(self, code, detail):
        super().__init__(detail)
        self.code = code
        self.detail = detail


def reject(code, detail):
    raise Rejection(code, detail)


def integer(value):
    return type(value) is int


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            reject("B_JSON_DUPLICATE_KEY", "duplicate JSON key: " + key)
        result[key] = value
    return result


def read_certificate(path):
    with open(path, "rb") as handle:
        raw = handle.read(MAX_INPUT_BYTES + 1)
    if len(raw) > MAX_INPUT_BYTES:
        reject("B_INPUT_SIZE", "certificate must be smaller than 2,000,000 bytes")
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object)
    except (ValueError, UnicodeError, RecursionError) as error:
        reject("B_JSON", str(error))


def inspect_certificate(certificate):
    if type(certificate) is not dict:
        reject("B_SCHEMA", "top level must be an object")
    required = {"format", "graph", "modules", "coefficients", "patterns"}
    if set(certificate) != required:
        reject("B_SCHEMA", "top-level keys must be exactly " + str(sorted(required)))
    if certificate["format"] != "zf-unimodality-v1":
        reject("B_SCHEMA", "unsupported format")
    graph = certificate["graph"]
    if type(graph) is not dict or set(graph) != {"n", "edges"}:
        reject("B_GRAPH_SCHEMA", "graph requires exactly n and edges")
    n = graph["n"]
    if not integer(n) or n < 0:
        reject("B_GRAPH_ORDER", "n must be a nonnegative integer")
    edges = graph["edges"]
    if type(edges) is not list:
        reject("B_GRAPH_SCHEMA", "edges must be a list")
    adjacency = [0] * n
    edge_set = set()
    for index, edge in enumerate(edges):
        if type(edge) is not list or len(edge) != 2:
            reject("B_EDGE_SCHEMA", "edge %d must have two endpoints" % index)
        u, v = edge
        if not integer(u) or not integer(v) or not (0 <= u < n and 0 <= v < n):
            reject("B_EDGE_ENDPOINT", "edge %d has an invalid endpoint" % index)
        if u == v:
            reject("B_GRAPH_LOOP", "loop at vertex %d" % u)
        pair = (min(u, v), max(u, v))
        if pair in edge_set:
            reject("B_GRAPH_DUPLICATE_EDGE", "repeated undirected edge %s" % (pair,))
        edge_set.add(pair)
        adjacency[u] |= 1 << v
        adjacency[v] |= 1 << u

    modules = certificate["modules"]
    if type(modules) is not list:
        reject("B_PARTITION", "modules must be a list")
    owner = [-1] * n
    for module_index, module in enumerate(modules):
        if type(module) is not list or not module:
            reject("B_PARTITION", "each module must be a nonempty list")
        for vertex in module:
            if not integer(vertex) or not 0 <= vertex < n:
                reject("B_PARTITION", "invalid vertex in module %d" % module_index)
            if owner[vertex] != -1:
                reject("B_PARTITION", "vertex %d occurs more than once" % vertex)
            owner[vertex] = module_index
    if any(index == -1 for index in owner):
        reject("B_PARTITION", "modules do not cover every explicit graph vertex")

    coefficients = certificate["coefficients"]
    if type(coefficients) is not list or len(coefficients) != n + 1:
        reject("B_COEFFICIENT_SCHEMA", "coefficients must have length n+1")
    if any(not integer(value) or value < 0 for value in coefficients):
        reject("B_COEFFICIENT_SCHEMA", "coefficients must be nonnegative integers")

    entries = certificate["patterns"]
    if type(entries) is not list:
        reject("B_PATTERN_SCHEMA", "patterns must be a list")
    pattern_count = 1 << len(modules)
    manifest = {}
    for entry in entries:
        if type(entry) is not dict or set(entry) != {"mask", "forcing", "multiplicity"}:
            reject("B_PATTERN_SCHEMA", "each pattern requires mask, forcing, multiplicity")
        mask = entry["mask"]
        if not integer(mask) or not 0 <= mask < pattern_count:
            reject("B_PATTERN_MASK", "mask outside the binary module range")
        if mask in manifest:
            reject("B_PATTERN_DUPLICATE", "duplicate mask %d" % mask)
        if type(entry["forcing"]) is not bool:
            reject("B_PATTERN_SCHEMA", "forcing must be a JSON boolean")
        multiplicity = entry["multiplicity"]
        if not integer(multiplicity) or multiplicity < 1:
            reject("B_PATTERN_SCHEMA", "multiplicity must be a positive integer")
        manifest[mask] = entry
    if len(manifest) != pattern_count:
        missing = next(mask for mask in range(pattern_count) if mask not in manifest)
        reject("B_PATTERN_MISSING", "missing binary mask %d" % missing)
    return n, adjacency, edge_set, modules, coefficients, manifest


def check_all_pair_forts(n, adjacency, modules):
    """Check the fort definition on every pair, against explicit vertices."""
    pair_count = 0
    for module_index, module in enumerate(modules):
        for first in range(len(module)):
            u = module[first]
            for second in range(first + 1, len(module)):
                v = module[second]
                pair_count += 1
                for outside in range(n):
                    if outside == u or outside == v:
                        continue
                    hits_u = bool(adjacency[outside] & (1 << u))
                    hits_v = bool(adjacency[outside] & (1 << v))
                    if hits_u != hits_v:
                        reject(
                            "B_PAIR_NOT_FORT",
                            "module %d pair (%d,%d): outside vertex %d has exactly one neighbor in the pair"
                            % (module_index, u, v, outside),
                        )
    return pair_count


def forces_all(adjacency, uncolored):
    """Ordinary vertex-level rule; state is the actual labeled white set."""
    all_vertices = (1 << len(adjacency)) - 1
    while uncolored:
        colored = all_vertices ^ uncolored
        changed = False
        while colored:
            vertex_bit = colored & -colored
            colored ^= vertex_bit
            vertex = vertex_bit.bit_length() - 1
            white_neighbors = adjacency[vertex] & uncolored
            if white_neighbors and not (white_neighbors & (white_neighbors - 1)):
                uncolored ^= white_neighbors
                changed = True
                # Restart with the newly colored vertex included in the scan.
                break
        if not changed:
            return False
    return True


def audit_labeled_sets(n, adjacency, modules, coefficients, manifest):
    reconstructed = [0] * (n + 1)
    occurrences = [0] * len(manifest)
    accepted = 0
    visited = 0
    # Every choice is an actual vertex or the absence of a white vertex.
    choices = [(-1,) + tuple(module) for module in modules]
    for labeled_choice in itertools.product(*choices):
        uncolored = 0
        mask = 0
        white_count = 0
        for module_index, vertex in enumerate(labeled_choice):
            if vertex != -1:
                uncolored |= 1 << vertex
                mask |= 1 << module_index
                white_count += 1
        visited += 1
        occurrences[mask] += 1
        actual = forces_all(adjacency, uncolored)
        declared = manifest[mask]["forcing"]
        if actual != declared:
            reject(
                "B_FORCING_MISMATCH",
                "mask %d labeled uncolored vertices %s: declared %s, vertex closure gives %s"
                % (mask, [v for v in labeled_choice if v != -1], declared, actual),
            )
        if actual:
            # Deliberately one increment per labeled set; no orbit weights.
            reconstructed[n - white_count] += 1
            accepted += 1
    for mask, entry in manifest.items():
        if entry["multiplicity"] != occurrences[mask]:
            reject(
                "B_MULTIPLICITY_MISMATCH",
                "mask %d: declared %d, explicitly visited %d labeled sets"
                % (mask, entry["multiplicity"], occurrences[mask]),
            )
    for degree, (declared, actual) in enumerate(zip(coefficients, reconstructed)):
        if declared != actual:
            reject(
                "B_COEFFICIENT_MISMATCH",
                "degree %d: declared %d, explicit labeled enumeration gives %d"
                % (degree, declared, actual),
            )
    return visited, accepted, reconstructed


def check_canonical(n, edge_set, modules):
    """Identity restriction, performed only after the semantic forcing audit."""
    sizes = [32, 33, 2, 2, 2, 2]
    expected_modules = []
    offset = 0
    for size in sizes:
        expected_modules.append(list(range(offset, offset + size)))
        offset += size
    if n != offset or modules != expected_modules:
        reject("B_CANONICAL_PARTITION", "expected the fixed contiguous modules 32,33,2,2,2,2")
    owner = [0] * n
    for index, module in enumerate(expected_modules):
        for vertex in module:
            owner[vertex] = index
    for u in range(n):
        for v in range(u + 1, n):
            a, b = owner[u], owner[v]
            expected = a == b or ((a < 2) != (b < 2))
            if ((u, v) in edge_set) != expected:
                reject("B_CANONICAL_EDGE", "fixed graph adjacency mismatch at (%d,%d)" % (u, v))


def verify(certificate, generic_audit=False):
    n, adjacency, edge_set, modules, coefficients, manifest = inspect_certificate(certificate)
    pair_count = check_all_pair_forts(n, adjacency, modules)
    visited, accepted, reconstructed = audit_labeled_sets(
        n, adjacency, modules, coefficients, manifest
    )
    if not generic_audit:
        check_canonical(n, edge_set, modules)
    return {
        "checker": "B",
        "status": "accepted",
        "mode": "generic-audit" if generic_audit else "canonical",
        "n": n,
        "modules": len(modules),
        "pair_forts_checked": pair_count,
        "patterns_checked": len(manifest),
        "labeled_uncolored_sets_checked": visited,
        "forcing_complements_counted": accepted,
        "coefficients": reconstructed,
        "coverage_requires_checker_c": True,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", help="UTF-8 certificate JSON")
    parser.add_argument("--generic-audit", action="store_true", help="audit supplied graph without fixed-target identity restriction")
    args = parser.parse_args(argv)
    try:
        result = verify(read_certificate(args.certificate), args.generic_audit)
    except Rejection as error:
        print(json.dumps({"checker": "B", "status": "rejected", "reason": error.code, "detail": error.detail}, sort_keys=True))
        return 1
    except OSError as error:
        print(json.dumps({"checker": "B", "status": "error", "reason": "B_INPUT_IO", "detail": str(error)}, sort_keys=True))
        return 2
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
