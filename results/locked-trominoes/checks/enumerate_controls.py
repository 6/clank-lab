#!/usr/bin/env python3
"""Independent exhaustive locked-tromino controls; no search-code imports.

Every three-cell subset is considered as a tile. Every disjoint tile pair is
tested by enumerating its ten unordered splits. Search covers the first empty
cell, with no symmetry reduction. Symmetries are used only to classify results.
"""

import argparse
import hashlib
import itertools
import json
import time

from independent import _connected, _splits, check_block


def enumerate_locked(height, width):
    if type(height) is not int or type(width) is not int or min(height, width) <= 0:
        raise ValueError("positive integer dimensions required")
    if height * width % 3:
        raise ValueError("area must be divisible by three")
    started = time.monotonic()
    cells = tuple((r, c) for r in range(height) for c in range(width))
    triples = [frozenset(t) for t in itertools.combinations(cells, 3) if _connected(t)]
    masks = [sum(1 << (r * width + c) for r, c in t) for t in triples]
    covering = [0] * len(cells)
    compatible = [0] * len(triples)
    for i, tile in enumerate(triples):
        for r, c in tile:
            covering[r * width + c] |= 1 << i
    checked_pairs = 0
    compatible_pairs = 0
    for i, j in itertools.combinations(range(len(triples)), 2):
        if masks[i] & masks[j]:
            continue
        checked_pairs += 1
        splits = list(_splits(triples[i] | triples[j]))
        if splits == [frozenset((triples[i], triples[j]))]:
            compatible[i] |= 1 << j
            compatible[j] |= 1 << i
            compatible_pairs += 1

    def signature(tiles):
        return tuple(sorted(tuple(sorted(t)) for t in tiles))

    def orbit_key(tiles):
        transforms = []
        for reflect_r, reflect_c in itertools.product((False, True), repeat=2):
            for transpose in ((False, True) if height == width else (False,)):
                transformed = []
                for tile in tiles:
                    points = []
                    for r, c in tile:
                        if transpose:
                            r, c = c, r
                        points.append((height - 1 - r if reflect_r else r,
                                       width - 1 - c if reflect_c else c))
                    transformed.append(points)
                transforms.append(signature(transformed))
        return min(transforms)

    full = (1 << len(cells)) - 1
    all_available = (1 << len(triples)) - 1
    nodes = 0
    solutions = []
    orbits = {}

    def visit(occupied, available, chosen):
        nonlocal nodes
        nodes += 1
        if occupied == full:
            tiles = [triples[i] for i in chosen]
            block = {"height": height, "width": width,
                     "tiles": [[list(cell) for cell in sorted(t)] for t in tiles]}
            check_block(block)
            encoded = signature(tiles)
            solutions.append(encoded)
            key = orbit_key(tiles)
            orbits[key] = orbits.get(key, 0) + 1
            return
        missing = full ^ occupied
        first = (missing & -missing).bit_length() - 1
        options = covering[first] & available
        while options:
            least = options & -options
            options ^= least
            i = least.bit_length() - 1
            if masks[i] & occupied:
                raise RuntimeError("compatibility invariant lost")
            visit(occupied | masks[i], available & compatible[i], chosen + [i])

    visit(0, all_available, [])
    canonical_bytes = json.dumps(sorted(solutions), separators=(",", ":")).encode()
    representatives = sorted(orbits)
    orbit_bytes = json.dumps(representatives, separators=(",", ":")).encode()
    return {"height": height, "width": width, "complete": True,
            "connected_triples": len(triples), "disjoint_pairs_checked": checked_pairs,
            "compatible_pairs": compatible_pairs, "nodes": nodes,
            "locked_tilings": len(solutions), "symmetry_orbits": len(orbits),
            "orbit_sizes": sorted(orbits.values()),
            "solutions_sha256": hashlib.sha256(canonical_bytes).hexdigest(),
            "orbit_representatives_sha256": hashlib.sha256(orbit_bytes).hexdigest(),
            "orbit_representatives": representatives,
            "elapsed_seconds": round(time.monotonic() - started, 6)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("height", type=int)
    parser.add_argument("width", type=int)
    args = parser.parse_args()
    print(json.dumps(enumerate_locked(args.height, args.width), sort_keys=True))


if __name__ == "__main__":
    main()
