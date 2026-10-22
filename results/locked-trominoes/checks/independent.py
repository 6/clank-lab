#!/usr/bin/env python3
"""Direct, search-independent checker for finite locked tromino witnesses.

Usage: python3 independent.py certificate.json
       python3 independent.py --block block.json

No other project modules are imported.  A successful certificate check covers
exactly the supplied blocks and declared seams, not an infinite family theorem.
"""

import argparse
import itertools
import json
import sys


class InvalidCertificate(ValueError):
    """An input fails the certificate specification."""


def _require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def _connected(cells):
    """Reachability in the induced grid graph, computed without tile templates."""
    cells = set(cells)
    if not cells:
        return False
    reached = {next(iter(cells))}
    frontier = list(reached)
    while frontier:
        r, c = frontier.pop()
        for q in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)):
            if q in cells and q not in reached:
                reached.add(q)
                frontier.append(q)
    return reached == cells


def _splits(cells):
    """All unordered partitions into connected triples, each exactly once."""
    ordered = sorted(cells)
    _require(len(ordered) == 6, "pair union must have six cells")
    whole = frozenset(ordered)
    for rest in itertools.combinations(ordered[1:], 2):
        first = frozenset((ordered[0],) + rest)
        second = whole - first
        if _connected(first) and _connected(second):
            yield frozenset((first, second))


def _check_pair(first, second, context):
    expected = frozenset((first, second))
    partitions = list(_splits(first | second))
    _require(partitions == [expected],
             f"{context}: pair admits {len(partitions)} partitions, expected one")


def _parse_block(block, context):
    _require(type(block) is dict, f"{context}: block must be an object")
    _require(set(block) == {"height", "width", "tiles"},
             f"{context}: expected exactly height, width, tiles")
    h, w, raw_tiles = block["height"], block["width"], block["tiles"]
    _require(type(h) is int and h > 0, f"{context}: invalid height")
    _require(type(w) is int and w > 0, f"{context}: invalid width")
    _require(type(raw_tiles) is list, f"{context}: tiles must be an array")
    _require(3 * len(raw_tiles) == h * w, f"{context}: incorrect tile count")
    tiles, occupied = [], set()
    for i, raw_tile in enumerate(raw_tiles):
        label = f"{context}, tile {i}"
        _require(type(raw_tile) is list and len(raw_tile) == 3,
                 f"{label}: expected three cells")
        points = []
        for cell in raw_tile:
            _require(type(cell) is list and len(cell) == 2,
                     f"{label}: cell must be a two-element array")
            r, c = cell
            _require(type(r) is int and type(c) is int,
                     f"{label}: coordinates must be integers")
            _require(0 <= r < h and 0 <= c < w,
                     f"{label}: cell outside rectangle")
            points.append((r, c))
        tile = frozenset(points)
        _require(len(tile) == 3, f"{label}: duplicate cell")
        _require(_connected(tile), f"{label}: disconnected triple")
        _require(not occupied.intersection(tile), f"{label}: overlapping tiles")
        occupied.update(tile)
        tiles.append(tile)
    _require(len(occupied) == h * w, f"{context}: incomplete partition")
    return h, w, tiles


def _straight_alternative(h, w, tiles):
    """Give a distinct explicit tiling when a straight tiling differs.

    False means this simple witness was not found, not uniqueness of the tiling.
    In the intended h >= 6, h divisible by 3, w >= 4 range, a locked tiling
    always differs from the vertical straight tiling.
    """
    original = frozenset(tiles)
    if h % 3 == 0:
        candidate = frozenset(
            frozenset((r + k, c) for k in range(3))
            for r in range(0, h, 3) for c in range(w))
        if candidate != original:
            return "vertical_straight"
    if w % 3 == 0:
        candidate = frozenset(
            frozenset((r, c + k) for k in range(3))
            for r in range(h) for c in range(0, w, 3))
        if candidate != original:
            return "horizontal_straight"
    return None


def check_block(block):
    """Validate one JSON block, raising InvalidCertificate on any failure."""
    h, w, tiles = _parse_block(block, "block")
    pairs = 0
    for i, j in itertools.combinations(range(len(tiles)), 2):
        _check_pair(tiles[i], tiles[j], f"block, tiles {i}, {j}")
        pairs += 1
    alternative = _straight_alternative(h, w, tiles)
    intended = h >= 6 and h % 3 == 0 and w >= 4
    _require(not intended or alternative is not None,
             "intended rectangle lacks a distinct straight-tiling witness")
    return {"height": h, "width": w, "tiles": len(tiles), "pairs": pairs,
            "locked": True, "alternative_tiling": alternative,
            "intended_dimension_range": intended}


def check_certificate(certificate):
    """Check all blocks and all ordered full-edge seams in a certificate.

    vertical [a,b] means a above b and requires equal widths;
    horizontal [a,b] means a left of b and requires equal heights.
    """
    _require(type(certificate) is dict, "certificate must be an object")
    _require(set(certificate) == {"blocks", "vertical", "horizontal"},
             "expected exactly blocks, vertical, horizontal")
    blocks = certificate["blocks"]
    _require(type(blocks) is dict and bool(blocks), "blocks must be nonempty")
    summaries, parsed = {}, {}
    for name, block in blocks.items():
        _require(type(name) is str and bool(name), "block names must be nonempty strings")
        summaries[name] = check_block(block)
        parsed[name] = _parse_block(block, name)
    seams = []
    for direction in ("vertical", "horizontal"):
        declared = certificate[direction]
        _require(type(declared) is list, f"{direction}: seams must be an array")
        seen = set()
        for seam in declared:
            _require(type(seam) is list and len(seam) == 2,
                     f"{direction}: seam must name two blocks")
            _require(all(type(name) is str and name in parsed for name in seam),
                     f"{direction}: unknown or invalid block name")
            a, b = seam
            _require((a, b) not in seen, f"{direction}: duplicate seam {seam}")
            seen.add((a, b))
            ha, wa, ta = parsed[a]
            hb, wb, tb = parsed[b]
            if direction == "vertical":
                _require(wa == wb, f"vertical {seam}: widths differ")
                dr, dc = ha, 0
            else:
                _require(ha == hb, f"horizontal {seam}: heights differ")
                dr, dc = 0, wa
            translated = [frozenset((r + dr, c + dc) for r, c in tile) for tile in tb]
            for i, first in enumerate(ta):
                for j, second in enumerate(translated):
                    _check_pair(first, second, f"{direction} {seam}, tiles {i}, {j}")
            seams.append({"direction": direction, "blocks": seam,
                          "cross_pairs": len(ta) * len(tb), "locked": True})
    return {"accepted": True, "scope": "supplied blocks and declared seams",
            "blocks": summaries, "seams": seams}


def _unique_keys(pairs):
    result = {}
    for key, value in pairs:
        _require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate")
    parser.add_argument("--block", action="store_true")
    args = parser.parse_args(argv)
    try:
        with open(args.certificate, encoding="utf-8") as stream:
            obj = json.load(stream, object_pairs_hook=_unique_keys)
        result = check_block(obj) if args.block else check_certificate(obj)
    except (ValueError, OSError) as exc:
        print(json.dumps({"accepted": False, "error": str(exc)}), file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
