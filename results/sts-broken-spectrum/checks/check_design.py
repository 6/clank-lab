"""Check the Steiner triple system and its two bicolorings from the definitions.

Usage: python3 checks/check_design.py [data/sts39.json]

A Steiner triple system on the points 0, ..., v-1 is a family of 3-element
blocks such that every pair of distinct points lies in exactly one block.
A strict k-bicoloring is a map from the points onto {0, ..., k-1} (every
color is used) under which every block receives exactly two colors.

The script exits with status 0 if the file passes, and with status 1 and a
line starting with REJECT: otherwise.
"""
import json
import sys
from collections import Counter
from itertools import combinations


class Reject(Exception):
    pass


def check_sts(v, blocks):
    if type(v) is not int or v < 3:
        raise Reject('the number of points is not an integer of at least 3')
    if type(blocks) is not list:
        raise Reject('the blocks are not a list')
    pairs = Counter()
    seen = set()
    for block in blocks:
        if (type(block) is not list or len(block) != 3
                or any(type(x) is not int or not 0 <= x < v for x in block)
                or len(set(block)) != 3):
            raise Reject(f'{block} is not a set of three points')
        key = tuple(sorted(block))
        if key in seen:
            raise Reject(f'block {list(key)} is repeated')
        seen.add(key)
        for pair in combinations(key, 2):
            pairs[pair] += 1
    for pair in combinations(range(v), 2):
        if pairs[pair] != 1:
            raise Reject(f'pair {list(pair)} lies in {pairs[pair]} blocks')
    assert len(blocks) == v * (v - 1) // 6


def check_bicoloring(v, blocks, coloring, k, name):
    if type(coloring) is not list or len(coloring) != v:
        raise Reject(f'{name} does not give one color per point')
    if any(type(c) is not int or not 0 <= c < k for c in coloring):
        raise Reject(f'{name} uses a color outside 0..{k - 1}')
    if set(coloring) != set(range(k)):
        raise Reject(f'{name} does not use all {k} colors')
    for block in blocks:
        colors = {coloring[x] for x in block}
        if len(colors) != 2:
            raise Reject(f'{name} gives block {block} {len(colors)} colors')
    return sorted(Counter(coloring).values())


def main(argv):
    path = argv[1] if len(argv) > 1 else 'data/sts39.json'
    try:
        with open(path) as f:
            data = json.load(f)
        if set(data) != {'points', 'blocks', 'coloring3', 'coloring5'}:
            raise Reject('unexpected keys in the data file')
        v, blocks = data['points'], data['blocks']
        check_sts(v, blocks)
        sizes3 = check_bicoloring(v, blocks, data['coloring3'], 3, 'coloring3')
        sizes5 = check_bicoloring(v, blocks, data['coloring5'], 5, 'coloring5')
    except Reject as e:
        print(f'REJECT: {e}')
        return 1
    print(f'OK: Steiner triple system with {v} points and {len(blocks)} blocks')
    print(f'OK: strict 3-bicoloring with class sizes {sizes3}')
    print(f'OK: strict 5-bicoloring with class sizes {sizes5}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
