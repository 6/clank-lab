#!/usr/bin/env python3
"""Check every finite fact the proof uses, with two independent checkers.

    python3 checks/check.py

1. Coverage: the certificates in data/ contain exactly the blocks and the
   ordered seams the gluing argument needs (widths 4 to 55, width 5's
   heights, and the four tail blocks).
2. Both checkers (locked.py and independent.py, written separately) accept
   every block and every seam: each is a tiling with no recombination move.
3. Controls: an exhaustive enumeration finds 26 locked tilings of the
   6 x 4 rectangle (7 up to symmetry, as Tucker-Foltz reports) and 50 of the
   6 x 6 rectangle, and both checkers accept each of them.
4. Corruptions: both checkers reject planted faults, and the coverage check
   rejects a missing block or seam.
5. The Lean sources in lean/Generated/ are exactly the rendering of these
   certificates, so Lean checks the same coordinates.
6. The tiling figures in the paper and the README image are drawn from
   these certificates.

Python 3.10 or later, standard library only.
"""
import copy
from itertools import product
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DATA = ROOT / 'data'
sys.path.insert(0, str(HERE))
import enumerate_controls  # noqa: E402
import independent  # noqa: E402
import locked  # noqa: E402
import render_lean  # noqa: E402


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL ' + message)


def family(cert, dimensions, vertical, horizontal):
    """The certificate has exactly these blocks and these ordered seams."""
    if set(cert['blocks']) != set(dimensions):
        raise ValueError('missing or extra block')
    for name, (h, w) in dimensions.items():
        b = cert['blocks'][name]
        if (b['height'], b['width']) != (h, w):
            raise ValueError('wrong block dimensions')
    for key, want in (('vertical', vertical), ('horizontal', horizontal)):
        if sorted(cert[key]) != sorted(map(list, want)):
            raise ValueError('missing, extra or repeated ' + key + ' seam')


def tail_family():
    dims = {f'h{h}w{w}': (h, w) for h, w in product((6, 9), (8, 9))}
    vertical = [[f'h{a}w{w}', f'h{b}w{w}'] for w, a, b in product((8, 9), (6, 9), (6, 9))]
    horizontal = [[f'h{h}w{a}', f'h{h}w{b}'] for h, a, b in product((6, 9), (8, 9), (8, 9))]
    return dims, vertical, horizontal


def coverage():
    files = []
    for w in range(4, 56):
        heights = (9, 12) if w == 5 else (6, 9)
        dims = {f'h{h}w{w}': (h, w) for h in heights}
        path = f'witnesses/width-{w}.json'
        family(locked.load(DATA / path), dims, list(product(dims, repeat=2)), [])
        files.append(path)
    for h in (6, 15):
        path = f'witnesses/direct-{h}x5.json'
        family(locked.load(DATA / path), {'A': (h, 5)}, [], [])
        files.append(path)
    family(locked.load(DATA / 'palette.json'), *tail_family())
    files.append('palette.json')
    present = {p.relative_to(DATA).as_posix() for p in DATA.rglob('*.json')}
    require(present == set(files), 'data/ holds files the proof does not use, or lacks some')
    return files


def certify(files):
    blocks = seams = 0
    for path in files:
        cert = locked.load(DATA / path)
        first = locked.check_certificate(cert)
        second = independent.check_certificate(cert)
        require(first['accepted'] and second['accepted'], path)
        blocks += first['blocks']
        seams += first['seams']
    return blocks, seams


def controls():
    for w, total, orbits in ((4, 26, 7), (6, 50, 9)):
        found = enumerate_controls.enumerate_locked(6, w)
        require(found['complete'] and found['locked_tilings'] == total
                and found['symmetry_orbits'] == orbits, f'6 x {w} control count')
        # The enumerator checks every tiling it finds with independent.py and
        # returns one per symmetry class; both checkers check those again.
        for tiles in found['orbit_representatives']:
            cert = {'blocks': {'A': {'height': 6, 'width': w, 'tiles': [list(map(list, t)) for t in tiles]}},
                    'vertical': [], 'horizontal': []}
            locked.check_certificate(cert)
            independent.check_certificate(cert)


def rejected(cert, checker):
    try:
        checker(cert)
    except ValueError:
        return True
    return False


def corruptions():
    good = locked.load(DATA / 'palette.json')
    cases = []
    bad = copy.deepcopy(good)
    tile = next(iter(bad['blocks'].values()))['tiles'][0]
    tile[0] = tile[1][:]
    cases.append(('a repeated cell', bad))
    bad = copy.deepcopy(good)
    b = next(iter(bad['blocks'].values()))
    b['tiles'][0][0] = [b['height'], 0]
    cases.append(('a cell outside its block', bad))
    bad = copy.deepcopy(good)
    next(iter(bad['blocks'].values()))['tiles'][0][0][0] = True
    cases.append(('a coordinate that is not an integer', bad))
    cases.append(('two straight trominoes side by side, which recombine',
                  {'blocks': {'A': {'height': 3, 'width': 2,
                                    'tiles': [[[0, 0], [1, 0], [2, 0]], [[0, 1], [1, 1], [2, 1]]]}},
                   'vertical': [], 'horizontal': []}))
    bad = locked.load(DATA / 'witnesses/direct-6x5.json')
    bad['vertical'] = [['A', 'A']]
    cases.append(('a locked 6 x 5 block stacked on a copy of itself, which recombines', bad))
    for label, cert in cases:
        for checker in (locked.check_certificate, independent.check_certificate):
            require(rejected(cert, checker), 'accepted ' + label)
    dims, vertical, horizontal = tail_family()
    for key in ('vertical', 'horizontal'):
        bad = copy.deepcopy(good)
        bad[key].pop()
        require(rejected(bad, lambda c: family(c, dims, vertical, horizontal)),
                'coverage accepted a missing ' + key + ' seam')
    bad = copy.deepcopy(good)
    bad['blocks'].pop(next(iter(bad['blocks'])))
    require(rejected(bad, lambda c: family(c, dims, vertical, horizontal)),
            'coverage accepted a missing block')
    return 2 * len(cases) + 3


def lean_sources():
    """The rendering of data/ equals lean/Generated/, file for file."""
    records = [('Tail', DATA / 'palette.json'), ('Direct6', DATA / 'witnesses/direct-6x5.json'),
               ('Direct15', DATA / 'witnesses/direct-15x5.json')]
    records += [(f'Width{w}', DATA / f'witnesses/width-{w}.json') for w in range(4, 56)]
    loaded = [(module, render_lean.load(path)) for module, path in records]
    patterns = set()
    for _, data in loaded:
        for aa, bb in render_lean.pair_sets(data):
            for a in aa:
                for b in bb:
                    if a != b and render_lean.adjacent(a, b):
                        patterns.add(render_lean.normalized(a, b)[0])
    patterns = sorted(patterns)
    index = {p: i for i, p in enumerate(patterns)}
    outputs = {'Catalog.lean': render_lean.make_catalog(patterns),
               'Universal.lean': render_lean.final_module()}
    for module, data in loaded:
        outputs[f'{module}.lean'] = render_lean.render_module(data, module, index)
    generated = ROOT / 'lean' / 'Generated'
    require({p.name for p in generated.glob('*.lean')} == set(outputs),
            'lean/Generated/ has extra or missing files')
    for name, text in outputs.items():
        require((generated / name).read_text(encoding='utf-8') == text,
                f'lean/Generated/{name} is not the rendering of data/')
    return len(outputs), len(patterns)


def main():
    sys.stdout.reconfigure(line_buffering=True)
    files = coverage()
    print(f'PASS coverage: {len(files)} certificates hold exactly the blocks and seams the proof needs')
    blocks, seams = certify(files)
    print(f'PASS both checkers accept all {blocks} blocks and {seams} ordered seams')
    controls()
    print('PASS controls: 26 locked 6 x 4 tilings (7 up to symmetry) and 50 locked 6 x 6 tilings')
    print(f'PASS corruptions: all {corruptions()} planted faults rejected')
    modules, patterns = lean_sources()
    print(f'PASS the {modules} generated Lean files are the rendering of data/ '
          f'({patterns} interacting tile-pair patterns)')
    subprocess.run([sys.executable, str(HERE / 'figures.py')], check=True)
    print('PASS all finite checks; build lean/ with lake for the proof')


if __name__ == '__main__':
    main()
