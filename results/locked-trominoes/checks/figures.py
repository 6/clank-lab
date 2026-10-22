#!/usr/bin/env python3
"""Draw the paper's tiling figures and the README image from the certificates, and check them.

    python3 checks/figures.py           check paper/paper.tex and data/tiling.svg
    python3 checks/figures.py --write   rewrite the figures in both

Each figure is TikZ code between the lines "%% BEGIN FIGURE name" and
"%% END FIGURE name" in paper/paper.tex. The tilings drawn are taken from the
certificates in data/, and every drawn rectangle is checked again, as a whole,
by both certificate checkers: it is a tiling with no recombination move.
"""
import argparse
import itertools
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import independent  # noqa: E402
import locked  # noqa: E402

ROOT = HERE.parent
PAPER = ROOT / 'paper' / 'paper.tex'
SVG = ROOT / 'data' / 'tiling.svg'
COLORS = ['tileA', 'tileB', 'tileC', 'tileD', 'tileE', 'tileF']
HEX = ['#a6cee3', '#fdcdac', '#ccebc5', '#decbe4', '#fff2ae', '#e6e6e6']


def block(path, name):
    b = locked.load(ROOT / 'data' / path)['blocks'][name]
    return b['height'], b['width'], [[tuple(c) for c in t] for t in b['tiles']]


def place(parts):
    """Union of blocks placed at (row, column) offsets: (offset, block) pairs."""
    tiles = []
    for (dr, dc), (_, _, ts) in parts:
        tiles += [[(r + dr, c + dc) for r, c in t] for t in ts]
    return tiles


def require_locked(h, w, tiles):
    """Both checkers accept the whole drawn rectangle as one block."""
    cert = {'blocks': {'A': {'height': h, 'width': w,
                             'tiles': [[list(c) for c in t] for t in tiles]}},
            'vertical': [], 'horizontal': []}
    locked.check_certificate(cert)
    independent.check_certificate(cert)


def require_tiling(h, w, tiles):
    cells = [c for t in tiles for c in t]
    assert sorted(cells) == [(r, c) for r in range(h) for c in range(w)], 'not a partition'
    assert all(independent._connected(t) and len(t) == 3 for t in tiles), 'not trominoes'


def coloring(tiles):
    """Greedy colors, so that tiles sharing an edge get different colors."""
    owner = {c: i for i, t in enumerate(tiles) for c in t}
    color = {}
    for i, t in enumerate(tiles):
        near = {owner.get((r + dr, c + dc)) for r, c in t
                for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1))}
        used = {color[j] for j in near if j in color}
        color[i] = next(k for k in range(len(COLORS)) if k not in used)
    return color


def tikz(h, w, tiles, seams=(), x0=0.0, caption=None, depth=None):
    """TikZ commands for one tiling; seams are ('h', row) or ('v', column) cuts."""
    owner = {c: i for i, t in enumerate(tiles) for c in t}
    color = coloring(tiles)
    out = []
    for i, t in enumerate(tiles):
        for r, c in sorted(t):
            out.append(f'\\fill[{COLORS[color[i]]}] ({x0 + c:g},{-r:g}) rectangle ++(1,-1);')
    out.append(f'\\draw[cellgrid] ({x0:g},0) grid ({x0 + w:g},{-h:g});')
    edges = []
    for r in range(h):
        for c in range(w):
            if c + 1 == w or owner[(r, c)] != owner[(r, c + 1)]:
                edges.append(f'({x0 + c + 1:g},{-r:g})--++(0,-1)')
            if r + 1 == h or owner[(r, c)] != owner[(r + 1, c)]:
                edges.append(f'({x0 + c:g},{-r - 1:g})--++(1,0)')
    for r in range(h):
        edges.append(f'({x0:g},{-r:g})--++(0,-1)')
    for c in range(w):
        edges.append(f'({x0 + c:g},0)--++(1,0)')
    for k in range(0, len(edges), 8):
        out.append('\\draw[tileedge] ' + ' '.join(edges[k:k + 8]) + ';')
    for kind, at in seams:
        if kind == 'h':
            out.append(f'\\draw[seam] ({x0 - 0.4:g},{-at:g})--({x0 + w + 0.4:g},{-at:g});')
        else:
            out.append(f'\\draw[seam] ({x0 + at:g},0.4)--({x0 + at:g},{-h - 0.4:g});')
    if caption:
        out.append(f'\\node[below] at ({x0 + w / 2:g},{-(depth or h) - 0.5:g}) {{{caption}}};')
    return out


def svg(h, w, tiles, seams=(), cell=24):
    """The same drawing as tikz(), as an SVG image for the README."""
    owner = {c: i for i, t in enumerate(tiles) for c in t}
    color = coloring(tiles)
    pad = cell // 2
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{w * cell + 2 * pad}" '
           f'height="{h * cell + 2 * pad}" viewBox="{-pad} {-pad} {w * cell + 2 * pad} {h * cell + 2 * pad}">']
    for i, t in enumerate(tiles):
        for r, c in sorted(t):
            out.append(f'<rect x="{c * cell}" y="{r * cell}" width="{cell}" height="{cell}" '
                       f'fill="{HEX[color[i]]}" stroke="#bbbbbb" stroke-width="0.5"/>')
    lines = []
    for r in range(h):
        for c in range(w):
            if c + 1 == w or owner[(r, c)] != owner[(r, c + 1)]:
                lines.append(f'M{(c + 1) * cell} {r * cell}v{cell}')
            if r + 1 == h or owner[(r, c)] != owner[(r + 1, c)]:
                lines.append(f'M{c * cell} {(r + 1) * cell}h{cell}')
    lines += [f'M0 {r * cell}v{cell}' for r in range(h)] + [f'M{c * cell} 0h{cell}' for c in range(w)]
    out.append(f'<path d="{"".join(lines)}" stroke="#000000" stroke-width="2.5" '
               'stroke-linecap="round" fill="none"/>')
    for kind, at in seams:
        d = f'M{-pad} {at * cell}H{w * cell + pad}' if kind == 'h' else f'M{at * cell} {-pad}V{h * cell + pad}'
        out.append(f'<path d="{d}" stroke="#b30000" stroke-width="3.5" stroke-dasharray="8 5" fill="none"/>')
    out.append('</svg>')
    return '\n'.join(out) + '\n'


def picture(scale, body):
    return [f'\\begin{{tikzpicture}}[x={scale}cm,y={scale}cm]', *body, '\\end{tikzpicture}']


def figures():
    figs = {}

    # A locked tiling of the 6 x 4 rectangle: the height-6 block of width 4.
    b6 = block('witnesses/width-4.json', 'h6w4')
    require_locked(*b6)
    figs['example'] = picture(0.55, tikz(*b6))

    # A recombination move: two straight trominoes become two L-trominoes.
    before = [[(0, 0), (1, 0), (2, 0)], [(0, 1), (1, 1), (2, 1)]]
    after = [[(0, 0), (0, 1), (1, 0)], [(1, 1), (2, 0), (2, 1)]]
    for t in (before, after):
        require_tiling(3, 2, t)
    splits = set(independent._splits(frozenset(c for t in before for c in t)))
    assert {frozenset(map(frozenset, before)), frozenset(map(frozenset, after))} <= splits
    body = tikz(3, 2, before) + ['\\draw[->,thick] (2.6,-1.5)--(3.9,-1.5);'] \
        + tikz(3, 2, after, x0=4.5)
    figs['move'] = picture(0.55, body)

    # Two different tilings of the 6 x 4 rectangle (the extra tiling a locked
    # tiling needs): all straight trominoes vertical, or the first three
    # columns horizontal.
    h, w = 6, 4
    vertical = [[(r + k, c) for k in range(3)] for r in range(0, h, 3) for c in range(w)]
    mixed = [[(r, k) for k in range(3)] for r in range(h)] \
        + [[(r + k, c) for k in range(3)] for r in range(0, h, 3) for c in range(3, w)]
    for t in (vertical, mixed):
        require_tiling(h, w, t)
    assert frozenset(map(frozenset, vertical)) != frozenset(map(frozenset, mixed))
    figs['two-tilings'] = picture(0.45, tikz(h, w, vertical)
                                  + tikz(h, w, mixed, x0=w + 2))

    # The two width-4 blocks stacked in all four orders, seams marked.
    b9 = block('witnesses/width-4.json', 'h9w4')
    body, x0 = [], 0.0
    for top, bottom in itertools.product((b6, b9), repeat=2):
        hh = top[0] + bottom[0]
        tiles = place([((0, 0), top), ((top[0], 0), bottom)])
        require_locked(hh, 4, tiles)
        body += tikz(hh, 4, tiles, seams=[('h', top[0])], x0=x0,
                     caption=f'${top[0]}+{bottom[0]}$', depth=18)
        x0 += 4 + 2.5
    figs['stack'] = picture(0.3, body)

    # Width 5: the blocks of heights 9 and 12 stacked both ways, and the two
    # single tilings of the 6 x 5 and 15 x 5 rectangles.
    c9 = block('witnesses/width-5.json', 'h9w5')
    c12 = block('witnesses/width-5.json', 'h12w5')
    d6 = block('witnesses/direct-6x5.json', 'A')
    d15 = block('witnesses/direct-15x5.json', 'A')
    body, x0 = [], 0.0
    for top, bottom in ((c9, c12), (c12, c9)):
        tiles = place([((0, 0), top), ((top[0], 0), bottom)])
        require_locked(21, 5, tiles)
        body += tikz(21, 5, tiles, seams=[('h', top[0])], x0=x0,
                     caption=f'${top[0]}+{bottom[0]}$', depth=21)
        x0 += 5 + 2.5
    for single in (d6, d15):
        require_locked(*single)
        body += tikz(*single, x0=x0, caption=f'${single[0]}\\times5$', depth=21)
        x0 += 5 + 2.5
    figs['width-five'] = picture(0.3, body)

    # The four tail blocks (heights 6, 9 by widths 8, 9) in a 2 x 2 array.
    p = {(hh, ww): block('palette.json', f'h{hh}w{ww}') for hh in (6, 9) for ww in (8, 9)}
    parts = [((0, 0), p[6, 8]), ((0, 8), p[6, 9]), ((6, 0), p[9, 8]), ((6, 8), p[9, 9])]
    tiles = place(parts)
    require_locked(15, 17, tiles)
    figs['palette'] = picture(0.32, tikz(15, 17, tiles, seams=[('h', 6), ('v', 8)]))
    figs['svg'] = svg(15, 17, tiles, seams=[('h', 6), ('v', 8)])
    return figs


def render(figs, text):
    for name, lines in figs.items():
        if name == 'svg':
            continue
        pattern = re.compile(r'(%% BEGIN FIGURE ' + re.escape(name) + r'\n).*?(%% END FIGURE '
                             + re.escape(name) + r'\n)', re.S)
        if len(pattern.findall(text)) != 1:
            raise SystemExit(f'paper.tex needs exactly one "%% BEGIN FIGURE {name}" block')
        text = pattern.sub(lambda m: m.group(1) + '\n'.join(lines) + '\n' + m.group(2), text)
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--write', action='store_true', help='rewrite the figures in paper.tex')
    args = parser.parse_args()
    figs = figures()
    text = PAPER.read_text(encoding='utf-8')
    new = render(figs, text)
    image = SVG.read_text(encoding='utf-8') if SVG.is_file() else None
    if args.write:
        PAPER.write_text(new, encoding='utf-8')
        SVG.write_text(figs['svg'], encoding='utf-8')
        print(f'wrote {len(figs) - 1} paper figures and {SVG.relative_to(ROOT)}')
    elif new != text or image != figs['svg']:
        raise SystemExit('the figures in paper/paper.tex or data/tiling.svg differ from the '
                         'certificates; run python3 checks/figures.py --write')
    else:
        print(f'PASS the {len(figs) - 1} tiling figures in the paper and the README image '
              'are drawn from the certificates')


if __name__ == '__main__':
    main()
