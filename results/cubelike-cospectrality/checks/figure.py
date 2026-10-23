#!/usr/bin/env python3
"""Reproduce or check the optional connected-graph illustration.

The connection set is the d=7 instance of Theorem 10.2 of Arnadottir and
Godsil, Strongly cospectral vertices in normal Cayley graphs (2023).
This illustration is not a premise of the universal upper bound.
Use --write to regenerate the SVG and the two marked blocks in paper.tex;
use --check (the default) to compare them with the graph derived here.
Only the Python standard library is required.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from math import cos, pi, sin
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HIGHLIGHT = (0, 7, 120, 127)


def graph():
    basis = [1 << i for i in range(7)]
    first = basis[:3]
    last = basis[3:]
    connection = set(basis)
    connection.update(first[i] ^ first[j] for i in range(3) for j in range(i + 1, 3))
    connection.update(last[i] ^ last[j] for i in range(4) for j in range(i + 1, 4))
    connection.update(7 ^ x for x in last)
    assert sorted(connection) == [1, 2, 3, 4, 5, 6, 8, 15, 16, 23, 24, 32,
                                  39, 40, 48, 64, 71, 72, 80, 96]
    assert 0 not in connection and len(connection) == 20
    edges = [(u, u ^ s) for u in range(128) for s in sorted(connection) if u < u ^ s]
    assert len(edges) == len(set(edges)) == 1280
    assert Counter(v for edge in edges for v in edge) == Counter({v: 20 for v in range(128)})
    reached, todo = {0}, [0]
    while todo:
        u = todo.pop()
        for s in connection:
            v = u ^ s
            if v not in reached:
                reached.add(v)
                todo.append(v)
    assert len(reached) == 128
    fibers = defaultdict(list)
    for a in range(128):
        theta = sum(1 - 2 * ((a & s).bit_count() % 2) for s in connection)
        fibers[theta].append(a)
    character_class = [g for g in range(128)
                       if all(len({(a & g).bit_count() % 2 for a in group}) == 1
                              for group in fibers.values())]
    assert character_class == list(HIGHLIGHT)
    return edges, fibers


def layout():
    # The four highlighted vertices occupy the cardinal points. All other
    # vertices follow them in the same order of cosets of the highlighted class.
    representatives = sorted({min(v ^ h for h in HIGHLIGHT) for v in range(128)})
    assert len(representatives) == 32 and representatives[0] == 0
    order = [h ^ representative for h in HIGHLIGHT for representative in representatives]
    assert sorted(order) == list(range(128))
    return {v: (cos(pi / 2 - 2 * pi * i / 128), sin(pi / 2 - 2 * pi * i / 128))
            for i, v in enumerate(order)}


def svg(edges, positions):
    def point(v):
        x, y = positions[v]
        return 350 + 270 * x, 350 - 270 * y

    out = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 700 700" role="img" '
           'aria-labelledby="title description">',
           '<title id="title">Strongly cospectral vertices in a connected cubelike graph</title>',
           '<desc id="description">The connected 20-regular graph on 128 vertices from '
           'Arnadottir and Godsil, Theorem 10.2. All 1280 edges are shown. '
           'The strongly cospectral class 0, 7, 120, 127 is highlighted in blue.</desc>',
           '<rect width="700" height="700" fill="white"/>',
           '<g fill="none" stroke="rgb(137,149,163)" stroke-width="0.55" stroke-opacity="0.22">']
    for u, v in edges:
        x, y = point(u)
        xx, yy = point(v)
        out.append(f'<path d="M{x:.6f},{y:.6f} L{xx:.6f},{yy:.6f}"/>')
    out.append('</g><g fill="rgb(38,53,72)">')
    for v in range(128):
        if v not in HIGHLIGHT:
            x, y = point(v)
            out.append(f'<circle cx="{x:.6f}" cy="{y:.6f}" r="2.2"/>')
    out.append('</g><g fill="rgb(7,94,172)" stroke="white" stroke-width="2">')
    for v in HIGHLIGHT:
        x, y = point(v)
        out.append(f'<circle cx="{x:.6f}" cy="{y:.6f}" r="7"/>')
    out.append('</g><g fill="rgb(7,94,172)" font-family="sans-serif" font-size="24" '
               'font-weight="600" text-anchor="middle" dominant-baseline="central">')
    for v in HIGHLIGHT:
        x, y = positions[v]
        out.append(f'<text x="{350 + 310*x:.6f}" y="{350 - 310*y:.6f}">{v}</text>')
    out.append('</g></svg>')
    return '\n'.join(out) + '\n'


def tikz(edges, positions):
    out = [r'\begin{tikzpicture}[x=2.35cm,y=2.35cm]',
           r'\definecolor{graphblue}{RGB}{7,94,172}',
           r'\definecolor{graphgray}{RGB}{137,149,163}']
    for v in range(128):
        x, y = positions[v]
        out.append(rf'\coordinate (v{v}) at ({x:.8f},{y:.8f});')
    out.append(r'\begin{scope}[draw=graphgray,opacity=.22,line width=.15pt]')
    for u, v in edges:
        out.append(rf'\draw (v{u}) -- (v{v});')
    out.append(r'\end{scope}')
    for v in range(128):
        if v not in HIGHLIGHT:
            out.append(rf'\fill[black!75] (v{v}) circle[radius=.55pt];')
    for v in HIGHLIGHT:
        out.append(rf'\filldraw[fill=graphblue,draw=white,line width=.6pt] (v{v}) circle[radius=2pt];')
        x, y = positions[v]
        out.append(rf'\node[text=graphblue] at ({1.16*x:.8f},{1.16*y:.8f}) {{$ {v} $}};')
    out.append(r'\end{tikzpicture}')
    return '\n'.join(out) + '\n'


def table(fibers):
    out = [r'\begin{tabular}{r r c c c}', r'\hline',
           r'Eigenvalue $\theta$ & Multiplicity & $g=7$ & $g=120$ & $g=127$\\', r'\hline']
    for theta, group in sorted(fibers.items(), reverse=True):
        signs = ['+' if (group[0] & g).bit_count() % 2 == 0 else '-' for g in HIGHLIGHT[1:]]
        out.append(f'${theta}$ & {len(group)} & ${signs[0]}$ & ${signs[1]}$ & ${signs[2]}$' + r'\\')
    out += [r'\hline', r'\end{tabular}']
    return '\n'.join(out) + '\n'


def replace_block(text, label, replacement):
    start, end = f'% BEGIN EXAMPLE {label}\n', f'% END EXAMPLE {label}'
    assert text.count(start) == text.count(end) == 1
    before, rest = text.split(start)
    _, after = rest.split(end)
    return before + start + replacement + end + after


def main():
    parser = ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    edges, fibers = graph()
    positions = layout()
    expected_svg = svg(edges, positions)
    paper_path = ROOT / 'paper/paper.tex'
    old_paper = paper_path.read_text()
    new_paper = replace_block(old_paper, 'FIGURE', tikz(edges, positions))
    new_paper = replace_block(new_paper, 'TABLE', table(fibers))
    svg_path = ROOT / 'data/figure.svg'
    if args.write:
        svg_path.write_text(expected_svg)
        paper_path.write_text(new_paper)
    else:
        assert svg_path.read_text() == expected_svg, 'SVG differs; reproduce with --write'
        assert old_paper == new_paper, 'Paper figure or table differs; reproduce with --write'
    print('Figure and spectral-sign table: PASS (128 vertices, 1280 edges; '
          'highlighted class 0,7,120,127)')


if __name__ == '__main__':
    main()
