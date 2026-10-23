#!/usr/bin/env python3
"""Regenerate or check the SVG and TikZ drawings from the graph edge list."""

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
POSITIONS = [
    (0.7, 2.0), (6.7, 1.2), (3.5, 4.5), (-0.2, 4.0),
    (4.7, 0.6), (2.7, 2.0), (5.1, 5.0), (1.5, 4.0),
    (2.0, 0.7), (7.1, 3.9), (4.1, 3.0),
]


def render_figures(graph):
    if graph["n"] != len(POSITIONS):
        raise ValueError("figure layout needs 11 vertices")
    edges = graph["edges"]
    svg = [
        '<svg xmlns="http://www.w3.org/2000/svg" width="760" height="510" viewBox="0 0 760 510" role="img" aria-labelledby="title desc">',
        '  <title id="title">The counterexample graph G</title>',
        '  <desc id="desc">Vertices 0 through 10. Edges: ' +
        ', '.join(str(u) + '-' + str(v) for u, v in edges) + '.</desc>',
        '  <rect width="760" height="510" fill="white"/>',
        '  <g stroke="#59636e" stroke-width="1.8" fill="none">',
    ]
    points = [(90 * (x + 0.6), 90 * (5.5 - y)) for x, y in POSITIONS]
    for u, v in edges:
        x1, y1 = points[u]
        x2, y2 = points[v]
        svg.append('    <line x1="{:.1f}" y1="{:.1f}" x2="{:.1f}" y2="{:.1f}"/>'.format(x1, y1, x2, y2))
    svg.extend(['  </g>', '  <g fill="white" stroke="#17212b" stroke-width="1.7">'])
    for x, y in points:
        svg.append('    <circle cx="{:.1f}" cy="{:.1f}" r="14"/>'.format(x, y))
    svg.extend(['  </g>', '  <g fill="#17212b" font-family="sans-serif" font-size="16" text-anchor="middle" dominant-baseline="central">'])
    for vertex, (x, y) in enumerate(points):
        svg.append('    <text x="{:.1f}" y="{:.1f}">{}</text>'.format(x, y, vertex))
    svg.extend(['  </g>', '</svg>'])

    tex = [r"\begin{tikzpicture}[x=1.3cm,y=1.3cm,",
           r"  vertex/.style={circle,draw,fill=white,minimum size=6mm,inner sep=0pt,font=\small}]"
           ]
    for vertex, (x, y) in enumerate(POSITIONS):
        tex.append(r"  \coordinate (v%d) at (%.1f,%.1f);" % (vertex, x, y))
    tex.append(r"  \begin{scope}[draw=black!70,line width=0.6pt]")
    for u, v in edges:
        tex.append(r"    \draw (v%d) -- (v%d);" % (u, v))
    tex.append(r"  \end{scope}")
    for vertex in range(graph["n"]):
        tex.append(r"  \node[vertex] at (v%d) {%d};" % (vertex, vertex))
    tex.append(r"\end{tikzpicture}")
    return {"graph.svg": "\n".join(svg) + "\n", "graph.tex": "\n".join(tex) + "\n"}


def check_figures(graph):
    for name, expected in render_figures(graph).items():
        if (ROOT / "data" / name).read_text(encoding="utf-8") != expected:
            raise ValueError(name + " differs from the graph drawing; regenerate with checks/figure.py --write")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate both drawings")
    args = parser.parse_args()
    graph = json.loads((ROOT / "data" / "graph.json").read_text(encoding="utf-8"))
    if args.write:
        for name, content in render_figures(graph).items():
            (ROOT / "data" / name).write_text(content, encoding="utf-8")
        print("Wrote graph.svg and graph.tex from graph.json")
    else:
        check_figures(graph)
        print("PASS figures: SVG and TikZ match graph.json")


if __name__ == "__main__":
    main()
