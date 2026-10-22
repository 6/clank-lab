#!/usr/bin/env python3
"""Draw the 36-letter prefix with its five-position attractor as an SVG.

Usage: draw_word.py WITNESSES.json OBSTRUCTION.json OUT.svg [--check]

An illustration only, not part of the proof. The letters and shaded
positions come from the first witness, and the three regions of the lower
bound from the obstruction. With --check, the drawing is regenerated and
compared with OUT.svg instead of written, so the figure in the README is
known to match the data. Standard library only.
"""

import json
import sys

CELL, LEFT, TOP = 22, 10, 10


def regions(obstruction):
    """Each group's span: from its first to its last covered position."""
    spans = []
    for group in obstruction["groups"]:
        covered = [s + k for f in group["factors"] for s in f["starts"] for k in range(len(f["factor"]))]
        spans.append((min(covered), max(covered), group["lower_bound"]))
    return spans


def draw(witness, obstruction):
    word, marked = witness["word"], set(witness["attractor"])
    width = 2 * LEFT + CELL * len(word)
    out = ['<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" '
           'viewBox="0 0 %d %d" font-family="monospace">' % (width, 110, width, 110),
           '<rect width="100%" height="100%" fill="white"/>']
    for i, letter in enumerate(word):
        x = LEFT + CELL * i
        fill = "#9db7f0" if i in marked else "white"
        out.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s" stroke="black"/>'
                   % (x, TOP, CELL, CELL, fill))
        out.append('<text x="%d" y="%d" font-size="14" text-anchor="middle">%s</text>'
                   % (x + CELL // 2, TOP + 16, letter))
        if i % 5 == 0 or i == len(word) - 1:
            out.append('<text x="%d" y="%d" font-size="10" text-anchor="middle">%d</text>'
                       % (x + CELL // 2, TOP + CELL + 13, i))
    y = TOP + CELL + 32
    for first, last, bound in regions(obstruction):
        x0, x1 = LEFT + CELL * first + 2, LEFT + CELL * (last + 1) - 2
        out.append('<path d="M%d %d V%d H%d V%d" fill="none" stroke="black"/>' % (x0, y - 5, y, x1, y - 5))
        out.append('<text x="%d" y="%d" font-size="11" text-anchor="middle">at least %d</text>'
                   % ((x0 + x1) // 2, y + 15, bound))
    out.append('</svg>')
    return "\n".join(out) + "\n"


def main():
    if len(sys.argv) not in (4, 5) or (len(sys.argv) == 5 and sys.argv[4] != "--check"):
        print(__doc__)
        return 2
    with open(sys.argv[1], encoding="utf-8") as handle:
        witness = json.load(handle)["witnesses"][0]
    with open(sys.argv[2], encoding="utf-8") as handle:
        obstruction = json.load(handle)
    svg = draw(witness, obstruction)
    if len(sys.argv) == 5:
        with open(sys.argv[3], encoding="utf-8") as handle:
            same = handle.read() == svg
        print("figure matches the data" if same else "figure differs from the data")
        return 0 if same else 1
    with open(sys.argv[3], "w", encoding="utf-8") as handle:
        handle.write(svg)
    return 0


if __name__ == "__main__":
    sys.exit(main())
