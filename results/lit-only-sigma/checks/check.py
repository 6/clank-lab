#!/usr/bin/env python3
"""Check the finite witness and its displayed graph and closure table."""

import json
import math
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def edges(certificate):
    rows = certificate["rows"]
    return [(i, j) for i in range(len(rows)) for j in range(i + 1, len(rows))
            if rows[i] >> j & 1]


def lit_vertices(state, n=7):
    return [i for i in range(n) if state >> i & 1]


def graph_svg(certificate):
    """Draw exactly the edges and lit vertices of the certificate."""
    points = [(180, 40), (310, 115), (310, 265), (180, 340),
              (50, 265), (50, 115), (180, 190)]
    parts = [
        '<svg xmlns="http://www.w3.org/2000/svg" width="360" height="390" '
        'viewBox="0 0 360 390" role="img" aria-labelledby="title description">',
        '<title id="title">The seven-vertex graph and starting configuration</title>',
        '<desc id="description">The complement of a six-cycle and an isolated '
        'vertex. Vertices 0, 1, 3 and 4 are lit, shown in blue.</desc>',
        '<rect width="360" height="390" fill="white"/>',
        '<g fill="none" stroke="dimgray" stroke-width="1.5">',
    ]
    for i, j in edges(certificate):
        x1, y1 = points[i]
        x2, y2 = points[j]
        if j < 6 and j - i == 3:
            dx, dy = x2 - x1, y2 - y1
            length = math.hypot(dx, dy)
            cx = (x1 + x2) / 2 - 72 * dy / length
            cy = (y1 + y2) / 2 + 72 * dx / length
            parts.append(f'<path d="M {x1} {y1} Q {cx:.3f} {cy:.3f} {x2} {y2}"/>')
        else:
            parts.append(f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}"/>')
    parts += ['</g>', '<g stroke="black" stroke-width="1.6">']
    for i, (x, y) in enumerate(points):
        fill = "lightblue" if certificate["start"] >> i & 1 else "white"
        parts.append(f'<circle cx="{x}" cy="{y}" r="17" fill="{fill}"/>')
    parts += ['</g>', '<g font-family="sans-serif" font-size="17" '
              'text-anchor="middle" dominant-baseline="central" fill="black">']
    parts += [f'<text x="{x}" y="{y}">{i}</text>' for i, (x, y) in enumerate(points)]
    parts += ['</g>', '<text x="180" y="380" font-family="sans-serif" '
              'font-size="13" text-anchor="middle" fill="black">Blue vertices are lit.</text>',
              '</svg>']
    return "\n".join(parts) + "\n"


def graph_tex(certificate):
    """The paper's picture, with labels agreeing with the certificate."""
    points = [("0", "2"), ("1.73", "1"), ("1.73", "-1"),
              ("0", "-2"), ("-1.73", "-1"), ("-1.73", "1"), ("0", "0")]
    parts = [r"\begin{tikzpicture}[scale=0.9, every node/.style={circle,draw,",
             r"  minimum size=6mm,inner sep=0pt}, line width=0.5pt]"]
    for i, (x, y) in enumerate(points):
        fill = "blue!25" if certificate["start"] >> i & 1 else "white"
        parts.append(rf"\node[fill={fill}] (v{i}) at ({x},{y}) {{$ {i} $}};")
    for i, j in edges(certificate):
        if j < 6 and j - i == 3:
            parts.append(rf"\draw (v{i}) to[bend left=18] (v{j});")
        else:
            parts.append(rf"\draw (v{i}) -- (v{j});")
    parts.append(r"\end{tikzpicture}")
    return "\n".join(parts) + "\n"


def closure_table(certificate):
    """The full valid-move table, generated from the frozen closed set."""
    parts = [r"\begin{tabular}{rll}", r"\hline",
             r"$z$ & Lit vertices & Successors \\", r"\hline"]
    for state in certificate["closed"]:
        lit = lit_vertices(state, len(certificate["rows"]))
        vertices = ",".join(map(str, lit))
        successors = ",".join(str(state ^ certificate["rows"][i]) for i in lit)
        parts.append(rf"${state}$ & $\{{{vertices}\}}$ & ${successors}$ \\")
    parts += [r"\hline", r"\end{tabular}"]
    return "\n".join(parts) + "\n"


def run_checker(script, certificate, expected):
    result = subprocess.run([sys.executable, "-I", str(ROOT / "checks" / script),
                             str(certificate)], capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(f"{script} rejected the certificate:\n{result.stderr}{result.stdout}")
    actual = json.loads(result.stdout)
    if any(actual.get(key) != value for key, value in expected.items()):
        raise RuntimeError(f"{script}: unexpected result {actual}")


def main():
    good = ROOT / "data" / "certificate.json"
    bad = ROOT / "data" / "corrupt.json"
    certificate = json.loads(good.read_text())
    corruption = json.loads(bad.read_text())
    if corruption != dict(certificate, closed=[s for s in certificate["closed"] if s != 45]):
        raise RuntimeError("The control must delete state 45 and leave the other inputs unchanged.")
    run_checker("check_certificate.py", good,
                {"accepted": True, "n": 7, "start": 27, "regular_upper": 0,
                 "lit_lower": 4, "closed_states": 10})
    run_checker("independent.py", good,
                {"accepted": True, "errors": [], "ML": 0, "ML_star": 4,
                 "lower_bound": 4, "closed_size": 10, "edges": 15})
    for checker in ("check_certificate.py", "independent.py"):
        result = subprocess.run([sys.executable, "-I", str(ROOT / "checks" / checker),
                                 str(bad)], capture_output=True, text=True)
        if result.returncode == 0:
            raise RuntimeError(f"{checker} accepted the deleted-state control.")
    print("PASS two independent certificate checkers: n=7, start=27, ML=0, ML*=4; "
          "both reject deleted-state corruption.")

    # These are mathematical display checks, not checks of file integrity.
    # Reconstruct the diagram and transition table from the accepted input.
    for filename, rendered in (("graph.svg", graph_svg(certificate)),
                               ("graph.tex", graph_tex(certificate)),
                               ("closure-table.tex", closure_table(certificate))):
        if (ROOT / "data" / filename).read_text() != rendered:
            raise RuntimeError(f"{filename} does not display the certificate faithfully.")
    transitions = sum(s.bit_count() for s in certificate["closed"])
    if transitions != 42:
        raise RuntimeError("Unexpected number of valid transitions.")
    print("PASS diagram and closure table match certificate: "
          "7 vertices, 15 edges, 10 states, 42 valid moves.")


if __name__ == "__main__":
    main()
