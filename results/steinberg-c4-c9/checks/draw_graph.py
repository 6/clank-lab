#!/usr/bin/env python3
"""Reproduce the rational drawing using only the published bundle.

With Python 3.10 or later, run ``python3 checks/draw_graph.py`` to write
data/graph.svg and data/graph.pdf; add --check to check the supplied files
without overwriting them. No third-party Python packages are needed.

The outer face is the unique 15-sided face of data/rotation.txt. Place its
vertices on the strictly convex integer polygon below. The graph is not
3-connected: a direct Tutte solve can collapse its separating pairs.
Triangulate each bounded nontriangular face by adding a temporary center,
then solve the uniform-weight Tutte equations exactly over Fraction. Omit
all temporary centers and spokes when drawing the original graph. Check
the original rotation, vertex/edge sets, and all intersections directly;
no reliance on a connectivity hypothesis of Tutte's theorem is required.

The SVG and PDF use the same coordinates rounded to six decimal places.
Both the exact solution and these finite-decimal coordinates are checked
using rational/integer orientation and closed-segment tests (including
touches, overlaps, vertices on nonincident edges, and coincident vertices).
The SVG vertex/edge elements and PDF segment/marker-start coordinates are
parsed back to check their coordinates and incidence. --check requires the supplied
files to equal the complete deterministic renderings, including all PDF
commands, SVG styling and its fixed y-axis reversal. This is not a general
SVG/PDF validator. PDF points and SVG user units have identical numeric values.

--corruption FILE applies a published control to the generated SVG before
checking it, and must exit 1 with REJECT. The rendered rational coordinates
are also checked directly by the Lean proof; this script is not trusted by
that proof.
"""

import argparse
from fractions import Fraction as Q
from functools import cmp_to_key
from itertools import combinations
import json
from pathlib import Path
import sys
import xml.etree.ElementTree as ET


ROOT = Path(__file__).resolve().parent.parent
NS = "http://www.w3.org/2000/svg"
UNIT = 10**6
SIZE = 800
# Counterclockwise, approximately equally spaced; exact convexity is checked.
POLYGON = [(1000000, 0), (913545, 406737), (669131, 743145),
           (309017, 951057), (-104528, 994522), (-500000, 866025),
           (-809017, 587785), (-978148, 207912), (-978148, -207912),
           (-809017, -587785), (-500000, -866025), (-104528, -994522),
           (309017, -951057), (669131, -743145), (913545, -406737)]


class Rejection(ValueError):
    """A failed assertion about the drawing or its mathematical inputs."""


def require(condition, message):
    if not condition:
        raise Rejection(message)


def read_inputs():
    rows = [line.split() for line in (ROOT / "data/graph.txt").read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    n, m = map(int, rows[0])
    edges = [tuple(sorted(map(int, row))) for row in rows[1:]]
    require(len(edges) == m and len(set(edges)) == m, "graph edge count")
    require(all(0 <= u < v < n for u, v in edges), "invalid graph edge")
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    rot = {}
    for line in (ROOT / "data/rotation.txt").read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        vertex, neighbors = line.split(":")
        v = int(vertex)
        require(v not in rot, "duplicate rotation vertex")
        rot[v] = list(map(int, neighbors.split()))
    require(set(rot) == set(adj), "rotation vertex set")
    for v in adj:
        require(len(rot[v]) == len(adj[v]) and set(rot[v]) == adj[v],
                f"rotation neighbors at {v}")
    reached, stack = {0}, [0]
    while stack:
        for w in adj[stack.pop()]:
            if w not in reached:
                reached.add(w)
                stack.append(w)
    require(reached == set(adj), "disconnected graph")
    darts = {(u, v) for u, v in edges} | {(v, u) for u, v in edges}
    faces = []
    while darts:
        start = dart = min(darts)
        face = []
        while True:
            require(dart in darts, "face walk repeats before closing")
            darts.remove(dart)
            u, v = dart
            face.append(u)
            dart = (v, rot[v][(rot[v].index(u) + 1) % len(rot[v])])
            if dart == start:
                break
        require(len(face) >= 3 and len(set(face)) == len(face), "nonsimple face")
        faces.append(face)
    require(n - m + len(faces) == 2, "rotation is not spherical")
    return adj, set(edges), rot, faces


def orient(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def solve(matrix):
    """Exact Gaussian elimination with two right-hand sides."""
    n = len(matrix)
    a = [[Q(x) for x in row] for row in matrix]
    for k in range(n):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        require(pivot is not None, "singular Tutte system")
        a[k], a[pivot] = a[pivot], a[k]
        for i in range(k + 1, n):
            if not a[i][k]:
                continue
            factor = a[i][k] / a[k][k]
            a[i][k] = Q(0)
            for j in range(k + 1, n + 2):
                a[i][j] -= factor * a[k][j]
    solution = [None] * n
    for i in range(n - 1, -1, -1):
        solution[i] = tuple((a[i][n + d] - sum(a[i][j] * solution[j][d]
                             for j in range(i + 1, n))) / a[i][i]
                            for d in range(2))
    return solution


def tutte(adj, faces):
    candidates = [f for f in faces if len(f) == len(POLYGON)]
    require(len(candidates) == 1, "expected unique 15-sided outer face")
    outer = candidates[0]
    for i in range(len(POLYGON)):
        a, b = POLYGON[i], POLYGON[(i + 1) % len(POLYGON)]
        require(all(orient(a, b, c) > 0 for j, c in enumerate(POLYGON)
                    if j not in (i, (i + 1) % len(POLYGON))),
                "outer polygon is not strictly convex")
    graph = {v: set(neighbors) for v, neighbors in adj.items()}
    for f in faces:
        if f == outer or len(f) == 3:
            continue
        center = len(graph)
        graph[center] = set(f)
        for v in f:
            graph[v].add(center)
    # Coordinates in points, with a 30-point margin in an 800-point square.
    fixed = {v: (Q(400) + Q(370 * x, UNIT), Q(400) + Q(370 * y, UNIT))
             for v, (x, y) in zip(outer, POLYGON)}
    interior = sorted(set(graph) - set(fixed))
    index = {v: i for i, v in enumerate(interior)}
    matrix = [[0] * (len(interior) + 2) for _ in interior]
    for v, i in index.items():
        matrix[i][i] = len(graph[v])
        for w in graph[v]:
            if w in index:
                matrix[i][index[w]] -= 1
            else:
                for d in range(2):
                    matrix[i][len(interior) + d] += fixed[w][d]
    points = dict(zip(interior, solve(matrix))) | fixed
    for v in interior:
        for d in range(2):
            require(len(graph[v]) * points[v][d] ==
                    sum(points[w][d] for w in graph[v]), "inexact Tutte solution")
    return {v: points[v] for v in adj}, outer


def on_segment(a, b, p):
    return orient(a, b, p) == 0 and all(min(a[d], b[d]) <= p[d] <= max(a[d], b[d])
                                     for d in range(2))


def intersects(a, b, c, d):
    x, y, z, w = orient(a, b, c), orient(a, b, d), orient(c, d, a), orient(c, d, b)
    return ((x * y < 0 and z * w < 0) or
            any(on_segment(p, q, r) for p, q, r, cross in
                [(a, b, c, x), (a, b, d, y), (c, d, a, z), (c, d, b, w)]
                if cross == 0))


def check_geometry(points, edges, vertices):
    require(set(points) == set(vertices), "drawing vertex set differs from graph")
    require(len(set(points.values())) == len(points), "coincident vertices")
    for (u, v), (s, t) in combinations(sorted(edges), 2):
        common = {u, v} & {s, t}
        if common:
            shared = next(iter(common))
            a, b = next(x for x in (u, v) if x != shared), next(x for x in (s, t) if x != shared)
            require(not on_segment(points[shared], points[a], points[b]) and
                    not on_segment(points[shared], points[b], points[a]),
                    f"incident edges {(u, v)} and {(s, t)} overlap")
        else:
            require(not intersects(points[u], points[v], points[s], points[t]),
                    f"nonincident edges {(u, v)} and {(s, t)} intersect")
    for v, p in points.items():
        for u, w in edges:
            if v not in (u, w):
                require(not on_segment(points[u], points[w], p),
                        f"vertex {v} lies on edge {(u, w)}")


def check_rotation(points, rot):
    def compare(a, b):
        ha, hb = (a[1] < 0 or (a[1] == 0 and a[0] < 0)), (b[1] < 0 or (b[1] == 0 and b[0] < 0))
        if ha != hb:
            return 1 if ha else -1
        cross = a[0] * b[1] - a[1] * b[0]
        return (cross < 0) - (cross > 0)

    for v, neighbors in rot.items():
        def cmp(u, w):
            return compare(tuple(points[u][d] - points[v][d] for d in range(2)),
                           tuple(points[w][d] - points[v][d] for d in range(2)))
        actual = sorted(neighbors, key=cmp_to_key(cmp))
        k = actual.index(neighbors[0])
        require(actual[k:] + actual[:k] == neighbors, f"geometric rotation differs at {v}")


def check_clearance(points, edges, outer):
    # Exact squared-distance comparisons in micropoints. Markers have radius
    # 1.8 points and strokes width 0.9, so 4.5 points is a conservative gap.
    limit = 4500000**2
    for a, b in combinations(points.values(), 2):
        require(sum((a[d] - b[d])**2 for d in range(2)) > limit, "markers too close")
    for v, p in points.items():
        for u, w in edges:
            if v in (u, w):
                continue
            a = tuple(points[w][d] - points[u][d] for d in range(2))
            b = tuple(p[d] - points[u][d] for d in range(2))
            length = sum(x*x for x in a)
            dot = sum(x*y for x, y in zip(a, b))
            if 0 < dot < length:
                require((a[0]*b[1] - a[1]*b[0])**2 > limit * length,
                        "vertex marker too close to nonincident edge")
            # Endpoint distances were already checked for all vertex pairs.
    for i, u in enumerate(outer):
        w = outer[(i + 1) % len(outer)]
        require(all(orient(points[u], points[w], p) > 0 for v, p in points.items()
                    if v not in outer), "vertex outside the stated outer face")


def decimal(micropoints):
    sign = "-" if micropoints < 0 else ""
    value = abs(micropoints)
    return f"{sign}{value // UNIT}.{value % UNIT:06d}"


def rounded(points):
    return {v: tuple(round(x * UNIT) for x in xy) for v, xy in points.items()}


def svg(points, edges):
    lines = [f'<svg xmlns="{NS}" width="800" height="800" viewBox="0 0 800 800">',
             '<title>The 82-vertex planar counterexample</title>',
             '<desc>136 straight edges; illustration only, not part of the proof.</desc>',
             '<rect width="800" height="800" fill="white"/>',
             '<g transform="translate(0 800) scale(1 -1)">',
             '<g id="edges" stroke="#253648" stroke-width="0.9" fill="none">']
    for u, v in sorted(edges):
        x, y = map(decimal, points[u])
        a, b = map(decimal, points[v])
        lines.append(f'<line id="e-{u}-{v}" x1="{x}" y1="{y}" x2="{a}" y2="{b}"/>')
    lines += ['</g>', '<g id="vertices" fill="rgb(16,30,43)">']
    for v, xy in sorted(points.items()):
        x, y = map(decimal, xy)
        lines.append(f'<circle id="v-{v}" cx="{x}" cy="{y}" r="1.8"><title>{v}</title></circle>')
    lines += ['</g>', '</g>', '</svg>', '']
    return "\n".join(lines).encode()


def check_svg(data, edges, vertices, rot):
    root = ET.fromstring(data)
    points, actual_edges = {}, set()
    for circle in root.iter(f"{{{NS}}}circle"):
        v = int(circle.attrib['id'].removeprefix('v-'))
        require(v not in points, "duplicate drawn vertex")
        points[v] = Q(circle.attrib['cx']), Q(circle.attrib['cy'])
    for line in root.iter(f"{{{NS}}}line"):
        u, v = map(int, line.attrib['id'].removeprefix('e-').split('-'))
        edge = (u, v)
        require(u < v and edge not in actual_edges, "duplicate or invalid drawn edge")
        require(u in points and v in points, "drawn edge has unknown endpoint")
        require((Q(line.attrib['x1']), Q(line.attrib['y1'])) == points[u] and
                (Q(line.attrib['x2']), Q(line.attrib['y2'])) == points[v],
                "drawn edge endpoint differs from its vertex")
        actual_edges.add(edge)
    require(actual_edges == edges, "drawing edge set differs from graph")
    check_geometry(points, actual_edges, vertices)
    check_rotation(points, rot)


def pdf(points, edges):
    # A minimal, deterministic PDF: no fonts, timestamps or external converter.
    commands = ['1 1 1 rg 0 0 800 800 re f', '0.145 0.212 0.282 RG 0.9 w']
    for u, v in sorted(edges):
        commands.append(' '.join(map(decimal, points[u])) + ' m ' +
                        ' '.join(map(decimal, points[v])) + ' l S')
    commands.append('0.063 0.118 0.169 rg')
    radius, bend = 1800000, 994113  # four cubic arcs for each vertex marker
    for x, y in points.values():
        commands.append(f'{decimal(x + radius)} {decimal(y)} m')
        for coords in [(x + radius, y + bend, x + bend, y + radius, x, y + radius),
                       (x - bend, y + radius, x - radius, y + bend, x - radius, y),
                       (x - radius, y - bend, x - bend, y - radius, x, y - radius),
                       (x + bend, y - radius, x + radius, y - bend, x + radius, y)]:
            commands.append(' '.join(map(decimal, coords)) + ' c')
        commands.append('f')
    stream = ('\n'.join(commands) + '\n').encode('ascii')
    objects = [b'<< /Type /Catalog /Pages 2 0 R >>',
               b'<< /Type /Pages /Kids [3 0 R] /Count 1 >>',
               b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 800 800] /Resources << >> /Contents 4 0 R >>',
               b'<< /Length ' + str(len(stream)).encode() + b' >>\nstream\n' + stream + b'endstream']
    data = b'%PDF-1.4\n%\xe2\xe3\xcf\xd3\n'
    offsets = [0]
    for i, obj in enumerate(objects, 1):
        offsets.append(len(data))
        data += f'{i} 0 obj\n'.encode() + obj + b'\nendobj\n'
    start = len(data)
    data += f'xref\n0 {len(objects) + 1}\n0000000000 65535 f \n'.encode()
    data += b''.join(f'{offset:010d} 00000 n \n'.encode() for offset in offsets[1:])
    data += f'trailer\n<< /Size {len(objects) + 1} /Root 1 0 R >>\nstartxref\n{start}\n%%EOF\n'.encode()
    return data


def check_pdf(data, points, edges):
    # Parse the simple vector content independently of the PDF emitter's loops.
    # Positions stay exact: each decimal number denotes a rational micropoint.
    stream = data.split(b'\nstream\n')[1].split(b'endstream')[0]
    segments, centers = [], []
    for line in stream.decode('ascii').splitlines():
        words = line.split()
        if words[-2:] == ['l', 'S']:
            require(len(words) == 7 and words[2] == 'm', "invalid PDF segment")
            a = tuple(Q(s) * UNIT for s in words[:2])
            b = tuple(Q(s) * UNIT for s in words[3:5])
            segments.append(tuple(sorted((a, b))))
        elif words[-1:] == ['m']:
            require(len(words) == 3, "invalid PDF marker")
            centers.append((Q(words[0]) * UNIT - 1800000, Q(words[1]) * UNIT))
    expected = [tuple(sorted((points[u], points[v]))) for u, v in edges]
    require(sorted(segments) == sorted(expected), "PDF edge coordinates differ from SVG")
    require(sorted(centers) == sorted(points.values()), "PDF vertex coordinates differ from SVG")


def corrupt(data, path):
    control = json.loads(path.read_text())
    require(type(control) is dict, "control must be a JSON object")
    root = ET.fromstring(data)
    if 'remove_edge' in control:
        require(set(control) == {'remove_edge'} and type(control['remove_edge']) is list
                and len(control['remove_edge']) == 2
                and all(type(v) is int for v in control['remove_edge']),
                "control edge must be a pair of integer vertex labels")
        u, v = control['remove_edge']
        group = root.find(f".//{{{NS}}}g[@id='edges']")
        line = group.find(f"{{{NS}}}line[@id='e-{u}-{v}']")
        require(line is not None, "control edge does not exist")
        group.remove(line)
    elif 'move_vertex' in control:
        require(set(control) == {'move_vertex', 'position'}
                and type(control['move_vertex']) is int
                and type(control['position']) is list and len(control['position']) == 2,
                "control needs an integer vertex label and two coordinates")
        for coordinate in control['position']:
            Q(str(coordinate))  # refuse nonfinite or malformed coordinates
        v = control['move_vertex']
        x, y = control['position']
        circle = root.find(f".//{{{NS}}}circle[@id='v-{v}']")
        require(circle is not None, "control vertex does not exist")
        circle.set('cx', str(x))
        circle.set('cy', str(y))
        for line in root.iter(f"{{{NS}}}line"):
            u, w = map(int, line.attrib['id'].removeprefix('e-').split('-'))
            if v in (u, w):
                end = '1' if v == u else '2'
                line.set('x' + end, str(x))
                line.set('y' + end, str(y))
    elif control.get('mirror') is True:
        require(set(control) == {'mirror'}, "unexpected mirror control fields")
        for element in root.iter():
            for attr in ('cx', 'x1', 'x2'):
                if attr in element.attrib:
                    element.set(attr, decimal(int((SIZE - Q(element.attrib[attr])) * UNIT)))
    else:
        raise ValueError("unknown drawing corruption")
    return ET.tostring(root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--corruption', type=Path)
    args = parser.parse_args()
    adj, edges, rot, faces = read_inputs()
    exact, outer = tutte(adj, faces)
    check_geometry(exact, edges, adj)
    check_rotation(exact, rot)
    display = rounded(exact)
    svg_data, pdf_data = svg(display, edges), pdf(display, edges)
    if args.corruption:
        try:
            damaged = corrupt(svg_data, args.corruption)
        except Exception as error:
            raise RuntimeError(f"corruption setup failed: {error}") from error
        check_svg(damaged, edges, adj, rot)
        print("PASS: corrupted drawing was accepted")
        return
    check_svg(svg_data, edges, adj, rot)
    check_pdf(pdf_data, display, edges)
    check_clearance(display, edges, outer)
    for suffix, data in [('svg', svg_data), ('pdf', pdf_data)]:
        path = ROOT / f'data/graph.{suffix}'
        if args.check:
            saved = path.read_bytes()
            if suffix == 'svg':
                check_svg(saved, edges, adj, rot)
            else:
                check_pdf(saved, display, edges)
            require(saved == data, f"supplied {path.name} differs from checked rendering")
        else:
            path.write_bytes(data)
    print(f"PASS: drawing has exactly {len(adj)} vertices and {len(edges)} edges; "
          "exact and rendered coordinates have no crossings and match the published rotation")
    print("Outer face: " + ' '.join(map(str, outer)))
    print("PASS: SVG/PDF paths agree; marker clearances exceed 4.5 points")


if __name__ == '__main__':
    try:
        main()
    except Rejection as error:
        print(f"REJECT: {error}", file=sys.stderr)
        sys.exit(1)
    except Exception as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(2)
