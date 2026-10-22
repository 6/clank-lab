#!/usr/bin/env python3
"""Reproduce the optional figure of the candidate using only the published bundle.

With Python 3.10 or later, run ``python3 -I checks/draw_antiprism.py`` to
write data/antiprism.svg and data/antiprism.pdf; add --check to check the
supplied files without overwriting them. No third-party packages are needed.

The ten points are read from the exact Lean definition of the candidate,
lean/ThomsonN10/Candidate.lean: the rational height interval [heightLower,
heightUpper] and the coordinate formulas of candidateAt. The height drawn is
the interval's midpoint; the interval is narrower than 2^-300, far below the
drawing's resolution. The left panel is an orthographic view of the points
and the edges of their convex hull, with the heights h and -h of the two
squares marked; the right panel is the view from above, with the angle
pi/4 between the squares marked. Coordinates are rounded to six decimal
places of a point.

The check reads the drawn SVG back. It recovers each point's three
coordinates from its two drawn positions (x and y from the top view, z from
the side view), and requires, within 10^-6 of the unit radius: that the two
panels agree; that each recovered point equals the candidate's point with
the same index; and, from the recovered points alone, that they are unit
vectors, the poles are (0,0,1) and (0,0,-1), points 2-5 lie at one height h
in the Lean interval and 6-9 at -h, at angles k pi/2 and pi/4 + k pi/2. It
also checks the drawn hull edges, the h and pi/4 marks, the labels, and that
the PDF's points and segments are the SVG's. --check requires the supplied
files to equal the deterministic renderings byte for byte.

--corruption FILE applies a published control to the generated SVG before
checking it, and must exit 1 with REJECT. This figure is not part of the
proof.
"""

import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
import math
from pathlib import Path
import re
import sys
import xml.etree.ElementTree as ET


ROOT = Path(__file__).resolve().parent.parent
NS = "http://www.w3.org/2000/svg"
UNIT = 10**6                  # micropoints per point
WIDTH, HEIGHT = 720, 360      # points
SCALE = 140                   # points per unit length
SIDE = (190, 180)             # center of the side view
TOP = (545, 180)              # center of the top view
AZIMUTH = math.radians(-27)   # side view: direction of the viewer
ELEVATION = math.radians(16)
TOL = 1e-6                    # in units of the sphere's radius
ENERGY = 32.7169494601        # the published enclosure, to ten decimals
COLORS = {'pole': (0.75, 0.16, 0.12), 'upper': (0.10, 0.30, 0.62),
          'lower': (0.85, 0.47, 0.05)}
MARKER = 4.2                  # marker radius in points


class Rejection(ValueError):
    """A failed assertion about the drawing or its inputs."""


def require(condition, message):
    if not condition:
        raise Rejection(message)


def role(i):
    return 'pole' if i < 2 else 'upper' if i < 6 else 'lower'


# ---------------------------------------------------------------- the candidate
def read_candidate():
    """Height interval and the ten points of candidateAt, from the Lean source."""
    text = (ROOT / 'lean/ThomsonN10/Candidate.lean').read_text()
    bounds = {}
    for name in ('heightLower', 'heightUpper'):
        match = re.search(rf'^def {name} : ℚ := (\d+) / (\d+)$', text, re.M)
        require(match is not None, f"{name} not found")
        bounds[name] = Q(int(match.group(1)), int(match.group(2)))
    lower, upper = bounds['heightLower'], bounds['heightUpper']
    require(0 < lower < upper < 1, "height interval")
    require('noncomputable def rho (h : ℝ) : ℝ := Real.sqrt (1 - h ^ 2)\n' in text,
            "rho differs from sqrt(1 - h^2)")
    require('noncomputable def q (h : ℝ) : ℝ := rho h * Real.sqrt 2 / 2\n' in text,
            "q differs from rho * sqrt 2 / 2")
    match = re.search(r'noncomputable def candidateAt \(h : ℝ\) : Configuration :=\s*'
                      r'!\[(.*?)\]', text, re.S)
    require(match is not None, "candidateAt not found")
    h = (lower + upper) / 2
    rho = math.sqrt(1 - float(h) ** 2)
    values = {'0': 0.0, '1': 1.0, '(-1)': -1.0, 'h': float(h), '(-h)': -float(h),
              '(rho h)': rho, '(-rho h)': -rho,
              '(q h)': rho * math.sqrt(2) / 2, '(-q h)': -rho * math.sqrt(2) / 2}
    token = r'\(-?(?:rho h|q h|h|1)\)|0|1|h'
    points = []
    for entry in match.group(1).split(','):
        parts = re.fullmatch(rf'\s*vec ({token}) ({token}) ({token})\s*', entry)
        require(parts is not None, f"unrecognized candidate entry {entry.strip()!r}")
        points.append(tuple(values[parts.group(k)] for k in (1, 2, 3)))
    require(len(points) == 10, "candidate does not have ten points")
    return points, lower, upper


# ---------------------------------------------------------------- geometry
def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


VIEW = (math.cos(ELEVATION) * math.cos(AZIMUTH), math.cos(ELEVATION) * math.sin(AZIMUTH),
        math.sin(ELEVATION))
RIGHT = (-math.sin(AZIMUTH), math.cos(AZIMUTH), 0.0)
UP = (-math.sin(ELEVATION) * math.cos(AZIMUTH), -math.sin(ELEVATION) * math.sin(AZIMUTH),
      math.cos(ELEVATION))


def side(p):
    return (SIDE[0] + SCALE * dot(p, RIGHT), SIDE[1] - SCALE * dot(p, UP))


def top(p):
    return (TOP[0] + SCALE * p[0], TOP[1] - SCALE * p[1])


def hull(points):
    """Faces (with outward normals) and edges of the convex hull, by brute force."""
    faces = []
    for i, j, k in combinations(range(len(points)), 3):
        normal = cross(sub(points[j], points[i]), sub(points[k], points[i]))
        sides = [dot(normal, sub(p, points[i])) for m, p in enumerate(points)
                 if m not in (i, j, k)]
        if all(s < -1e-9 for s in sides) or all(s > 1e-9 for s in sides):
            if sides[0] > 0:
                normal = tuple(-x for x in normal)
            faces.append(((i, j, k), normal))
    edges = {}
    for (i, j, k), normal in faces:
        for edge in ((i, j), (i, k), (j, k)):
            edges.setdefault(edge, []).append(dot(normal, VIEW) > 0)
    return faces, {edge: any(front) for edge, front in edges.items()}


def energy(points):
    return sum(1 / math.dist(a, b) for a, b in combinations(points, 2))


# ---------------------------------------------------------------- rendering
def micro(xy):
    return tuple(round(v * UNIT) for v in xy)


def decimal(micropoints):
    sign = "-" if micropoints < 0 else ""
    value = abs(micropoints)
    return f"{sign}{value // UNIT}.{value % UNIT:06d}"


def layout(points):
    """Every drawn element, in micropoints, shared by the SVG and PDF writers."""
    h = points[2][2]
    rho = math.hypot(points[2][0], points[2][1])
    faces, visible = hull(points)
    lines, ellipses, labels = [], [], []
    marks = []
    # Side view: the sphere, the equator and the two circles of latitude.
    ellipses.append(('sphere', micro(SIDE), round(SCALE * UNIT), round(SCALE * UNIT), 'solid'))
    for name, z, radius in (('equator', 0.0, 1.0), ('lat-upper', h, rho), ('lat-lower', -h, rho)):
        center = micro(side((0.0, 0.0, z)))
        ellipses.append((name, center, round(SCALE * radius * UNIT),
                         round(SCALE * radius * math.sin(ELEVATION) * UNIT), 'dashed'))
    lines.append(('axis', micro(side((0, 0, -1.12))), micro(side((0, 0, 1.12))), 'axis'))
    # The h marks: a dimension line left of the sphere, from the equator's
    # height to each square's height (the leftmost points of the circles).
    x = SIDE[0] - 1.22 * SCALE
    for name, z in (('h-upper', h), ('h-lower', -h)):
        level = SIDE[1] - SCALE * z * math.cos(ELEVATION)
        lines.append((name, micro((x, SIDE[1])), micro((x, level)), 'mark'))
        lines.append((name + '-leader', micro((SIDE[0] - SCALE * rho, level)),
                      micro((x - 6, level)), 'leader'))
        labels.append((name + '-label', micro((x - 14, (SIDE[1] + level) / 2 + 4.5)), 'h', 'italic'))
    lines.append(('equator-leader', micro((SIDE[0] - SCALE, SIDE[1])), micro((x - 6, SIDE[1])),
                  'leader'))
    for (i, j), front in sorted(visible.items()):
        lines.append((f'e-{i}-{j}', micro(side(points[i])), micro(side(points[j])),
                      'edge' if front else 'hidden'))
    # Top view: the equator, both squares, the two rays and the pi/4 arc.
    ellipses.append(('top-equator', micro(TOP), round(SCALE * UNIT), round(SCALE * UNIT), 'solid'))
    for first in (2, 6):
        for k in range(4):
            i, j = first + k, first + (k + 1) % 4
            lines.append((f'ts-{min(i, j)}-{max(i, j)}', micro(top(points[i])),
                          micro(top(points[j])), 'upper' if first == 2 else 'lower'))
    for i in (2, 6):
        lines.append((f'ray-{i}', micro(TOP), micro(top(points[i])), 'leader'))
    radius = 0.42 * rho
    arc = (micro(top((radius, 0.0, 0.0))),
           micro(top((radius * math.cos(math.pi / 4), radius * math.sin(math.pi / 4), 0.0))))
    marks.append(('arc', micro(TOP), round(SCALE * radius * UNIT), arc))
    middle = top((0.6 * rho * math.cos(math.pi / 8), 0.6 * rho * math.sin(math.pi / 8), 0.0))
    labels.append(('arc-label', micro((middle[0] - 4, middle[1] + 4)), 'π/4', 'roman'))
    # Points and their labels; labels sit outward from the polar axis.
    drawn = []
    for i, p in enumerate(points):
        drawn.append((f's-{i}', micro(side(p)), role(i)))
        drawn.append((f't-{i}', micro(top(p)), role(i)))
        sx, sy = side(p)
        if i < 2:
            offset = (12, -6 if i == 0 else 16)
        else:
            u = dot(p, RIGHT)
            offset = (10 if u >= 0 else -17, -7 if p[2] > 0 else 16)
        labels.append((f'sl-{i}', micro((sx + offset[0], sy + offset[1])), str(i), 'roman'))
        if i >= 2:
            tx, ty = top(p)
            norm = math.hypot(p[0], p[1])
            labels.append((f'tl-{i}', micro((tx + 15 * p[0] / norm - 4,
                                             ty - 15 * p[1] / norm + 4.5)), str(i), 'roman'))
    labels.append(('tl-poles', micro((TOP[0] + 7, TOP[1] + 17)), '0, 1', 'roman'))
    labels.append(('title-side', micro((SIDE[0] - 52, 24)), 'side view', 'roman'))
    labels.append(('title-top', micro((TOP[0] - 50, 24)), 'from above', 'roman'))
    return {'lines': lines, 'ellipses': ellipses, 'labels': labels, 'marks': marks,
            'points': drawn}


STYLE = {'edge': ('#253648', '1.1', None), 'hidden': ('#253648', '0.7', '3 2.5'),
         'axis': ('#8a8f96', '0.6', '2 2'), 'mark': ('#000000', '0.8', None),
         'leader': ('#8a8f96', '0.6', None), 'upper': ('#1a4d9e', '1.0', None),
         'lower': ('#d97808', '1.0', '4 2.5'), 'solid': ('#b8bcc2', '0.7', None),
         'dashed': ('#b8bcc2', '0.7', '3 2.5')}


def rgb(color):
    return 'rgb(' + ','.join(str(round(255 * c)) for c in color) + ')'


def svg(drawing):
    out = [f'<svg xmlns="{NS}" width="{WIDTH}" height="{HEIGHT}" '
           f'viewBox="0 0 {WIDTH} {HEIGHT}">',
           '<title>The bicapped square antiprism of ten points on the sphere</title>',
           '<desc>Generated by checks/draw_antiprism.py from lean/ThomsonN10/Candidate.lean; '
           'illustration only, not part of the proof.</desc>',
           f'<rect width="{WIDTH}" height="{HEIGHT}" fill="white"/>']
    for name, (cx, cy), rx, ry, kind in drawing['ellipses']:
        color, width, dash = STYLE[kind]
        out.append(f'<ellipse id="{name}" cx="{decimal(cx)}" cy="{decimal(cy)}" '
                   f'rx="{decimal(rx)}" ry="{decimal(ry)}" fill="none" stroke="{color}" '
                   f'stroke-width="{width}"' + (f' stroke-dasharray="{dash}"' if dash else '')
                   + '/>')
    for name, (cx, cy), radius, ((x1, y1), (x2, y2)) in drawing['marks']:
        out.append(f'<path id="{name}" d="M {decimal(x1)} {decimal(y1)} A {decimal(radius)} '
                   f'{decimal(radius)} 0 0 0 {decimal(x2)} {decimal(y2)}" fill="none" '
                   'stroke="#000000" stroke-width="0.8"/>')
    for name, (x1, y1), (x2, y2), kind in drawing['lines']:
        color, width, dash = STYLE[kind]
        out.append(f'<line id="{name}" x1="{decimal(x1)}" y1="{decimal(y1)}" '
                   f'x2="{decimal(x2)}" y2="{decimal(y2)}" stroke="{color}" '
                   f'stroke-width="{width}"' + (f' stroke-dasharray="{dash}"' if dash else '')
                   + '/>')
    for name, (cx, cy), kind in drawing['points']:
        out.append(f'<circle id="{name}" cx="{decimal(cx)}" cy="{decimal(cy)}" '
                   f'r="{MARKER}" fill="{rgb(COLORS[kind])}"/>')
    for name, (x, y), text, style in drawing['labels']:
        font = ' font-style="italic"' if style == 'italic' else ''
        size = 15 if style == 'italic' else 12
        out.append(f'<text id="{name}" x="{decimal(x)}" y="{decimal(y)}" '
                   f'font-family="Helvetica, Arial, sans-serif" font-size="{size}"{font}>'
                   f'{text}</text>')
    out += ['</svg>', '']
    return '\n'.join(out).encode()


def pdf(drawing):
    # A minimal, deterministic PDF with the base-14 fonts: no embedding,
    # timestamps or external converter. PDF's y axis points up.
    def pt(x, y):
        return f'{decimal(x)} {decimal(HEIGHT * UNIT - y)}'

    def ellipse_path(cx, cy, rx, ry):
        k = 0.5522847498
        bx, by = round(k * rx), round(k * ry)
        return [f'{pt(cx + rx, cy)} m',
                f'{pt(cx + rx, cy - by)} {pt(cx + bx, cy - ry)} {pt(cx, cy - ry)} c',
                f'{pt(cx - bx, cy - ry)} {pt(cx - rx, cy - by)} {pt(cx - rx, cy)} c',
                f'{pt(cx - rx, cy + by)} {pt(cx - bx, cy + ry)} {pt(cx, cy + ry)} c',
                f'{pt(cx + bx, cy + ry)} {pt(cx + rx, cy + by)} {pt(cx + rx, cy)} c']

    def stroke(kind):
        color, width, dash = STYLE[kind]
        r, g, b = (int(color[i:i + 2], 16) / 255 for i in (1, 3, 5))
        return [f'{r:.3f} {g:.3f} {b:.3f} RG {width} w', f'[{dash or ""}] 0 d']

    commands = ['1 1 1 rg 0 0 %d %d re f' % (WIDTH, HEIGHT)]
    for name, (cx, cy), rx, ry, kind in drawing['ellipses']:
        commands += stroke(kind) + ellipse_path(cx, cy, rx, ry) + ['S']
    for name, (cx, cy), radius, ((x1, y1), (x2, y2)) in drawing['marks']:
        # One cubic for the 45-degree arc, from (x1, y1) counterclockwise.
        k = round(4 / 3 * math.tan(math.pi / 16) * radius)
        a = math.pi / 4
        c1 = (x1, y1 - k)
        c2 = (x2 + round(k * math.sin(a)), y2 + round(k * math.cos(a)))
        commands += stroke('mark') + [f'{pt(x1, y1)} m', f'{pt(*c1)} {pt(*c2)} {pt(x2, y2)} c', 'S']
    for name, a, b, kind in drawing['lines']:
        commands += stroke(kind) + [f'{pt(*a)} m {pt(*b)} l S']
    commands.append('[] 0 d')
    radius = round(MARKER * UNIT)
    for name, (cx, cy), kind in drawing['points']:
        commands.append('%.3f %.3f %.3f rg' % COLORS[kind])
        commands += ellipse_path(cx, cy, radius, radius) + ['f']
    commands.append('0 0 0 rg')
    for name, (x, y), text, style in drawing['labels']:
        if text == 'π/4':
            commands.append(f'BT /F2 12 Tf {pt(x, y)} Td (p) Tj /F1 12 Tf (/4) Tj ET')
        else:
            font, size = ('/F3', 15) if style == 'italic' else ('/F1', 12)
            commands.append(f'BT {font} {size} Tf {pt(x, y)} Td ({text}) Tj ET')
    stream = ('\n'.join(commands) + '\n').encode('ascii')
    fonts = (b'<< /Font << /F1 5 0 R /F2 6 0 R /F3 7 0 R >> >>')
    objects = [b'<< /Type /Catalog /Pages 2 0 R >>',
               b'<< /Type /Pages /Kids [3 0 R] /Count 1 >>',
               b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %d %d] /Resources '
               % (WIDTH, HEIGHT) + fonts + b' /Contents 4 0 R >>',
               b'<< /Length ' + str(len(stream)).encode() + b' >>\nstream\n' + stream + b'endstream',
               b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>',
               b'<< /Type /Font /Subtype /Type1 /BaseFont /Symbol >>',
               b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Oblique '
               b'/Encoding /WinAnsiEncoding >>']
    data = b'%PDF-1.4\n%\xe2\xe3\xcf\xd3\n'
    offsets = []
    for i, obj in enumerate(objects, 1):
        offsets.append(len(data))
        data += f'{i} 0 obj\n'.encode() + obj + b'\nendobj\n'
    start = len(data)
    data += f'xref\n0 {len(objects) + 1}\n0000000000 65535 f \n'.encode()
    data += b''.join(f'{offset:010d} 00000 n \n'.encode() for offset in offsets)
    data += (f'trailer\n<< /Size {len(objects) + 1} /Root 1 0 R >>\nstartxref\n{start}\n%%EOF\n'
             .encode())
    return data


# ---------------------------------------------------------------- checking
def number(element, attribute):
    return Q(element.attrib[attribute])


def model_top(x, y):
    return (float(x - TOP[0]) / SCALE, float(TOP[1] - y) / SCALE)


def check_svg(data, candidate, lower, upper):
    """Read the drawing back and check it against the candidate."""
    root = ET.fromstring(data)
    found = {}
    for element in root.iter():
        name = element.attrib.get('id')
        if name is not None:
            require(name not in found, f"duplicate element {name}")
            found[name] = element
    # Recover each point from its two drawn positions.
    recovered = []
    for i in range(10):
        require(f's-{i}' in found and f't-{i}' in found, f"point {i} is not drawn twice")
        x, y = model_top(number(found[f't-{i}'], 'cx'), number(found[f't-{i}'], 'cy'))
        su = float(number(found[f's-{i}'], 'cx') - SIDE[0]) / SCALE
        sv = float(SIDE[1] - number(found[f's-{i}'], 'cy')) / SCALE
        require(abs(su - (x * RIGHT[0] + y * RIGHT[1])) <= TOL,
                f"point {i}: the side and top views disagree")
        z = (sv - x * UP[0] - y * UP[1]) / UP[2]
        recovered.append((x, y, z))
    require(len([n for n in found if re.fullmatch(r'[st]-\d+', n)]) == 20,
            "drawing has points other than the ten candidate points")
    for i, (p, r) in enumerate(zip(candidate, recovered)):
        require(max(abs(a - b) for a, b in zip(p, r)) <= TOL,
                f"drawn point {i} differs from the candidate's point {i}")
    # Properties of the recovered points alone.
    for i, r in enumerate(recovered):
        require(abs(math.sqrt(dot(r, r)) - 1) <= 2 * TOL, f"drawn point {i} is not a unit vector")
    require(max(map(abs, sub(recovered[0], (0, 0, 1)))) <= TOL, "point 0 is not the north pole")
    require(max(map(abs, sub(recovered[1], (0, 0, -1)))) <= TOL, "point 1 is not the south pole")
    h = recovered[2][2]
    require(float(lower) - TOL <= h <= float(upper) + TOL, "height outside the Lean interval")
    for k in range(4):
        for i, height, angle in ((2 + k, h, k * math.pi / 2),
                                 (6 + k, -h, math.pi / 4 + k * math.pi / 2)):
            x, y, z = recovered[i]
            require(abs(z - height) <= TOL, f"point {i} is not at height {'+' if height > 0 else '-'}h")
            turn = math.atan2(y, x) - angle
            require(abs(math.remainder(turn, 2 * math.pi)) <= 2 * TOL,
                    f"point {i} is not at angle {angle / math.pi:g} pi")
    require(abs(energy(recovered) - ENERGY) <= 1e-4, "energy of the drawn points")
    # Hull edges in the side view.
    _, visible = hull(recovered)
    drawn_edges = set()
    for name, element in found.items():
        match = re.fullmatch(r'e-(\d+)-(\d+)', name)
        if match:
            i, j = int(match.group(1)), int(match.group(2))
            require(i < j <= 9, f"invalid edge {name}")
            ends = ((number(element, 'x1'), number(element, 'y1')),
                    (number(element, 'x2'), number(element, 'y2')))
            centers = tuple((number(found[f's-{v}'], 'cx'), number(found[f's-{v}'], 'cy'))
                            for v in (i, j))
            require(ends == centers, f"edge {name} does not join its points")
            drawn_edges.add((i, j))
    require(drawn_edges == set(visible), "drawn edges are not the convex hull's edges")
    require(len(drawn_edges) == 24, "the hull should have 24 edges")
    # The two height marks: from the equator's level to each square's level.
    for name, height in (('h-upper', h), ('h-lower', -h)):
        require(name in found, f"missing mark {name}")
        line = found[name]
        require(number(line, 'x1') == number(line, 'x2'), f"mark {name} is not vertical")
        levels = [float(SIDE[1] - number(line, a)) / SCALE for a in ('y1', 'y2')]
        require(abs(levels[0]) <= TOL and abs(levels[1] - height * UP[2]) <= TOL,
                f"mark {name} does not span the equator to height {'+' if height > 0 else '-'}h")
        require(found[name + '-label'].text == 'h', f"mark {name} is not labeled h")
    for name, height in (('lat-upper', h), ('lat-lower', -h)):
        ellipse = found[name]
        center = float(SIDE[1] - number(ellipse, 'cy')) / SCALE
        require(abs(center - height * UP[2]) <= TOL, f"circle {name} is not at its square's height")
    # The pi/4 mark in the top view.
    path = found['arc'].attrib['d'].split()
    require(len(path) == 11 and path[0] == 'M' and path[3] == 'A', "arc path")
    for (x, y), angle in (((path[1], path[2]), 0.0), ((path[9], path[10]), math.pi / 4)):
        u, v = model_top(Q(x), Q(y))
        require(abs(math.remainder(math.atan2(v, u) - angle, 2 * math.pi)) <= 2 * TOL,
                "the pi/4 arc does not run from point 2's direction to point 6's")
    require(found['arc-label'].text == 'π/4', "arc label")
    for i in (2, 6):
        ray = found[f'ray-{i}']
        end = (number(ray, 'x2'), number(ray, 'y2'))
        require(end == (number(found[f't-{i}'], 'cx'), number(found[f't-{i}'], 'cy')),
                f"ray {i} does not end at point {i}")
    # Each label is nearer its own point than any other in its panel.
    for prefix, label, points in (('s', 'sl', range(10)), ('t', 'tl', range(2, 10))):
        centers = {i: (number(found[f'{prefix}-{i}'], 'cx'), number(found[f'{prefix}-{i}'], 'cy'))
                   for i in points}
        for i in points:
            text = found[f'{label}-{i}']
            require(text.text == str(i), f"label {label}-{i} does not read {i}")
            spot = (float(number(text, 'x')) + 3.5, float(number(text, 'y')) - 4.5)
            nearest = min(centers, key=lambda j: math.dist(spot, centers[j]))
            require(nearest == i, f"label {i} is nearer point {nearest} in the {prefix} panel")
    return found


def check_pdf(data, svg_elements):
    # Parse the vector content independently of the PDF emitter's loops.
    stream = data.split(b'\nstream\n')[1].split(b'endstream')[0].decode('ascii')
    segments, centers = [], []
    lines = stream.splitlines()
    for n, line in enumerate(lines):
        words = line.split()
        if words[-2:] == ['l', 'S']:
            require(len(words) == 7 and words[2] == 'm', "invalid PDF segment")
            a = (Q(words[0]), HEIGHT - Q(words[1]))
            b = (Q(words[3]), HEIGHT - Q(words[4]))
            segments.append(tuple(sorted((a, b))))
        elif words[-1:] == ['m'] and n + 5 < len(lines) and lines[n + 5] == 'f':
            centers.append((Q(words[0]) - Q(str(MARKER)), HEIGHT - Q(words[1])))
    expected = [tuple(sorted(((number(e, 'x1'), number(e, 'y1')), (number(e, 'x2'), number(e, 'y2')))))
                for e in svg_elements.values() if e.tag == f'{{{NS}}}line']
    require(sorted(segments) == sorted(expected), "PDF segments differ from the SVG's")
    points = [(number(e, 'cx'), number(e, 'cy')) for e in svg_elements.values()
              if e.tag == f'{{{NS}}}circle']
    require(sorted(centers) == sorted(points), "PDF points differ from the SVG's")


# ---------------------------------------------------------------- controls
def corrupt(data, path):
    control = json.loads(path.read_text())
    require(type(control) is dict and len(control) >= 1, "control must be a JSON object")
    root = ET.fromstring(data)
    by_id = {e.attrib['id']: e for e in root.iter() if 'id' in e.attrib}
    if 'move' in control:
        require(set(control) == {'move', 'by'} and len(control['by']) == 2, "move control fields")
        element = by_id.get(control['move'])
        require(element is not None, "control element does not exist")
        dx, dy = (Q(str(v)) for v in control['by'])
        if element.tag == f'{{{NS}}}circle':
            old = (element.attrib['cx'], element.attrib['cy'])
            new = (decimal(round((Q(old[0]) + dx) * UNIT)), decimal(round((Q(old[1]) + dy) * UNIT)))
            element.set('cx', new[0])
            element.set('cy', new[1])
            # Lines that ended at the point follow it.
            for line in root.iter(f'{{{NS}}}line'):
                for end in ('1', '2'):
                    if (line.attrib['x' + end], line.attrib['y' + end]) == old:
                        line.set('x' + end, new[0])
                        line.set('y' + end, new[1])
        else:
            require(element.tag == f'{{{NS}}}line', "only points and lines can be moved")
            for attr, delta in (('x1', dx), ('x2', dx), ('y1', dy), ('y2', dy)):
                element.set(attr, decimal(round((Q(element.attrib[attr]) + delta) * UNIT)))
    elif 'swap_labels' in control:
        require(set(control) == {'swap_labels'} and len(control['swap_labels']) == 2,
                "swap control fields")
        a, b = (str(v) for v in control['swap_labels'])
        for element in root.iter():
            name = element.attrib.get('id')
            if name is None:
                continue
            parts = name.split('-')
            parts = [b if p == a else a if p == b else p for p in parts]
            if parts[0] in ('e', 'ts'):
                parts[1:] = sorted(parts[1:], key=int)
            element.set('id', '-'.join(parts))
            if parts[0] in ('sl', 'tl') and element.text in (a, b):
                element.text = b if element.text == a else a
    elif 'remove' in control:
        require(set(control) == {'remove'}, "remove control fields")
        for parent in root.iter():
            for child in list(parent):
                if child.attrib.get('id') == control['remove']:
                    parent.remove(child)
                    break
            else:
                continue
            break
        else:
            raise ValueError("control element does not exist")
    else:
        raise ValueError("unknown drawing corruption")
    return ET.tostring(root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--corruption', type=Path)
    args = parser.parse_args()
    candidate, lower, upper = read_candidate()
    drawing = layout(candidate)
    svg_data, pdf_data = svg(drawing), pdf(drawing)
    if args.corruption:
        try:
            damaged = corrupt(svg_data, args.corruption)
        except Exception as error:
            raise RuntimeError(f"corruption setup failed: {error}") from error
        check_svg(damaged, candidate, lower, upper)
        print("PASS: corrupted drawing was accepted")
        return
    elements = check_svg(svg_data, candidate, lower, upper)
    check_pdf(pdf_data, elements)
    for suffix, data in (('svg', svg_data), ('pdf', pdf_data)):
        path = ROOT / f'data/antiprism.{suffix}'
        if args.check:
            saved = path.read_bytes()
            if suffix == 'svg':
                check_svg(saved, candidate, lower, upper)
            else:
                check_pdf(saved, elements)
            require(saved == data, f"supplied {path.name} differs from the checked rendering")
        else:
            path.write_bytes(data)
    print("PASS: the drawn points are the candidate's ten points of lean/ThomsonN10/Candidate.lean, "
          "with its 24 hull edges and the h and pi/4 marks; SVG and PDF agree")


if __name__ == '__main__':
    try:
        main()
    except Rejection as error:
        print(f"REJECT: {error}", file=sys.stderr)
        sys.exit(1)
    except Exception as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(2)
