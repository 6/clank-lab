#!/usr/bin/env python3
"""Independent exact finite rectangle topology checker; Python standard library only.

Inputs are straight rectangle boundaries in R^2, compactified by one unmarked
point at infinity. All geometry uses Fraction. No supplied facial data is used
to construct the embedding. Run with --self-test to exercise negative controls.
"""
import argparse
import copy
import hashlib
import json
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path


class Reject(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise Reject(reason)


NAMES = ('a', 'd', 'c', 'Cprime', 'C')
PARTITIONS = {'a': {1, 2}, 'd': {2, 3}, 'c': {3, 4},
              'Cprime': {1, 2, 3}, 'C': {2, 3, 4}}
DISJOINT = {frozenset(p) for p in [('a', 'c'), ('c', 'C'), ('C', 'd'),
                                 ('d', 'Cprime'), ('Cprime', 'a')]}


def rational(x):
    require(type(x) is int or type(x) is str, 'coordinates must be integers or rational strings')
    try:
        return Q(x)
    except (ValueError, ZeroDivisionError):
        raise Reject('invalid rational coordinate')


def cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def on_segment(p, a, b):
    return cross(a, b, p) == 0 and all(min(a[i], b[i]) <= p[i] <= max(a[i], b[i]) for i in (0, 1))


def inside_polygon(p, poly):
    """Strict point location by exact horizontal ray parity; reject boundary."""
    parity = False
    for a, b in zip(poly, poly[1:]+poly[:1]):
        require(not on_segment(p, a, b), 'point lies on facial boundary')
        if (a[1] > p[1]) != (b[1] > p[1]):
            hit = a[0] + (p[1]-a[1])*(b[0]-a[0])/(b[1]-a[1])
            if hit > p[0]:
                parity = not parity
    return parity


def rect_inside(p, rect):
    x0, x1, y0, y1 = rect
    return x0 < p[0] < x1 and y0 < p[1] < y1


def segments(rects):
    result = []
    for name, (x0, x1, y0, y1) in rects.items():
        vertices = [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]
        require(x0 < x1 and y0 < y1, 'rectangle must have positive width and height')
        for a, b in zip(vertices, vertices[1:]+vertices[:1]):
            result.append((name, a, b))
    return result


def geometry(rects, punctures):
    segs = segments(rects)
    splits = [{a, b} for _, a, b in segs]
    crossings = []
    for i, (n, a, b) in enumerate(segs):
        for j in range(i+1, len(segs)):
            m, c, d = segs[j]
            if n == m:
                continue  # a positive rectangle is simple by construction
            h1, h2 = a[1] == b[1], c[1] == d[1]
            if h1 == h2:
                axis = 0 if h1 else 1
                fixed = 1-axis
                overlap = max(min(a[axis], b[axis]), min(c[axis], d[axis])) <= min(max(a[axis], b[axis]), max(c[axis], d[axis]))
                require(not (a[fixed] == c[fixed] and overlap), 'coincident or touching boundaries')
                continue
            h, v = (a, c) if h1 else (c, a)
            p = (v[0], h[1])
            if on_segment(p, a, b) and on_segment(p, c, d):
                require(p not in (a, b, c, d), 'nontransverse crossing at rectangle corner')
                require(all(p != old['point'] for old in crossings), 'multiple crossing')
                crossings.append({'curves': tuple(sorted((n, m))), 'point': p})
                splits[i].add(p)
                splits[j].add(p)
    for p in punctures.values():
        require(all(not on_segment(p, a, b) for _, a, b in segs), 'puncture on curve')
    edges = []
    for (name, a, b), points in zip(segs, splits):
        ordered = sorted(points)  # either coordinate increases along axis
        edges.extend((u, v, name) for u, v in zip(ordered, ordered[1:]))
    return edges, crossings


def direction(a, b):
    dx, dy = b[0]-a[0], b[1]-a[1]
    require((dx == 0) != (dy == 0), 'non-axis-aligned or zero edge')
    return (0 if dx > 0 else 2) if dx else (1 if dy > 0 else 3)


def audit_edges(edges):
    """Check the reconstructed straight graph, including missing split vertices.

    This is separate from segment splitting: no edge interior may contain an
    intersection or even another edge endpoint. This makes deletion of one
    curve's occurrence of a crossing detectable before facial traversal.
    """
    for i, (a, b, _) in enumerate(edges):
        direction(a, b)
        for c, d, _ in edges[i+1:]:
            for p in (a, b):
                require(not on_segment(p, c, d) or p in (c, d), 'missing crossing/vertex in reconstructed edge graph')
            for p in (c, d):
                require(not on_segment(p, a, b) or p in (a, b), 'missing crossing/vertex in reconstructed edge graph')
            h1, h2 = a[1] == b[1], c[1] == d[1]
            if h1 != h2:
                h, v = (a, c) if h1 else (c, a)
                p = (v[0], h[1])
                if on_segment(p, a, b) and on_segment(p, c, d):
                    require(p in (a, b) and p in (c, d), 'unsplit geometric crossing')
            else:
                require({a, b} != {c, d}, 'duplicate reconstructed edge')


def embedding(rects, punctures):
    """Build darts, CCW rotations and left facial walks from geometry alone.

    At the head of a dart take the clockwise predecessor of its reverse.
    Positive Jordan walks bound disks; clockwise walks are grouped with the
    smallest positive disk containing a left sample, or with the outer face.
    This also handles the disconnected a/c embedding without artificial edges.
    """
    edges, crossings = geometry(rects, punctures)
    audit_edges(edges)
    darts, outgoing = [], defaultdict(list)
    for a, b, name in edges:
        for u, v in [(a, b), (b, a)]:
            outgoing[u].append(len(darts))
            darts.append((u, v, name))
    rotations = {}
    for p, ds in outgoing.items():
        rotations[p] = sorted(ds, key=lambda d: direction(*darts[d][:2]))
        require(len(set(direction(*darts[d][:2]) for d in ds)) == len(ds), 'duplicate ray')
        require(len(ds) in (2, 4), 'bad vertex degree')
        if len(ds) == 4:
            labels = [darts[d][2] for d in rotations[p]]
            require(labels[0] == labels[2] and labels[1] == labels[3] and labels[0] != labels[1], 'crossing rotation does not alternate')
    successor = []
    for d, (_, v, _) in enumerate(darts):
        rotation = rotations[v]
        successor.append(rotation[(rotation.index(d ^ 1)-1) % len(rotation)])
    require(sorted(successor) == list(range(len(darts))), 'facial successor is not a permutation')
    coordinates = [sorted({p[i] for p in outgoing}) for i in (0, 1)]
    eps = min(b-a for values in coordinates for a, b in zip(values, values[1:])) / 4
    walks, seen = [], set()
    for start in range(len(darts)):
        if start in seen:
            continue
        ds, d = [], start
        while d not in seen:
            seen.add(d)
            ds.append(d)
            d = successor[d]
        require(d == start, 'facial walk merges into another walk')
        poly = [darts[d][0] for d in ds]
        require(len(poly) == len(set(poly)), 'facial boundary is not a Jordan polygon')
        area2 = sum(a[0]*b[1]-b[0]*a[1] for a, b in zip(poly, poly[1:]+poly[:1]))
        require(area2 != 0, 'zero area face')
        u, v, _ = darts[ds[0]]
        dx, dy = v[0]-u[0], v[1]-u[1]
        length = abs(dx)+abs(dy)
        sample = ((u[0]+v[0])/2-dy/length*eps, (u[1]+v[1])/2+dx/length*eps)
        corners = sum(darts[ds[i-1]][2] != darts[ds[i]][2] for i in range(len(ds)))
        walks.append({'darts': ds, 'polygon': poly, 'area2': area2, 'sample': sample, 'corners': corners})
    positive = [i for i, w in enumerate(walks) if w['area2'] > 0]

    def locate(p):
        containing = [i for i in positive if inside_polygon(p, walks[i]['polygon'])]
        return min(containing, key=lambda i: walks[i]['area2']) if containing else -1

    faces = {i: {'walks': [], 'punctures': [], 'inside': None, 'corners': 0} for i in [-1]+positive}
    for i, w in enumerate(walks):
        f = locate(w['sample'])
        if w['area2'] > 0:
            require(f == i, 'positive facial walk not assigned to its own disk')
        mask = sorted(n for n, r in rects.items() if rect_inside(w['sample'], r))
        face = faces[f]
        require(face['inside'] is None or face['inside'] == mask, 'face boundary membership mismatch')
        face['inside'] = mask
        face['walks'].append(i)
        face['corners'] += w['corners']
    for label, p in punctures.items():
        face = faces[locate(p)]
        require(face['inside'] == sorted(n for n, r in rects.items() if rect_inside(p, r)), 'puncture and face membership mismatch')
        face['punctures'].append(label)
    # Count components independently of facial walks.
    unseen = set(outgoing)
    components = 0
    while unseen:
        components += 1
        stack = [unseen.pop()]
        while stack:
            p = stack.pop()
            for d in outgoing[p]:
                q = darts[d][1]
                if q in unseen:
                    unseen.remove(q)
                    stack.append(q)
    require(len(outgoing)-len(edges)+len(faces) == 1+components, 'planar Euler characteristic failed')
    require(sum(len(f['walks']) for f in faces.values()) == len(walks), 'unassigned boundary walk')
    # Each Jordan boundary is explicit; no graph edge crosses except at its endpoints.
    # Plane embedding implies genus zero. A face with b boundary components has
    # chi=2-b on the capped sphere, and chi=2-b-p after removing p puncture disks.
    return {'vertices': len(outgoing), 'edges': len(edges), 'components': components,
            'crossings': crossings, 'rotations': rotations, 'darts': darts,
            'walks': walks, 'faces': faces}


def canonical_faces(faces):
    return sorted((tuple(sorted(f['inside'])), tuple(sorted(f['punctures'])), f['corners']) for f in faces)


def check(data):
    require(data.get('schema') == 1, 'unsupported schema')
    require(set(data['rectangles']) == set(NAMES), 'wrong curve names')
    require(set(data['punctures']) == set(map(str, range(1, 6))), 'wrong puncture names')
    require(all(len(r) == 4 for r in data['rectangles'].values()), 'rectangle arity')
    require(all(len(p) == 2 for p in data['punctures'].values()), 'point arity')
    rects = {n: tuple(map(rational, data['rectangles'][n])) for n in NAMES}
    punctures = {int(k): tuple(map(rational, p)) for k, p in data['punctures'].items()}
    require(len(set(punctures.values())) == 5, 'punctures must be distinct')
    full = embedding(rects, punctures)
    derived_partitions = {n: {i for i, p in punctures.items() if rect_inside(p, r)} for n, r in rects.items()}
    require(derived_partitions == PARTITIONS, 'geometric puncture partitions differ from 12,23,34,123,234')
    require(set(data['partitions']) == set(NAMES), 'partition claim curve names differ')
    require(all(sorted(data['partitions'][n]) == sorted(derived_partitions[n]) for n in NAMES), 'supplied partition claim false')
    require(all(2 <= len(s) <= 3 for s in derived_partitions.values()), 'inessential curve')
    require(len({frozenset((frozenset(s), frozenset(set(range(1, 6))-s))) for s in derived_partitions.values()}) == 5, 'curves not distinct by partitions')
    counts = Counter(x['curves'] for x in full['crossings'])
    pairs = []
    universe = set(punctures)
    for n, m in combinations(NAMES, 2):
        number = counts[tuple(sorted((n, m)))]
        expected = 0 if frozenset((n, m)) in DISJOINT else 2
        require(number == expected, 'wrong pentagon crossing number for '+n+','+m)
        record = {'curves': [n, m], 'crossings': number, 'minimal': True}
        if number:
            pair = embedding({n: rects[n], m: rects[m]}, punctures)
            require(pair['components'] == 1 and len(pair['faces']) == 4, 'pair complement is not four disks')
            require(all(len(f['walks']) == 1 and f['corners'] == 2 and len(f['punctures']) >= 1 for f in pair['faces'].values()), 'empty bigon or incorrect pair faces')
            s, t = derived_partitions[n], derived_partitions[m]
            require(all((s & t, s-t, t-s, universe-(s|t))), 'partitions do not force intersections')
            record['bigon_punctures'] = sorted(sorted(f['punctures']) for f in pair['faces'].values())
        pairs.append(record)
    penner = embedding({n: rects[n] for n in ('a', 'd', 'c')}, punctures)
    fs = list(penner['faces'].values())
    require(penner['components'] == 1 and len(fs) == 6, 'Penner complement must have six regions')
    require(all(len(f['walks']) == 1 for f in fs), 'Penner region not a disk')
    require(Counter((len(f['punctures']), f['corners']) for f in fs) == Counter({(0, 4): 1, (1, 2): 4, (1, 4): 1}), 'wrong Penner disk/puncture/corner census')
    require(penner['faces'][-1]['punctures'] == [5] and penner['faces'][-1]['corners'] == 4, 'outer quadrilateral does not contain puncture 5')
    # Supplied faces are assertions checked only after independent derivation.
    require(canonical_faces(data['penner_faces']) == canonical_faces(fs), 'supplied face claims disagree with derived facial walks')
    pants_embedding = embedding({n: rects[n] for n in ('a', 'c')}, punctures)
    pants = []
    for f in pants_embedding['faces'].values():
        boundary_labels = []
        for w in f['walks']:
            labels = {pants_embedding['darts'][d][2] for d in pants_embedding['walks'][w]['darts']}
            require(len(labels) == 1, 'pants boundary not a whole simple curve')
            boundary_labels.append(next(iter(labels)))
        require(len(boundary_labels)+len(f['punctures']) == 3, 'component is not a genus zero three-boundary piece')
        pants.append(sorted([str(p) for p in f['punctures']]+boundary_labels))
    wanted_pants = sorted([['1', '2', 'a'], ['3', '4', 'c'], ['5', 'a', 'c']])
    require(sorted(pants) == wanted_pants, 'wrong derived pants pieces')
    require(sorted(sorted(map(str, p)) for p in data['pants']) == wanted_pants, 'supplied pants claim false')
    return {'status': 'PASS', 'arithmetic': 'exact fractions',
            'partitions': {n: sorted(s) for n, s in derived_partitions.items()},
            'pairs': pairs, 'full_embedding': certificate(full),
            'penner_embedding': certificate(penner),
            'pants_embedding': certificate(pants_embedding), 'pants': sorted(pants),
            'puncture_boundary_replacement': {'peripheral_annuli': 5, 'unpunctured_disks': 1}}


def certificate(model):
    return {'V': model['vertices'], 'E': model['edges'], 'F': len(model['faces']),
            'components': model['components'], 'crossings': model['crossings'],
            'rotations': [{'vertex': p, 'ccw_darts': ds} for p, ds in sorted(model['rotations'].items())],
            'darts': model['darts'],
            'faces': [{'inside': f['inside'], 'punctures': sorted(f['punctures']),
                       'corners': f['corners'], 'boundary_components': len(f['walks']),
                       'chi_before_puncture_removal': 2-len(f['walks']),
                       'walks': [model['walks'][w]['darts'] for w in f['walks']],
                       'signed_double_areas': [model['walks'][w]['area2'] for w in f['walks']]}
                      for _, f in sorted(model['faces'].items())]}


def self_test(data):
    controls = []

    def rejects(name, mutate):
        changed = copy.deepcopy(data)
        mutate(changed)
        try:
            check(changed)
        except Reject as exc:
            controls.append({'mutation': name, 'status': 'REJECT', 'reason': str(exc)})
        else:
            raise Reject('negative control accepted: '+name)

    rejects('move p2 out of a/d overlap into d-only region (7,0)', lambda d: d['punctures'].__setitem__('2', [7, 0]))
    rejects('delete a/d crossing pair by lowering d top below a bottom', lambda d: d['rectangles'].__setitem__('d', [4, 10, -4, -3]))
    rejects('delete supplied Penner face', lambda d: d['penner_faces'].pop(3))
    rejects('falsify unpunctured quadrilateral corner count', lambda d: d['penner_faces'][3].__setitem__('corners', 2))
    rejects('assign p2 to false overlap face without moving geometry', lambda d: d['penner_faces'][2].__setitem__('punctures', []))
    # A split-pair or one-crossing deletion cannot arise from transverse closed
    # rectangles. Also check an exact tangency, where the pair would disappear.
    rejects('delete crossings at a/d tangency', lambda d: d['rectangles'].__setitem__('d', [6, 10, -4, 4]))
    # Delete one occurrence of a real crossing in the independently reconstructed
    # graph. The d segments still meet there, but the a segments are merged.
    rects = {n: tuple(map(rational, r)) for n, r in data['rectangles'].items()}
    punctures = {int(n): tuple(map(rational, p)) for n, p in data['punctures'].items()}
    edges, crossings = geometry(rects, punctures)
    target = next(x for x in crossings if set(x['curves']) == {'a', 'd'})['point']
    incident = [(i, e) for i, e in enumerate(edges) if e[2] == 'a' and target in e[:2]]
    require(len(incident) == 2, 'crossing deletion control has wrong precondition')
    ends = [e[1] if e[0] == target else e[0] for _, e in incident]
    corrupted = [e for i, e in enumerate(edges) if i not in {j for j, _ in incident}]
    corrupted.append((ends[0], ends[1], 'a'))
    try:
        audit_edges(corrupted)
    except Reject as exc:
        controls.append({'mutation': 'delete one a/d crossing occurrence from reconstructed graph', 'status': 'REJECT', 'reason': str(exc)})
    else:
        raise Reject('negative control accepted: deleted reconstructed crossing')
    # Metamorphic positive controls ensure this is not a coordinate whitelist.
    transformed = copy.deepcopy(data)
    for n, r in data['rectangles'].items():
        x0, x1, y0, y1 = map(rational, r)
        transformed['rectangles'][n] = list(map(str, [x0*Q(3, 2)+Q(7, 3), x1*Q(3, 2)+Q(7, 3), y0*Q(5, 7)-Q(2, 9), y1*Q(5, 7)-Q(2, 9)]))
    for n, p in data['punctures'].items():
        x, y = map(rational, p)
        transformed['punctures'][n] = list(map(str, [x*Q(3, 2)+Q(7, 3), y*Q(5, 7)-Q(2, 9)]))
    check(transformed)
    controls.append({'mutation': 'rational affine translation and positive axis scaling', 'status': 'PASS'})
    perturbed = copy.deepcopy(data)
    perturbed['punctures']['2'] = ['21/4', '1/3']
    check(perturbed)
    controls.append({'mutation': 'move p2 within same overlap face', 'status': 'PASS'})
    return controls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--output', type=Path, help='write complete independently derived certificate')
    args = parser.parse_args()
    try:
        raw = args.input.read_bytes()
        data = json.loads(raw)
        result = check(data)
        result['input_sha256'] = hashlib.sha256(raw).hexdigest()
        if args.self_test:
            result['controls'] = self_test(data)
        if args.output:
            args.output.write_text(json.dumps(result, indent=2, default=str)+'\n')
        print(json.dumps({'status': result['status'], 'input_sha256': result['input_sha256'],
                          'full_VEF': [result['full_embedding'][k] for k in ('V', 'E', 'F')],
                          'penner_VEF': [result['penner_embedding'][k] for k in ('V', 'E', 'F')],
                          'controls': result.get('controls', [])}, indent=2))
    except (Reject, KeyError, TypeError, ValueError, OSError, ZeroDivisionError) as exc:
        print(json.dumps({'status': 'REJECT', 'reason': str(exc)}))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
