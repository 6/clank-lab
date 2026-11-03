#!/usr/bin/env python3
"""Independent reconstruction of graph, path witnesses and SAT encodings.

Reconstructs the mathematical inputs independently of the producer.
"""
from collections import Counter
import hashlib
from itertools import combinations, product
import json
from pathlib import Path


class Reject(Exception):
    pass


def require(ok, reason):
    if not ok:
        raise Reject(reason)


def load(path):
    return json.loads(Path(path).read_text())


def mask(vertices):
    return sum(1 << v for v in vertices)


def exact_graph(data):
    pairs = list(combinations(range(6), 2))
    edges = sorted((a, b + 6) for b, pair in enumerate(pairs) for a in pair)
    require(data.get('n') == 21, 'graph: order')
    require(data.get('A') == list(range(6)), 'graph: originals')
    require(data.get('B') == list(range(6, 21)), 'graph: subdivision labels')
    require(data.get('B_pairs') == [list(p) for p in pairs], 'graph: edge labels')
    require(data.get('edges') == [list(e) for e in edges], 'graph: exact adjacency')
    require(data.get('complement_clique') == list(range(6, 21)),
            'graph: complement clique labels')
    E = set(edges)
    require(all(tuple(p) not in E for p in combinations(range(6, 21), 2)),
            'graph: complement clique adjacency')
    return E, pairs


def witnesses(data, edges):
    require(len(data) == 775, 'path: witness count')
    triples = []
    for row in data:
        t, p = row['triple'], row['path']
        require(len(t) == 3 and t == sorted(set(t)) and all(0 <= v < 21 for v in t),
                'path: triple distinctness/range')
        require(len(p) == len(set(p)) and all(0 <= v < 21 for v in p),
                'path: vertex distinctness/range')
        require(set(t) <= set(p), 'path: triple containment')
        for i in range(len(p)):
            for j in range(i + 1, len(p)):
                adjacent = tuple(sorted((p[i], p[j]))) in edges
                require(adjacent == (j == i + 1), 'path: induced adjacency')
        triples.append(tuple(t))
    require(len(set(triples)) == 775, 'path: duplicate triple')
    return set(triples)


def relation(side, edges, triples):
    if side == 'H':
        return sorted(edges), sorted(triples)
    require(side == 'complement', 'instance: graph side')
    return [p for p in combinations(range(21), 2) if p not in edges], []


def catalogue(data, side, edges, pairs):
    stars = [[6 + j for j, pair in enumerate(pairs) if a in pair] for a in range(6)]
    if side == 'H':
        expected = stars + [list(p) for p in combinations(range(21), 2)
                            if p not in edges and not any(set(p) <= set(s) for s in stars)]
    else:
        require(side == 'complement', 'catalogue: graph side')
        expected = [[a, b + 6] for b, pair in enumerate(pairs) for a in pair]
    require(data == expected, 'catalogue: exact ordered classes')
    require(len(data) == (126 if side == 'H' else 30), 'catalogue: size')
    return expected


def dimacs(path):
    header, clauses, pending = None, [], []
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('c'):
            continue
        fields = line.split()
        if fields[0] == 'p':
            require(header is None and fields[1] == 'cnf' and len(fields) == 4,
                    'formula: header')
            header = (int(fields[2]), int(fields[3]))
            continue
        require(header is not None, 'formula: missing header')
        for tok in fields:
            lit = int(tok)
            if lit == 0:
                require(len(pending) == len(set(pending)), 'formula: repeated literal')
                clauses.append(tuple(sorted(pending)))
                pending = []
            else:
                require(abs(lit) <= header[0], 'formula: literal range')
                pending.append(lit)
    require(header is not None and not pending and len(clauses) == header[1],
            'formula: clause count/terminator')
    return header[0], Counter(clauses)


def counter_clauses(N, k):
    def s(i, j):
        return N + (i - 1) * (k + 1) + j
    clauses = [(-i, s(i, 1)) for i in range(1, N + 1)]
    clauses += [(-s(i - 1, j), s(i, j))
                for i in range(2, N + 1) for j in range(1, k + 2)]
    clauses += [(-i, -s(i - 1, j - 1), s(i, j))
                for i in range(2, N + 1) for j in range(2, k + 2)]
    clauses.append((-s(N, k + 1),))
    return clauses


def expected_formula(kind, classes, k, edges, triples, n=21):
    if kind == 'cover':
        N = len(classes)
        clauses = [tuple(i + 1 for i, C in enumerate(classes) if v in C)
                   for v in range(n)] + counter_clauses(N, k)
        return N * (k + 2), Counter(tuple(sorted(c)) for c in clauses)
    require(kind == 'completeness', 'formula: kind')
    clauses = [tuple(-(v + 1) for v in e) for e in edges + triples]
    clauses += [tuple(v + 1 for v in range(n) if v not in C) for C in classes]
    clauses.append(tuple(range(1, n + 1)))
    return n, Counter(tuple(sorted(c)) for c in clauses)


def expected_map(kind, classes, k, edges=None, triples=None, n=21):
    if kind == 'completeness':
        return {'catalogue': classes, 'n': n, 'x': list(range(1, n + 1)),
                'exclusions': [list(e) for e in edges + triples]}
    N = len(classes)
    return {'catalogue': classes, 'n': n, 'k': k, 'y': list(range(1, N + 1)),
            's': [[N + (i - 1) * (k + 1) + j for j in range(1, k + 2)]
                  for i in range(1, N + 1)]}


def model_data(path, nvars):
    # Normalized signed-literal JSON arrays. Adapter must check all source bits.
    data = load(path)
    require(isinstance(data, list) and all(type(x) is int for x in data),
            'model: signed integer list')
    require(len(data) == nvars and {abs(x) for x in data} == set(range(1, nvars + 1)),
            'model: total unique assignment')
    return {abs(x): x > 0 for x in data}


def satisfied(clauses, assignment):
    return all(any(assignment[abs(x)] == (x > 0) for x in c) for c in clauses)


def check_model(kind, classes, k, clauses, assignment, edges, triples, n=21):
    require(satisfied(clauses, assignment), 'model: unsatisfied clause')
    if kind == 'cover':
        selected = [C for i, C in enumerate(classes, 1) if assignment[i]]
        require(len(selected) <= k, 'model: too many classes')
        require(set().union(*(set(C) for C in selected)) == set(range(n)),
                'model: uncovered vertex')
        return {'selected_classes': selected, 'selected_count': len(selected)}
    S = {v for v in range(n) if assignment[v + 1]}
    require(S and all(not set(e) <= S for e in edges + triples),
            'model: not a nonempty R-set')
    require(all(not S <= set(C) for C in classes), 'model: set lies inside catalogue')
    return {'uncovered_set': sorted(S)}


def full_enumeration(classes, edges, triples, n=21):
    r"""Visit every subset; recurrence is direct forbidden-hyperedge semantics.

    R(M) = R(M\{least vertex}) AND no forbidden e containing that vertex
    has e\{vertex} contained in the remainder. No catalogue inference is used
    to compute R. Coverage is independently the union of catalogue downsets.
    """
    size = 1 << n
    allowed = bytearray(size)
    covered = bytearray(size)
    allowed[0] = 1
    incident = [[] for _ in range(n)]
    for edge in edges + triples:
        m = mask(edge)
        for v in edge:
            incident[v].append(m ^ (1 << v))
    for C in classes:
        cm = mask(C)
        sub = cm
        while True:
            covered[sub] = 1
            if sub == 0:
                break
            sub = (sub - 1) & cm
    valid = 1
    gaps = []
    for m in range(1, size):
        bit = m & -m
        prev = m ^ bit
        if allowed[prev] and not any(prev & e == e for e in incident[bit.bit_length() - 1]):
            allowed[m] = 1
            valid += 1
            if not covered[m]:
                gaps.append(m)
    return {'subsets_visited': size, 'R_sets': valid, 'gap_count': len(gaps),
            'first_gap': None if not gaps else [v for v in range(n) if gaps[0] >> v & 1]}, allowed


def gap_control(classes, allowed, edges, triples):
    # Fixed prospective omission: catalogue member zero, no adaptive choice.
    omitted, rest = classes[0], classes[1:]
    m = mask(omitted)
    require(allowed[m] and all(m & mask(C) != m for C in rest),
            'gap: planted omission not witnessed')
    nvars, clauses = expected_formula('completeness', rest, None, edges, triples)
    assignment = {v + 1: v in omitted for v in range(21)}
    result = check_model('completeness', rest, None, clauses, assignment, edges, triples)
    normalized = '\n'.join(' '.join(map(str, c)) + ' 0'
                           for c, count in sorted(clauses.items()) for _ in range(count)) + '\n'
    result.update({'deleted_index': 0, 'variables': nvars, 'clauses': sum(clauses.values()),
                   'clause_multiset_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
                   'model_literals': [v + 1 if v in omitted else -(v + 1) for v in range(21)]})
    return result


def small_controls():
    # Existential auxiliary assignments checked in full for N<=3, including k=0,
    # unreachable j>i states, k=N, empty selection, and all input assignments.
    counter_cases = auxiliary_assignments = 0
    for N in range(1, 4):
        for k in range(N + 1):
            cls = Counter(tuple(sorted(c)) for c in counter_clauses(N, k))
            naux = N * (k + 1)
            for y in product((False, True), repeat=N):
                assignment = {i + 1: b for i, b in enumerate(y)}
                exists = False
                for aux in product((False, True), repeat=naux):
                    assignment.update({N + i + 1: b for i, b in enumerate(aux)})
                    sat = satisfied(cls, assignment)
                    require(not sat or sum(y) <= k, 'control: counter unsound')
                    exists |= sat
                    auxiliary_assignments += 1
                require(exists == (sum(y) <= k), 'control: counter completeness')
                extension = dict(enumerate(y, 1))
                for i in range(1, N + 1):
                    for j in range(1, k + 2):
                        extension[N + (i - 1) * (k + 1) + j] = sum(y[:i]) >= j
                require(satisfied(cls, extension) == (sum(y) <= k),
                        'control: canonical prefix extension')
                counter_cases += 1
    # Tiny solved cover: all pairs on three vertices, chromatic-cover minimum 2.
    classes = [[0, 1], [0, 2], [1, 2]]
    cover_cases = colouring_cases = 0
    for k in range(4):
        _, clauses = expected_formula('cover', classes, k, [], [], n=3)
        any_cover = False
        for y in product((False, True), repeat=3):
            direct = (sum(y) <= k and
                      set().union(*(set(C) for C, b in zip(classes, y) if b)) == set(range(3)))
            a = dict(enumerate(y, 1))
            for i in range(1, 4):
                for j in range(1, k + 2):
                    a[3 + (i - 1) * (k + 1) + j] = sum(y[:i]) >= j
            require(satisfied(clauses, a) == direct, 'control: small cover semantics')
            any_cover |= direct
            cover_cases += 1
        require(any_cover == (k >= 2), 'control: small solved cover')
        # All total colourings with fibres of size <=2. Extend every nonempty
        # fibre to the first containing pair; deduplicate; check full formula.
        for f in product(range(k), repeat=3):
            fibres = [{v for v in range(3) if f[v] == c} for c in range(k)]
            if any(len(S) > 2 for S in fibres):
                continue
            selected = {next(i for i, C in enumerate(classes) if S <= set(C))
                        for S in fibres if S}
            require(len(selected) <= k, 'control: extension/dedup cardinality')
            a = {i + 1: i in selected for i in range(3)}
            for i in range(1, 4):
                for j in range(1, k + 2):
                    a[3 + (i - 1) * (k + 1) + j] = sum(t < i for t in selected) >= j
            require(satisfied(clauses, a), 'control: colouring extension')
            colouring_cases += 1
    return {'counter_inputs': counter_cases, 'auxiliary_assignments': auxiliary_assignments,
            'tiny_cover_selections': cover_cases, 'tiny_colourings': colouring_cases}


def public_controls(root, plan, classes, edges, triples, phase):
    """Audit the actual public deleted-class formula/model and tiny controls."""
    out = {}
    if phase in ('all', 'formulas', 'maps', 'models'):
        inst = plan['deleted_class_control']
        C = classes['H'][1:]
        n, actual = dimacs(root / inst['cnf'])
        expected_n, expected = expected_formula('completeness', C, None, edges, triples)
        if phase in ('all', 'formulas', 'models'):
            require(n == expected_n and actual == expected, 'formula: deleted-class clauses')
        if phase in ('all', 'maps'):
            require(load(root / inst['map']) == expected_map('completeness', C, None, edges, triples),
                    'map: deleted-class meaning')
        if phase in ('all', 'models'):
            out['deleted_class_model'] = check_model('completeness', C, None, actual,
                model_data(root / inst['model'], n), edges, triples)
    if phase in ('all', 'controls'):
        out['tiny_public_instances'] = []
        for k in (1, 2):
            inst = plan['tiny_controls'][str(k)]
            C = [[0, 1], [1, 2]]
            n, actual = dimacs(root / inst['cnf'])
            expected_n, expected = expected_formula('cover', C, k, [], [], n=3)
            require(n == expected_n and actual == expected, 'control: public tiny clauses')
            require(load(root / inst['map']) == expected_map('cover', C, k, n=3),
                    'control: public tiny map')
            sat_count = 0
            for bits in product((False, True), repeat=n):
                a = dict(enumerate(bits, 1))
                if satisfied(actual, a):
                    sat_count += 1
                    check_model('cover', C, k, actual, a, [], [], n=3)
            require((sat_count > 0) == (k == 2), 'control: public tiny SAT/UNSAT')
            row = {'bound': k, 'variables': n, 'clauses': sum(actual.values()),
                   'assignments_checked': 1 << n, 'satisfying_assignments': sat_count}
            if k == 2:
                row['model'] = check_model('cover', C, k, actual,
                    model_data(root / inst['model'], n), [], [], n=3)
            out['tiny_public_instances'].append(row)
    return out


def check(root):
    class Options:
        phase = "all"
    args = Options()
    plan = {'catalogues': {'H': 'data/h7.json', 'complement': 'data/complement14.json'},
     'deleted_class_control': {'cnf': 'data/omitted-h-catalogue.cnf',
                               'map': 'data/omitted-h-catalogue.json',
                               'model': 'data/omitted-h-catalogue-model.json'},
     'graph': 'data/graph.json',
     'instances': [{'bound': 7,
                    'cnf': 'data/h7.cnf',
                    'kind': 'cover',
                    'map': 'data/h7.json',
                    'name': 'h7',
                    'side': 'H'},
                   {'bound': 8,
                    'cnf': 'data/h8.cnf',
                    'kind': 'cover',
                    'map': 'data/h8.json',
                    'model': 'data/h8-model.json',
                    'name': 'h8',
                    'side': 'H'},
                   {'bound': 14,
                    'cnf': 'data/complement14.cnf',
                    'kind': 'cover',
                    'map': 'data/complement14.json',
                    'name': 'complement14',
                    'side': 'complement'},
                   {'bound': 15,
                    'cnf': 'data/complement15.cnf',
                    'kind': 'cover',
                    'map': 'data/complement15.json',
                    'model': 'data/complement15-model.json',
                    'name': 'complement15',
                    'side': 'complement'},
                   {'cnf': 'data/h-catalogue.cnf',
                    'kind': 'completeness',
                    'map': 'data/h-catalogue.json',
                    'name': 'h-catalogue',
                    'side': 'H'},
                   {'cnf': 'data/complement-catalogue.cnf',
                    'kind': 'completeness',
                    'map': 'data/complement-catalogue.json',
                    'name': 'complement-catalogue',
                    'side': 'complement'}],
     'paths': 'data/paths.json',
     'tiny_controls': {'1': {'cnf': 'data/tiny1.cnf', 'map': 'data/tiny1.json'},
                       '2': {'cnf': 'data/tiny2.cnf',
                             'map': 'data/tiny2.json',
                             'model': 'data/tiny2-model.json'}}}
    out = {'check': 'independent semantic reconstruction', 'phase': args.phase}
    E, pairs = exact_graph(load(root / plan['graph']))
    if args.phase == 'graph':
        return out
    T = witnesses(load(root / plan['paths']), E)
    out['path_witnesses'] = len(T)
    if args.phase == 'paths':
        return out
    classes = {side: catalogue(load(root / p)['catalogue'], side, E, pairs)
               for side, p in plan['catalogues'].items()}
    require(set(classes) == {'H', 'complement'}, 'catalogue: both sides required')
    if args.phase == 'catalogues':
        return out
    if args.phase in ('all', 'formulas', 'maps', 'models'):
        out['instances'] = []
        required = {('H', 'cover', 7), ('H', 'cover', 8),
                    ('complement', 'cover', 14), ('complement', 'cover', 15),
                    ('H', 'completeness', None), ('complement', 'completeness', None)}
        seen = set()
        for inst in plan['instances']:
            side, kind, k = inst['side'], inst['kind'], inst.get('bound')
            C = classes[side]
            seen.add((side, kind, k))
            edges, triples = relation(side, E, T)
            expected_n, expected = expected_formula(kind, C, k, edges, triples)
            n, actual = dimacs(root / inst['cnf'])
            if args.phase in ('all', 'formulas', 'models'):
                require(n == expected_n and actual == expected, 'formula: exact clause multiset')
            if args.phase in ('all', 'maps'):
                require(load(root / inst['map']) == expected_map(kind, C, k, edges, triples),
                        'map: variable meaning/order/boundary')
            row = {'side': side, 'kind': kind, 'bound': k,
                   'variables': n, 'clauses': sum(actual.values())}
            if args.phase in ('all', 'models'):
                positive = kind == 'cover' and (side, k) in [('H', 8), ('complement', 15)]
                require(not positive or 'model' in inst, 'model: positive control missing')
                if 'model' in inst:
                    row['model'] = check_model(kind, C, k, actual,
                                               model_data(root / inst['model'], n), edges, triples)
            out['instances'].append(row)
        require(seen == required and len(plan['instances']) == 6, 'instance: exact six instances')
    out['public_controls'] = public_controls(root, plan, classes, sorted(E), sorted(T), args.phase)
    if args.phase in ('all', 'enumeration'):
        out['enumeration'] = {}
        for side, C in classes.items():
            edges, triples = relation(side, E, T)
            result, allowed = full_enumeration(C, edges, triples)
            require(result['gap_count'] == 0, 'enumeration: uncovered R-set')
            result['planted_gap'] = gap_control(C, allowed, edges, triples)
            out['enumeration'][side] = result
    if args.phase in ('all', 'controls'):
        out['small_controls'] = small_controls()
    out['status'] = 'PASS'
    return out
