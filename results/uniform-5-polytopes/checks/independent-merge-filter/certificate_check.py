#!/usr/bin/env python3
"""Standalone FILTER witness replay: stdlib only, never imports filter.py.

Stage-1 root/status proofs and facet facts are inherited frozen inputs.
Hash pins protect provenance; this program does not recertify stage 1.
"""
import argparse
from collections import Counter
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path


class Invalid(ValueError):
    pass


def require(test, message):
    if not test:
        raise Invalid(message)


def read(path):
    with (gzip.open(path, 'rt') if path.suffix == '.gz' else path.open()) as stream:
        return json.load(stream)


def rational_interval(pair):
    require(isinstance(pair, (list, tuple)) and len(pair) == 2 and all(isinstance(x, str) for x in pair),
            'expected two rational endpoint strings')
    try:
        low, high = Fraction(pair[0]), Fraction(pair[1])
    except (ValueError, ZeroDivisionError) as exc:
        raise Invalid('invalid finite rational interval') from exc
    require(0 < low <= high, 'nonpositive or unordered interval')
    return low, high


def cycle_key(p, facets, cells):
    require(type(p) is int and p >= 3 and len(facets) == len(cells) and 3 <= len(facets) <= 6,
            'malformed cycle')
    require(all(isinstance(x, str) and x for x in list(facets) + list(cells)), 'malformed cycle label')
    n = len(facets)
    candidates = []
    for start in range(n):
        for direction in (1, -1):
            oriented = []
            for step in range(n):
                vertex = (start + step * direction) % n
                edge = vertex if direction == 1 else (vertex - 1) % n
                oriented.append((facets[vertex], cells[edge]))
            candidates.append(tuple(oriented))
    return p, min(candidates)


def cycle_sides(key):
    polygon, boundary = key
    previous_cell = boundary[-1][1]
    sides = set()
    for facet, following_cell in boundary:
        a, b = sorted([previous_cell, following_cell])
        sides.add((facet, polygon, a, b))
        previous_cell = following_cell
    return sides


def selected_facets(requirements, bound, convention):
    chosen = set()
    for name, words in requirements.items():
        if convention == 'strict':
            permitted = all(word[0] <= bound for word in words)
        else:
            require(convention == 'parameter', 'unknown library convention')
            if name.startswith('duoprism-'):
                parameters = list(map(int, name.split('-')[1:]))
            elif name.startswith('antiprism-prism-'):
                parameters = [int(name.split('-')[-1])]
            else:
                parameters = []
            permitted = all(number <= bound for number in parameters)
        if permitted:
            chosen.add(name)
    return chosen


def inputs(base):
    here = Path(__file__).resolve().parent
    sources = read(here / 'sources.json')['sources']
    for filename, expected in sources.items():
        require(filename not in {
            'independent-s1-b2/evidence/comparison.json',
            'independent-s1-b2/evidence/stage1-result.json',
            'independent-s1-b2/evidence/stage1-verification.json',
        }, 'output receipt is not a byte-pinned input: ' + filename)
        require(Path(filename).suffix.lower() not in ('.md', '.tex', '.pdf', '.rst'),
                'mutable prose is not a runtime input: ' + filename)
        require(hashlib.sha256((base / filename).read_bytes()).hexdigest() == expected,
                'source hash mismatch: ' + filename)
    requirements, aliases = {}, {}
    for record in read(base / 'independent-s1-b2/library.json')['records']:
        name = record['name']
        require(name not in requirements, 'duplicate facet type')
        words = set()
        for w in record['words']:
            require(type(w['p']) is int and w['p'] >= 3, 'invalid facet polygon size')
            a, b = sorted([w['A'], w['B']])
            words.add((w['p'], a, b))
        require(words, 'empty facet word set')
        requirements[name] = words
        for alias in [name] + record['aliases']:
            require(alias not in aliases, 'duplicate facet alias')
            aliases[alias] = name
    cycles = {}
    for raw in read(base / 'independent-s1-b2/evidence/cycles.json.gz'):
        require(all(isinstance(w, list) and len(w) == 2 for w in raw['word']), 'invalid input word')
        key = cycle_key(raw['p'], [w[0] for w in raw['word']], [w[1] for w in raw['word']])
        require(key not in cycles, 'duplicate complete input cycle')
        require(raw['status'] in ('ROOT', 'FLAT', 'DEGENERATE', 'NO_ROOT'), 'invalid stage-1 status')
        if raw['status'] in ('ROOT', 'DEGENERATE'):
            require('R' in raw, 'missing root interval')
            root = rational_interval(raw['R'])
        else:
            require('R' not in raw, 'nonroot status carries interval')
            root = None
        for facet, p, a, b in cycle_sides(key):
            require(facet in requirements and (p, a, b) in requirements[facet], 'input side absent from library')
        cycles[key] = raw['status'], root
    return requirements, aliases, cycles


def interval_groups(keys, cycles):
    """Endpoint-event sweep; starts precede ends at equal coordinates (closed)."""
    events = []
    for identifier, key in enumerate(keys):
        status, root = cycles[key]
        if status == 'ROOT':
            low, high = root
            events += [(low, 0, identifier), (high, 1, identifier)]
    active_count = 0
    groups = []
    members = None
    for coordinate, event, identifier in sorted(events):
        if event == 0:
            if active_count == 0:
                low = coordinate
                members = set()
            active_count += 1
            members.add(identifier)
        else:
            active_count -= 1
            require(active_count >= 0, 'invalid interval event order')
            if active_count == 0:
                groups.append((low, coordinate, members))
    require(active_count == 0, 'unclosed interval component')
    return groups


def ids(values, limit):
    require(isinstance(values, list) and all(type(i) is int and 0 <= i < limit for i in values),
            'invalid certificate cycle id')
    require(len(set(values)) == len(values), 'duplicate cycle id')
    return set(values)


def output_key(raw, aliases):
    if isinstance(raw, list):
        p, facets, cells = raw
    else:
        p, facets, cells = raw['p'], raw['facets'], raw['cells']
    require(all(name in aliases for name in facets), 'unknown output facet')
    return cycle_key(p, [aliases[name] for name in facets], cells)


def class_sets(records, aliases):
    classes = set()
    for record in records:
        keys = [output_key(c, aliases) for c in record['cycles']]
        require(keys and len(set(keys)) == len(keys), 'empty class or duplicated cycle')
        group = frozenset(keys)
        require(group not in classes, 'duplicated class')
        classes.add(group)
    return classes


def check_records(record, complete, requirements, aliases, convention):
    """Replay absence witnesses and prove final closure, without finding removals."""
    chosen = selected_facets(requirements, record['bound'], convention)
    require(record['selected_facets'] == sorted(chosen), 'incorrect selected facet list')
    cycles = {key: value for key, value in complete.items() if all(f in chosen for f, _ in key[1])}
    keys = sorted(cycles)
    identifier = {key: i for i, key in enumerate(keys)}
    groups = interval_groups(keys, cycles)
    sides = [cycle_sides(key) for key in keys]
    facets = [{f for f, _ in key[1]} for key in keys]
    outputs, certificates = {}, {}
    for destination, source in ((outputs, record['classes']), (certificates, record['deletion_certificates'])):
        for item in source:
            index = item['class_index']
            require(type(index) is int and 0 <= index < len(groups) and index not in destination,
                    'duplicate or invalid class index')
            destination[index] = item
    checked_rounds = checked_removals = surviving_cycles = 0
    round_histogram = Counter()
    for index, (low, high, original) in enumerate(groups):
        current = set(original)
        cert = certificates.get(index)
        if cert:
            require(ids(cert['initial_cycle_ids'], len(keys)) == original, 'wrong original class membership')
            require(cert['rounds'], 'empty stored deletion certificate')
            rounds = cert['rounds']
        else:
            rounds = []
        round_histogram[len(rounds)] += 1
        for witnesses in rounds:
            require(witnesses, 'empty deletion round')
            available = {word for i in current for word in sides[i]}
            removed = set()
            for witness in witnesses:
                facet, word = witness['facet'], tuple(witness['missing'])
                require(facet in requirements and word in requirements[facet], 'fabricated missing orbit')
                require((facet,) + word not in available, 'witness orbit is still supported')
                batch = ids(witness['cycle_ids'], len(keys))
                require(batch and batch <= current and not (batch & removed), 'invalid or repeated removal')
                require(all(facet in facets[i] for i in batch), 'witness facet absent from removed cycle')
                removed.update(batch)
            current.difference_update(removed)
            checked_rounds += 1
            checked_removals += len(removed)
        item = outputs.get(index)
        if item:
            require(rational_interval(item['R']) == (low, high), 'wrong original class interval')
            survivor_keys = [output_key(raw, aliases) for raw in item['cycles']]
            require(survivor_keys and len(set(survivor_keys)) == len(survivor_keys), 'empty class or duplicate survivor')
            require(all(key in identifier for key in survivor_keys), 'unknown surviving cycle')
            claimed = {identifier[key] for key in survivor_keys}
        else:
            claimed = set()
        require(current == claimed, 'saved survivor set differs from witnessed removals')
        if cert:
            require(ids(cert['surviving_cycle_ids'], len(keys)) == current, 'wrong surviving certificate ids')
        available = {word for i in current for word in sides[i]}
        for facet in {facet for i in current for facet in facets[i]}:
            require(all((facet,) + word in available for word in requirements[facet]),
                    'remaining cycles are not closed')
        if current:
            root_intervals = [cycles[keys[i]][1] for i in current]
            hull = min(x[0] for x in root_intervals), max(x[1] for x in root_intervals)
            require(rational_interval(item['R_alive']) == hull, 'wrong surviving class hull')
        surviving_cycles += len(current)
    calculated = {'cycles': len(cycles), 'statuses': dict(Counter(value[0] for value in cycles.values())),
                  'omega_intervals': sum(value[0] == 'ROOT' for value in cycles.values()),
                  'radius_classes': len(groups), 'surviving_classes': len(outputs),
                  'surviving_cycles': surviving_cycles,
                  'removal_round_histogram': {str(k): v for k, v in round_histogram.items()}}
    require(record['counts'] == calculated, 'stored count metadata differs from certificate')
    return {'bound': record['bound'], 'convention': convention, 'checked_classes': len(groups),
            'checked_rounds': checked_rounds, 'checked_removals': checked_removals,
            'surviving_classes': len(outputs)}


def check_all(base, output):
    requirements, aliases, complete = inputs(base)
    reports = []
    for name, convention in [('classes_p6.json.gz', 'parameter'), ('classes_p10.json.gz', 'parameter'),
                             ('classes_p16.json.gz', 'parameter'), ('strict_p6.json.gz', 'strict')]:
        record = read(output / name)
        expected_bound = 6 if convention == 'strict' else int(name.split('_p')[1].split('.')[0])
        require(type(record['bound']) is int and record['bound'] == expected_bound, 'wrong bound for certificate file')
        report = check_records(record, complete, requirements, aliases, convention)
        actual_sets = class_sets(record['classes'], aliases)
        expected = read(base / f"independent-s23/inputs/u2_classes_p{record['bound']}.json.gz")
        equal = actual_sets == class_sets(expected, aliases)
        if convention == 'parameter':
            require(equal, 'complete class sets disagree with u2 expected data')
        report['matches_historical_u2_class_sets'] = equal
        if record['bound'] in (10, 16):
            reference = read(base / f"check_u1/classes_p{record['bound']}.json")
            require(actual_sets == class_sets(reference, aliases), 'complete class sets disagree with check_u1')
            report['matches_check_u1_class_sets'] = True
        reports.append(report)
    return reports


def mutations(record, complete):
    import copy
    for label in ['supported orbit falsely claimed missing', 'removed surviving cycle', 'omitted deletion round']:
        damaged = copy.deepcopy(record)
        if label == 'supported orbit falsely claimed missing':
            witness = damaged['deletion_certificates'][0]['rounds'][0][0]
            removed_key = sorted(complete)[witness['cycle_ids'][0]]
            supported_word = next(word[1:] for word in cycle_sides(removed_key) if word[0] == witness['facet'])
            witness['missing'] = list(supported_word)
        elif label == 'removed surviving cycle':
            next(c for c in damaged['classes'] if len(c['cycles']) > 1)['cycles'].pop()
        else:
            damaged['deletion_certificates'][0]['rounds'].pop()
        yield label, damaged


def corruptions(base, output):
    requirements, aliases, complete = inputs(base)
    record = read(output / 'classes_p16.json.gz')
    rejected = []
    for label, damaged in mutations(record, complete):
        try:
            check_records(damaged, complete, requirements, aliases, 'parameter')
        except Invalid:
            rejected.append(label)
        else:
            raise Invalid('certificate corruption accepted: ' + label)
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    parser.add_argument('--base', type=Path, default=here.parent)
    parser.add_argument('--out', type=Path, default=here / 'results')
    args = parser.parse_args()
    print(json.dumps({'certificates': check_all(args.base, args.out),
                      'corruptions_rejected': corruptions(args.base, args.out)}, sort_keys=True))


if __name__ == '__main__':
    main()
