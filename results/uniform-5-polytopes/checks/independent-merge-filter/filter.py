#!/usr/bin/env python3
"""Independent FILTER, derived from paper/main.tex's closure-filter paragraph.

No stage-1 proof or congruence proof is performed here. All numerical inputs
are frozen certified intervals, parsed as Fractions; expected classes are read
only after the actual fixed point has been computed.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys
import time


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def load_json(path):
    with (gzip.open(path, 'rt') if path.suffix == '.gz' else path.open()) as stream:
        return json.load(stream)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def interval(pair):
    require(isinstance(pair, (list, tuple)) and len(pair) == 2, 'interval needs two endpoints')
    require(all(isinstance(s, str) for s in pair), 'endpoints must be exact rational strings')
    try:
        lo, hi = map(Fraction, pair)
    except (ValueError, ZeroDivisionError) as exc:
        raise Invalid('non-finite or malformed endpoint') from exc
    require(0 < lo <= hi, 'interval must be positive and ordered')
    return lo, hi


def canonical(p, facets, cells):
    """C_i follows K_i; reversal swaps preceding/following cell at each K."""
    require(type(p) is int and p >= 3, 'invalid polygon size')
    require(len(facets) == len(cells) and len(facets) >= 3, 'invalid cycle length')
    require(all(isinstance(s, str) and s for s in (*facets, *cells)), 'invalid cycle label')
    n = len(facets)
    forward = tuple(zip(facets, cells))
    backward = tuple((facets[-i % n], cells[(-i - 1) % n]) for i in range(n))
    return p, min(w[i:] + w[:i] for w in (forward, backward) for i in range(n))


def side(p, a, b):
    return p, min(a, b), max(a, b)


def cycle_sides(key):
    p, word = key
    return frozenset((facet, *side(p, word[i - 1][1], cell))
                     for i, (facet, cell) in enumerate(word))


def cycle_json(key):
    p, word = key
    return {'p': p, 'facets': [x[0] for x in word], 'cells': [x[1] for x in word]}


@dataclass(frozen=True)
class Library:
    requirements: dict
    aliases: dict

    def selected(self, bound, convention='parameter'):
        """Historical controls cap family parameters; strict caps all polygons."""
        if convention == 'strict':
            return frozenset(k for k, words in self.requirements.items()
                             if max(w[0] for w in words) <= bound)
        require(convention == 'parameter', 'unknown cutoff convention')
        selected = set()
        for k in self.requirements:
            match = re.fullmatch(r'duoprism-(\d+)-(\d+)|antiprism-prism-(\d+)', k)
            if match is None or max(int(x) for x in match.groups() if x) <= bound:
                selected.add(k)
        return frozenset(selected)


def read_library(records):
    require(isinstance(records, list) and records, 'empty facet library')
    requirements, aliases = {}, {}
    for record in records:
        name = record['name']
        require(name not in requirements, 'duplicate facet')
        words = []
        for w in record['words']:
            require(type(w['p']) is int and w['p'] >= 3, 'invalid orbit polygon')
            require(all(isinstance(w[x], str) and w[x] for x in ('A', 'B')), 'invalid orbit cells')
            words.append(side(w['p'], w['A'], w['B']))
        require(words, 'facet has no polygon words')
        requirements[name] = frozenset(words)  # Orbit multiplicity does not enter FILTER.
        for alias in [name, *record['aliases']]:
            require(alias not in aliases, 'ambiguous facet alias')
            aliases[alias] = name
    return Library(requirements, aliases)


@dataclass(frozen=True)
class Cycle:
    key: tuple
    status: str
    roots: tuple


def validate_cycle(cycle, library):
    for facet, p, a, b in cycle_sides(cycle.key):
        require(facet in library.requirements, 'unknown facet in cycle')
        require((p, a, b) in library.requirements[facet], 'cycle side absent from facet library')
    require(len(cycle.key[1]) <= 6, 'cycle too long for frozen stage-1 contract')
    require(cycle.status in ('ROOT', 'FLAT', 'DEGENERATE', 'NO_ROOT'), 'unknown stage-1 status')
    require(len(cycle.roots) == (1 if cycle.status in ('ROOT', 'DEGENERATE') else 0),
            'stage-1 single-root contract violated')


def independent_cycles(records, library):
    cycles = {}
    for record in records:
        word = record['word']
        require(all(isinstance(w, list) and len(w) == 2 for w in word), 'invalid paired word')
        key = canonical(record['p'], [w[0] for w in word], [w[1] for w in word])
        roots = (interval(record['R']),) if 'R' in record else ()
        cycle = Cycle(key, record['status'], roots)
        validate_cycle(cycle, library)
        require(key not in cycles, 'duplicate cycle modulo rotations/reversal')
        cycles[key] = cycle
    return cycles


def reference_cycles(records, library):
    """Read check_u1 JSON as data only, including fail-closed degenerate export."""
    cycles = {}
    for r in records:
        key = canonical(r['p'], r['facets'], r['cells'])
        require(type(r['flat']) is bool, 'malformed flat flag')
        require(r['status'] in ('ROOT', 'NOROOT'), 'invalid reference status')
        if r['flat']:
            require(not r['degenerate'], 'flat and degenerate flags conflict')
            status, roots = 'FLAT', ()
        elif r['degenerate']:
            require(r['status'] == 'ROOT' and r['degenerate'] == [0] and len(r['R']) == 1,
                    'degenerate cycle must have exactly one root')
            status, roots = 'DEGENERATE', tuple(interval(x) for x in r['R'])
        elif r['status'] == 'NOROOT':
            require(not r['R'], 'NOROOT carries roots')
            status, roots = 'NO_ROOT', ()
        else:
            status, roots = 'ROOT', tuple(interval(x) for x in r['R'])
        cycle = Cycle(key, status, roots)
        validate_cycle(cycle, library)
        require(key not in cycles, 'duplicate reference cycle')
        cycles[key] = cycle
    return cycles


def select_cycles(cycles, selected):
    return {k: c for k, c in cycles.items() if all(f in selected for f, _ in k[1])}


def components(entries):
    """Exact closed-interval components. Running high endpoint handles bridges."""
    groups = []
    for lo, hi, key in sorted(entries):
        if groups and lo <= groups[-1][1]:
            groups[-1][1] = max(groups[-1][1], hi)
            groups[-1][2].add(key)
        else:
            groups.append([lo, hi, {key}])
    return groups


def close_class(keys, requirements):
    """Synchronous descending iteration; each removal has an absence witness."""
    active = set(keys)
    sides = {k: cycle_sides(k) for k in active}
    facets = {k: frozenset(f for f, _ in k[1]) for k in active}
    rounds = []
    while active:
        supported = set().union(*(sides[k] for k in active))
        used_facets = set().union(*(facets[k] for k in active))
        bad = {}
        for facet in sorted(used_facets):
            missing = sorted(w for w in requirements[facet] if (facet, *w) not in supported)
            if missing:
                bad[facet] = missing[0]
        removed = {k for k in active if facets[k].intersection(bad)}
        if not removed:
            break
        # A witness facet and missing orbit for every removed cycle, grouped by facet.
        witnesses = {}
        for key in sorted(removed):
            f = min(facets[key].intersection(bad))
            witnesses.setdefault((f, bad[f]), []).append(key)
        rounds.append(witnesses)
        active.difference_update(removed)
    return active, rounds


def audit_deletions(original, survivors, rounds, requirements):
    """Check a removal certificate without making the producer's deletion choices."""
    active = set(original)
    for witnesses in rounds:
        require(witnesses, 'empty removal round')
        supported = {s for k in active for s in cycle_sides(k)}
        removed = set()
        for (facet, word), keys in witnesses.items():
            require(word in requirements[facet] and (facet, *word) not in supported,
                    'invalid missing-orbit witness')
            for k in keys:
                require(k in active and k not in removed, 'duplicate or inactive removal')
                require(facet in {f for f, _ in k[1]}, 'witness facet not in removed cycle')
                removed.add(k)
        active -= removed
    require(active == set(survivors), 'certificate survivor mismatch')
    supported = {s for k in active for s in cycle_sides(k)}
    for k in active:
        for facet, _ in k[1]:
            require(all((facet, *w) in supported for w in requirements[facet]),
                    'survivor set is not a fixed point')
    return True


def calculate(cycles, library):
    roots = [(*r, k) for k, c in cycles.items() if c.status == 'ROOT' for r in c.roots]
    groups = components(roots)
    index = {key: i for i, key in enumerate(sorted(cycles))}
    survivors, audits, round_counts = [], [], Counter()
    for i, (lo, hi, keys) in enumerate(groups):
        alive, rounds = close_class(keys, library.requirements)
        audit_deletions(keys, alive, rounds, library.requirements)
        round_counts[len(rounds)] += 1
        if alive:
            alive_roots = [r for key in alive for r in cycles[key].roots
                           if r[0] <= hi and lo <= r[1]]
            survivors.append({'class_index': i, 'R': [str(lo), str(hi)],
                              'R_alive': [str(min(r[0] for r in alive_roots)),
                                          str(max(r[1] for r in alive_roots))],
                              'cycles': [cycle_json(k) for k in sorted(alive)]})
        if rounds:
            audits.append({'class_index': i, 'initial_cycle_ids': sorted(index[k] for k in keys),
                           'rounds': [[{'facet': f, 'missing': list(w),
                                        'cycle_ids': [index[k] for k in removed]}
                                       for (f, w), removed in sorted(ws.items())] for ws in rounds],
                           'surviving_cycle_ids': sorted(index[k] for k in alive)})
    return {'counts': {'cycles': len(cycles), 'statuses': dict(sorted(Counter(c.status for c in cycles.values()).items())),
                       'omega_intervals': len(roots), 'radius_classes': len(groups),
                       'surviving_classes': len(survivors),
                       'surviving_cycles': sum(len(c['cycles']) for c in survivors),
                       'removal_round_histogram': dict(sorted(round_counts.items()))},
            'classes': survivors, 'deletion_certificates': audits}


def class_sets(records, library):
    """A set of complete cycle sets; check duplicates before set construction."""
    result = set()
    for record in records:
        keys = []
        for c in record['cycles']:
            if isinstance(c, list):
                p, facets, cells = c
            else:
                p, facets, cells = c['p'], c['facets'], c['cells']
            facets = [library.aliases[f] for f in facets]
            keys.append(canonical(p, facets, cells))
        require(keys and len(set(keys)) == len(keys), 'empty class or duplicate cycle')
        frozen = frozenset(keys)
        require(frozen not in result, 'duplicate class')
        result.add(frozen)
    return result


def serialize_sets(sets):
    return [[cycle_json(k) for k in sorted(group)] for group in sorted(sorted(g) for g in sets)]


def compare_classes(actual, expected, library):
    a, b = class_sets(actual, library), class_sets(expected, library)
    return {'equal_complete_cycle_sets': a == b,
            'actual_classes': len(a), 'expected_classes': len(b),
            'missing_classes': serialize_sets(b - a), 'extra_classes': serialize_sets(a - b),
            'actual_set_sha256': digest(serialize_sets(a)), 'expected_set_sha256': digest(serialize_sets(b))}


def compare_cycles(actual, expected):
    missing, extra = expected.keys() - actual.keys(), actual.keys() - expected.keys()
    statuses = [k for k in actual.keys() & expected.keys() if actual[k].status != expected[k].status]
    overlap_failures = [k for k in actual.keys() & expected.keys()
                        if actual[k].status in ('ROOT', 'DEGENERATE') and expected[k].roots
                        and not all(max(a[0], b[0]) <= min(a[1], b[1])
                                    for a, b in zip(actual[k].roots, expected[k].roots))]
    # Intervals need only overlap; neither narrower certificate is required to contain the other.
    return {'equal_complete_cycle_sets': not missing and not extra,
            'equal_status_by_cycle': not statuses, 'root_intervals_overlap_exactly': not overlap_failures,
            'cycles': len(actual), 'missing': [cycle_json(k) for k in sorted(missing)],
            'extra': [cycle_json(k) for k in sorted(extra)],
            'status_disagreements': [cycle_json(k) for k in sorted(statuses)],
            'interval_disagreements': [cycle_json(k) for k in sorted(overlap_failures)]}


def pin_sources(base, manifest):
    observed = {}
    for name, expected in manifest['sources'].items():
        require(name not in {
            'independent-s1-b2/evidence/comparison.json',
            'independent-s1-b2/evidence/stage1-result.json',
            'independent-s1-b2/evidence/stage1-verification.json',
        }, 'output receipt is not a byte-pinned input: ' + name)
        require(Path(name).suffix.lower() not in ('.md', '.tex', '.pdf', '.rst'),
                'mutable prose is not a runtime input: ' + name)
        raw = (base / name).read_bytes()
        observed[name] = hashlib.sha256(raw).hexdigest()
        require(observed[name] == expected, 'source hash mismatch: ' + name)
    return observed


def check_library_data(library, reference_words, alias_records):
    words = {r['name']: frozenset(side(w[0], w[1], w[2]) for w in r['orbits']) for r in reference_words}
    require(words == library.requirements, 'facet word sets disagree with frozen source')
    aliases = {a: r['name'] for r in alias_records for a in [r['name'], *r['aliases']]}
    require(aliases == library.aliases, 'facet alias data disagree')


def replay(base, out):
    started = time.perf_counter()
    here = Path(__file__).resolve().parent
    manifest = load_json(here / 'sources.json')
    observed = pin_sources(base, manifest)
    library = read_library(load_json(base / 'independent-s1-b2/library.json')['records'])
    check_library_data(library, load_json(base / 'input_link/evidence/s1_facets_p16.json'),
                       load_json(base / 'check_u1/inputs/u1_facets_p16.json'))
    cycles = independent_cycles(load_json(base / 'independent-s1-b2/evidence/cycles.json.gz'), library)
    summary = {'schema': 'independent-filter-results-v1', 'scope': 'FILTER only, conditional on frozen stage-1 data',
               'source_sha256': observed, 'bounds': {}, 'control_set_disagreements': []}
    out.mkdir(parents=True, exist_ok=True)
    for p in (6, 10, 16):
        begin = time.perf_counter()
        selected = library.selected(p)
        actual = select_cycles(cycles, selected)
        result = calculate(actual, library)
        # Do not load expected class data before calculation.
        expected = load_json(base / f'independent-s23/inputs/u2_classes_p{p}.json.gz')
        comparisons = {'u2': compare_classes(result['classes'], expected, library)}
        if p in (10, 16):
            suffix = '.json.gz' if p == 16 else '.json'
            recorded = reference_cycles(load_json(base / f'check_u1/cycles_p{p}{suffix}'), library)
            comparisons['check_u1_complete_cycles'] = compare_cycles(actual, recorded)
            comparisons['check_u1_classes'] = compare_classes(
                result['classes'], load_json(base / f'check_u1/classes_p{p}.json'), library)
        else:
            comparisons['check_u1_classes'] = {'available': False,
                                             'reason': 'P=6 check_u1 class file not in frozen bundle'}
            # P=6 subset compared with the COMPLETE reference P=16 cycle data, not a count.
            recorded = reference_cycles(load_json(base / 'check_u1/cycles_p16.json.gz'), library)
            comparisons['check_u1_complete_cycles_restricted_to_p6_library'] = compare_cycles(
                actual, select_cycles(recorded, selected))
        result.update({'bound': p, 'cutoff': 'family parameters only; fixed families retained',
                       'selected_facets': sorted(selected), 'comparisons': comparisons})
        for name, comp in comparisons.items():
            if any(comp.get(k) is False for k in ('equal_complete_cycle_sets', 'equal_status_by_cycle',
                                                'root_intervals_overlap_exactly')):
                summary['control_set_disagreements'].append({'bound': p, 'comparison': name})
        write_json(out / f'classes_p{p}.json.gz', result)
        summary['bounds'][str(p)] = {'facets': len(selected), **result['counts'],
                                     'class_set_sha256': comparisons['u2']['actual_set_sha256'],
                                     'comparisons': comparisons,
                                     'elapsed_seconds': time.perf_counter() - begin}
    # This is a separate literal reading of L_P, not an alteration of the historical control.
    strict_facets = library.selected(6, 'strict')
    strict = calculate(select_cycles(cycles, strict_facets), library)
    expected6 = load_json(base / 'independent-s23/inputs/u2_classes_p6.json.gz')
    strict_comparison = compare_classes(strict['classes'], expected6, library)
    strict.update({'bound': 6, 'cutoff': 'all facet polygon sizes at most 6, literal paper L_P',
                   'selected_facets': sorted(strict_facets), 'comparison_to_frozen_p6': strict_comparison})
    write_json(out / 'strict_p6.json.gz', strict)
    summary['literal_paper_p6'] = {'facets': len(strict_facets), **strict['counts'],
                                   'matches_frozen_expected_sets': strict_comparison['equal_complete_cycle_sets'],
                                   'reason': 'Frozen P=6 controls retain fixed families with 8/10-gons; literal L_6 excludes them.'}
    summary['paper_statement_disagreements'] = [{'bound': 6, 'issue': 'literal L_P versus historical control cutoff',
                                                 'literal_facets': len(strict_facets),
                                                 'literal_survivors': strict['counts']['surviving_classes'],
                                                 'historical_facets': len(library.selected(6)),
                                                 'historical_survivors': summary['bounds']['6']['surviving_classes']}]
    summary['limitations'] = ['Stage-1 roots/statuses and library words are trusted hash-pinned certified data; not re-proved here.',
                              'P=6 check_u1 classes absent; u2 classes and complete restricted check_u1 P=16 cycles compared.',
                              'The paper definition of L_6 disagrees with its historical P=6 control convention.']
    summary['status'] = 'PASS_WITH_DOCUMENTED_P6_LIBRARY_CONVENTION' if not summary['control_set_disagreements'] else 'DISAGREEMENT'
    summary['elapsed_seconds'] = time.perf_counter() - started
    write_json(out / 'results.json', summary)
    return summary


def write_json(path, value):
    raw = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    path.write_bytes(gzip.compress(raw, mtime=0) if path.suffix == '.gz' else raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parent.parent,
                        help='targets/uniform-5-polytopes directory containing frozen input directories')
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parent / 'results')
    args = parser.parse_args()
    try:
        summary = replay(args.base, args.out)
    except (Invalid, OSError, KeyError, TypeError) as exc:
        print('FILTER FAILED: ' + str(exc), file=sys.stderr)
        return 1
    print(json.dumps({'status': summary['status'], 'elapsed_seconds': summary['elapsed_seconds'],
                      'survivors': {p: r['surviving_classes'] for p, r in summary['bounds'].items()},
                      'literal_paper_p6_survivors': summary['literal_paper_p6']['surviving_classes']}))
    return bool(summary['control_set_disagreements'])


if __name__ == '__main__':
    sys.exit(main())
