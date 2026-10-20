#!/usr/bin/env python3
"""Rebuild the Lean U3 report and compare its rows with independent S3.

Only the primary report's logical projection regenerates the Lean file. The
independent implementation uses different search/grouping and symmetry counts:
compare class/full cyclic signature, verdict, names, all exclusion pairs, ROOT
and FORCED, not implementation-specific search or symmetry multiplicities.
This is a standard-library checker; it imports neither search implementation.
"""
import argparse
from collections import Counter
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
SOURCE = BASE / 'data/primary-u3-p16.json.gz'
SIGNATURES = BASE / 'data/primary-u2-signatures-p16.json.gz'
LEAN = BASE / 'lean/Uniform5/CompositionU3ReportP16.lean'
SOURCE_SHA256 = '938851ddf8aed87c29a2cd897d8190ff29024cba923b11f2602a0d5893e7eca7'
SIGNATURES_SHA256 = '425c7d239a327c7eebbd72d2caf8129a14de26f6f9e65f7e667aeef38d93156d'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_bytes(path):
    raw = Path(path).read_bytes()
    return gzip.decompress(raw) if str(path).endswith('.gz') else raw


def read_json(path):
    return json.loads(read_bytes(path))


def signature_key(signature):
    """Unoriented cyclic words: facets at vertices, cells on outgoing edges."""
    def word_key(word):
        w = tuple(tuple(pair) for pair in word)
        require(bool(w), 'empty cycle word')
        reverse = tuple((w[-i % len(w)][0], w[(-i-1) % len(w)][1])
                        for i in range(len(w)))
        return min(seq[i:] + seq[:i] for seq in (w, reverse)
                   for i in range(len(w)))
    return tuple(sorted(signature['facets'])), tuple(sorted(map(word_key, signature['cycles'])))


def bind_signatures(signatures):
    """Check the ordered full keys against the independently pinned U2 source.

    The old U3 report cannot supply this binding: two figures in class 18
    have identical coarse metadata. Fresh U3 must consume this actual ordered
    signature list, whose full keys are checked here, not inferred from counts.
    """
    raw = read_bytes(SIGNATURES)
    require(hashlib.sha256(raw).hexdigest() == SIGNATURES_SHA256,
            'source signature digest differs')
    ordered = lambda rows: [(r['index'], [signature_key(v) for v in r['vfs']])
                            for r in rows]
    require(ordered(signatures) == ordered(json.loads(raw)),
            'ordered full signature binding differs')


def report_rows(report, signatures):
    """Bind the historical figure index to its full word signature."""
    bind_signatures(signatures)
    pins = {row['index']: row for row in signatures}
    require(len(pins) == len(signatures) == 563, 'signature class coverage')
    classes = report['classes']
    require(len(classes) == 563 and {c['index'] for c in classes} == set(pins),
            'primary class coverage')
    result = []
    for cls in classes:
        require(not cls['known_unmatched'], 'primary unmatched known name')
        seen = set()
        for fi, (figure, pin) in enumerate(zip(cls['vfs'], pins[cls['index']]['vfs'], strict=True)):
            require(sorted(figure['facets']) == sorted(pin['facets']) and
                    figure['n_cycles'] == len(pin['cycles']), 'primary signature order mismatch')
            key = signature_key(pin)
            require(key not in seen, 'duplicate primary signature')
            seen.add(key)
            require(len(figure['realisations']) == 1, 'primary encoding multiplicity changed')
            result.append((cls['index'], fi, 0, key, figure['realisations'][0]))
    require(len(result) == 629, 'primary row count')
    require(Counter(r[4]['verdict'] for r in result) == {'KNOWN': 628, 'REFUTED': 1},
            'primary verdict counts')
    require([i for i, r in enumerate(result) if r[4]['verdict'] == 'REFUTED'] == [12],
            'Lean row 12 is not the unique extra candidate')
    require(result[12][:3] == (18, 0, 0), 'extra candidate class/figure binding')
    require(result[12][4]['embedding'].get('A510001', [None])[0] == 'NO',
            'row 12 must exclude A510001 by NO, not a count mismatch')
    # The candidate-pair universe is the Cartesian product, in each class,
    # of its retained rows and its radius-admitted known construction names.
    # It is not inferred from the embedding entries being tested.
    known = report['known']
    require(len(known) == 890, 'known construction inventory size')
    by_class = {c['index']: set() for c in classes}
    for name, model in known.items():
        require(len(model['classes']) == 1 and model['classes'][0] in by_class,
                'known construction must enter exactly one retained class')
        by_class[model['classes'][0]].add(name)
    for cls in classes:
        require(len(cls['known_in_class']) == len(set(cls['known_in_class'])) and
                set(cls['known_in_class']) == by_class[cls['index']],
                'known radius-class inventories disagree')
    matches = Counter()
    pairs = set()
    for ci, fi, _, _, r in result:
        require(set(r['embedding']) == by_class[ci], 'incomplete candidate-pair universe')
        matched = [name for name, value in r['embedding'].items() if value[0] == 'MATCH']
        require(len(r['known_names']) == len(set(r['known_names'])) and
                set(matched) == set(r['known_names']), 'MATCH/name list disagreement')
        matches.update(matched)
        pairs.update((ci, fi, name) for name in by_class[ci])
    require(len(pairs) == 1152, 'candidate-pair universe size')
    require(matches == Counter({name: 1 for name in known}),
            'each of the 890 names must match exactly one row')
    return result


def logical_lines(rows):
    strings = lambda values: '[' + ', '.join(json.dumps(x, ensure_ascii=False) for x in values) + ']'
    boolean = lambda x: 'true' if x is True else 'false' if x is False else fail('not boolean')
    statuses = {'MATCH': 'match', 'NO': 'no', 'NO-COUNT': 'noCount', 'UNDECIDED': 'undecided'}
    lines = []
    for ci, fi, ri, _, r in rows:
        local = r['local_uniqueness']
        require(local['failures'] == [] and local['no_valid'] == [], 'nonempty local failure list')
        loc = ', '.join(str(local[k]) for k in ('neighbours', 'unique', 'valid_g', 'tested_g'))
        loc += ', ' + boolean(local['forced']) + ', [], []'
        emb = '[' + ', '.join('(' + json.dumps(name, ensure_ascii=False) + ', .' + statuses[value[0]] + ')'
                               for name, value in sorted(r['embedding'].items())) + ']'
        values = [str(ci), str(fi), str(ri), str(r['search_states']), str(r['facets']),
                  str(r['vf_points']), boolean(r['unique_root']), '⟨' + loc + '⟩',
                  strings(r['known_names']), emb, '.' + r['verdict'].lower()]
        lines.append('  ⟨' + ', '.join(values) + '⟩')
    return ',\n'.join(lines)


def fail(message):
    raise ValueError(message)


def generate(report, signatures, digest=SOURCE_SHA256):
    return ('import Uniform5.CompositionU3Report\n\n'
            '/-! Fixed logical projection of the committed P16 stage-three report.\n'
            f'Source SHA-256: {digest}.\n'
            'The finite counts below are proved by kernel reduction, not assumed. -/\n'
            'namespace Uniform5.Composition\n\n'
            'set_option maxRecDepth 10000\nset_option maxHeartbeats 800000\n\n'
            'noncomputable def u3ReportP16 : List U3ReportRow := [\n'
            + logical_lines(report_rows(report, signatures)) + '\n]\n' + FOOTER)


def compare_primary(reference, source_signatures, fresh, actual_input):
    """Compare fresh U3 with both the Lean projection and its ordered input."""
    bind_signatures(actual_input)
    inputs = {c['index']: c for c in actual_input}
    for cls in fresh['classes']:
        require(tuple(map(Fraction, cls['R'])) ==
                tuple(map(Fraction, inputs[cls['index']]['R'])),
                'fresh primary class interval differs from actual ordered input')
    require(generate(fresh, actual_input) == generate(reference, source_signatures),
            'fresh primary report logical projection differs')


def compare_independent(report, signatures, independent):
    expected = report_rows(report, signatures)
    own = {c['index']: c for c in independent}
    require(len(own) == len(independent) == 563, 'independent duplicate/missing classes')
    require(set(own) == {c['index'] for c in report['classes']}, 'independent class IDs differ')
    rows = {}
    extras = []
    for ci, cls in own.items():
        require(cls['status'] == 'COMPLETE', f'class {ci}: incomplete S3')
        require(cls['identification']['status'] == 'COMPLETE', f'class {ci}: incomplete identification')
        active = []
        for realization in cls['realisations']:
            # These 28 placements are rejected BEFORE the identification arrays
            # are constructed. No other early-refuted shape is silently skipped.
            if 'separation_witness' in realization:
                require(realization['status'] == 'REFUTED' and 'local_uniqueness' not in realization,
                        'invalid pre-identification separation rejection')
                extras.append((ci, realization))
            else:
                require('local_uniqueness' in realization, 'unaccounted early refutation')
                active.append(realization)
        checked = [q for q in cls['identification']['known'] if 'checks' in q]
        admitted = {name for name, model in report['known'].items() if ci in model['classes']}
        require({q['name'] for q in checked} == admitted,
                f'class {ci}: independent candidate-pair universe differs')
        require(all(len(q['checks']) == len(active) for q in checked), 'identification index coverage')
        for ai, realization in enumerate(active):
            key = (ci, signature_key(realization['signature']))
            require(key not in rows, 'duplicate active signature')
            embedding = {}
            for q in checked:
                require(q['status'] == 'IDENTIFIED-BY-ELIMINATION', 'unresolved known comparison')
                require(q['name'] not in embedding, 'duplicate known comparison')
                check = q['checks'][ai]
                if check['status'] == 'NO':
                    verdict = 'NO-COUNT' if check['reason'] == 'exact neighbour count' else 'NO'
                else:
                    require(q['possible'] == [ai] and q['name'] in realization.get('names', []),
                            'non-exclusion does not identify this row')
                    require(check['status'] in ('SOLE-REMAINING', 'POSSIBLE'), 'unexpected embedding status')
                    verdict = 'MATCH'
                embedding[q['name']] = verdict
            rows[key] = (realization, embedding, cls)
    require(len(rows) == 629 and len(extras) == 28, 'independent active/mirror counts')
    require(set(rows) == {(ci, key) for ci, _, _, key, _ in expected}, 'full signature coverage differs')
    pair_counts = Counter()
    for row_index, (ci, fi, _, key, reference) in enumerate(expected):
        realization, embedding, cls = rows[(ci, key)]
        where = f'Lean row {row_index} (class {ci}, figure {fi})'
        require(realization['status'] == reference['verdict'], where + ': verdict differs')
        require(sorted(realization.get('names', [])) == sorted(reference['known_names']), where + ': names differ')
        require((realization['radius']['status'] == 'UNIQUE') == reference['unique_root'] is True,
                where + ': ROOT differs')
        require((realization['local_uniqueness']['status'] == 'FORCED') == reference['local_uniqueness']['forced'] is True,
                where + ': forced flag differs')
        require(len(realization['signature']['facets']) == reference['facets'], where + ': facets differ')
        require(len(realization['local_uniqueness']['neighbours']) == reference['vf_points'], where + ': neighbour count differs')
        require(embedding == {name: value[0] for name, value in reference['embedding'].items()},
                where + ': NO/NO-COUNT/MATCH pairs differ')
        pair_counts.update(embedding.values())
        if row_index == 12:
            lo, hi = map(Fraction, cls['R'])
            require(lo < 1 < hi and realization['development']['status'] == 'REFUTED',
                    'row 12 is not the developed R=1 extra candidate')
            require(realization['radius']['R'] == cls['R'], 'extra candidate ROOT interval differs')
    require(pair_counts == {'MATCH': 890, 'NO-COUNT': 230, 'NO': 32}, 'embedding totals differ')
    require(Counter(name for r, _, _ in rows.values() for name in r.get('names', [])) ==
            Counter({name: 1 for name in report['known']}),
            'independent names do not match exactly once')
    # Every extra orientation must belong to a retained signature, not conceal a
    # new signature. The outcome audit separately verifies all 28 cut witnesses.
    for ci, realization in extras:
        main, _, _ = rows[(ci, signature_key(realization['signature']))]
        require(main['status'] == 'KNOWN', 'extra mirror has no known retained counterpart')
    return {'rows': len(rows), 'classes': len(own), 'extra_mirror_placements': len(extras),
            'embedding_pairs': dict(pair_counts), 'extra_candidate_lean_row': 12}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=SOURCE)
    parser.add_argument('--signatures', type=Path,
                        help='actual ordered input vfs.json, required with --primary-report')
    parser.add_argument('--lean', type=Path, default=LEAN)
    parser.add_argument('--write', type=Path, help='write regenerated Lean to a separate path')
    parser.add_argument('--primary-report', type=Path, help='fresh primary report to compare with the Lean projection')
    parser.add_argument('--independent', type=Path, help='fresh independent S3 JSONL to compare row by row')
    args = parser.parse_args()
    source = read_bytes(args.source)
    require(hashlib.sha256(source).hexdigest() == SOURCE_SHA256, 'source report digest differs from Lean header')
    report, signatures = json.loads(source), read_json(SIGNATURES)
    regenerated = generate(report, signatures)
    require(args.lean.read_text() == regenerated, 'Lean report is not the exact regenerated projection')
    if args.write:
        require(args.write.resolve() != args.lean.resolve(), 'write output must be separate from checked Lean file')
        args.write.write_text(regenerated)
    print('PASS Lean report: 629 rows regenerated byte-for-byte from source 938851dd')
    if args.primary_report:
        require(args.signatures is not None, '--primary-report requires its actual ordered --signatures input')
        compare_primary(report, signatures, read_json(args.primary_report), read_json(args.signatures))
        print('PASS fresh primary report: every Lean logical field agrees')
    elif args.signatures:
        bind_signatures(read_json(args.signatures))
    if args.independent:
        independent = [json.loads(line) for line in read_bytes(args.independent).splitlines() if line.strip()]
        print('PASS independent S3 report bridge:', json.dumps(compare_independent(report, signatures, independent), sort_keys=True))


# Fixed proof declarations: these depend only on the generated finite rows.
FOOTER = """
theorem u3ReportP16_length : u3ReportP16.length = 629 := by decide

theorem u3ReportP16_search_states :
    (u3ReportP16.map U3ReportRow.search_states).sum = 633 := by decide

theorem u3ReportP16_known_count :
    (u3ReportP16.filter fun r => r.verdict == .known).length = 628 := by decide

theorem u3ReportP16_refuted_count :
    (u3ReportP16.filter fun r => r.verdict == .refuted).length = 1 := by decide

theorem u3ReportP16_no_open :
    (u3ReportP16.filter fun r => r.verdict == .open).length = 0 := by decide

theorem u3ReportP16_all_roots : u3ReportP16.all (·.unique_root) = true := by decide

theorem u3ReportP16_all_forced :
    u3ReportP16.all (·.local_uniqueness.forced) = true := by decide

theorem u3ReportP16_known_names :
    (u3ReportP16.map fun r => r.known_names.length).sum = 890 := by decide

theorem u3ReportP16_no_count_eliminations :
    (u3ReportP16.map fun r =>
      (r.embedding.filter fun e => e.2 == .noCount).length).sum = 230 := by decide

theorem u3ReportP16_no_eliminations :
    (u3ReportP16.map fun r =>
      (r.embedding.filter fun e => e.2 == .no).length).sum = 32 := by decide

theorem u3ReportP16_signature_indices_nodup :
    (u3ReportP16.map U3ReportRow.signatureIndex).Nodup := by
  have hc : (u3ReportP16.map fun r => 100 * r.classIndex + r.figureIndex).Chain'
      (fun a b => a < b) := by decide
  have hn : (u3ReportP16.map fun r => 100 * r.classIndex + r.figureIndex).Nodup :=
    (List.chain'_iff_pairwise.mp hc).imp (fun h => Nat.ne_of_lt h)
  have hm : ((u3ReportP16.map U3ReportRow.signatureIndex).map
      (fun p => 100 * p.1 + p.2)).Nodup := by
    simpa only [List.map_map, Function.comp_def, U3ReportRow.signatureIndex] using hn
  exact List.Nodup.of_map _ hm

theorem u3ReportP16_mem_forced {r : U3ReportRow} (hr : r ∈ u3ReportP16) :
    r.local_uniqueness.forced = true :=
  List.all_eq_true.mp u3ReportP16_all_forced r hr

theorem u3ReportP16_mem_unique_root {r : U3ReportRow} (hr : r ∈ u3ReportP16) :
    r.unique_root = true :=
  List.all_eq_true.mp u3ReportP16_all_roots r hr

theorem u3ReportP16_mem_verdict {r : U3ReportRow} (hr : r ∈ u3ReportP16) :
    r.verdict = .known ∨ r.verdict = .refuted := by
  have hall : u3ReportP16.all (fun s => s.verdict == .known || s.verdict == .refuted) =
      true := by decide
  simpa using List.all_eq_true.mp hall r hr

end Uniform5.Composition
"""

if __name__ == "__main__":
    main()
