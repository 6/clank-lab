"""Replay the independent generator and verify its frozen JSON and controls."""
from receipt_policy import compare_receipt, read_receipt, parse_receipt
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import tempfile
from export import export_library
from library_compare import compare,corruptions
from parabolic import config_label


def check_incidences(data):
    counts = Counter()
    for record in data['records']:
        inc = record['incidences']
        cells,polygons = inc['cells'],inc['polygons']
        if 'neighbor_roots' in inc:
            n = len(inc['neighbor_roots'])
        elif 'neighbor_vectors' in inc:
            n = len(inc['neighbor_vectors'])
        else:
            n = inc['neighbor_count']
        if not (n-len(polygons)+len(cells) == 2):
            raise AssertionError(('VF Euler',record['name']))
        words = Counter()
        edge_sets = set()
        for polygon in polygons:
            edge = frozenset(polygon['neighbors'])
            if not (len(edge) == 2 and edge not in edge_sets):
                raise AssertionError()
            if not (all(0 <= i < n for i in edge)):
                raise AssertionError()
            edge_sets.add(edge)
            a,b = polygon['cells']
            if not (a != b and 0 <= a < len(cells) and 0 <= b < len(cells)):
                raise AssertionError()
            if not ([i for i,C in enumerate(cells) if edge <= set(C['neighbors'])] == sorted((a,b))):
                raise AssertionError()
            A,B = sorted((cells[a]['label'],cells[b]['label']))
            words[polygon['p'],A,B] += 1
        expected = Counter({(w['p'],w['A'],w['B']):w['multiplicity'] for w in record['words']})
        if not (words == expected):
            raise AssertionError(('words/multiplicities',record['name']))
        for i,C in enumerate(cells):
            verts = set(C['neighbors'])
            boundary = [p for p in polygons if i in p['cells']]
            if not (len(boundary) == len(verts)):
                raise AssertionError()
            if not (all(sum(v in p['neighbors'] for p in boundary) == 2 for v in verts)):
                raise AssertionError()
            reached = {min(verts)}
            while True:
                new = reached.union(*(set(p['neighbors']) for p in boundary if reached.intersection(p['neighbors'])))
                if new == reached:
                    break
                reached = new
            if not (reached == verts):
                raise AssertionError()
            if not (config_label(p['p'] for p in boundary) == C['label']):
                raise AssertionError()
        counts['types'] += 1
        counts['words'] += len(words)
        counts['occurrences'] += sum(words.values())
    if not (dict(counts) == data['counts']):
        raise AssertionError()
    if not (dict(counts) == {'types':181,'words':558,'occurrences':1277}):
        raise AssertionError()
    return {'status':'CERTIFIED','independent_incidence_counts':dict(counts)}


def own_controls(data):
    tests = []
    bad = copy.deepcopy(data)
    bad['records'][0]['words'][0]['multiplicity'] -= 1
    tests.append(('wrong multiplicity',bad))
    bad = copy.deepcopy(data)
    bad['records'][0]['incidences']['polygons'].pop()
    tests.append(('missing occurrence',bad))
    bad = copy.deepcopy(data)
    bad['records'][0]['incidences']['cells'][0]['label'] = 'cube'
    tests.append(('wrong local cell label',bad))
    bad = copy.deepcopy(data)
    polygon = bad['records'][0]['incidences']['polygons'][0]
    polygon['cells'] = [polygon['cells'][0]]*2
    tests.append(('one cell used twice',bad))
    for name,bad in tests:
        try:
            check_incidences(bad)
        except (AssertionError,KeyError,ValueError):
            pass
        else:
            raise AssertionError(('accepted corruption',name))
    return {'status':'CERTIFIED','incidence_corruptions_rejected':len(tests),
            'labels':[name for name,_ in tests]}


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument('--reference',type=Path,
                        default=here.parent/'input_link/evidence/s1_facets_p16.json')
    args = parser.parse_args()
    frozen_path = here/'library.json'
    frozen = json.loads(frozen_path.read_text())
    receipts=[]
    def emit(value):
        receipts.append(value)
        print(json.dumps(value, sort_keys=True))
    emit(check_incidences(frozen))
    with tempfile.TemporaryDirectory() as scratch:
        regenerated = Path(scratch)/'library.json'
        actual = export_library(regenerated,frozen['precision_bits'],announce=False)
        compare_receipt(actual, frozen, 'library.json')
    emit({'status':'CERTIFIED','frozen_library_sha256':hashlib.sha256(frozen_path.read_bytes()).hexdigest(),
          'generation':'parsed scientific fields agree'})
    emit(own_controls(frozen))
    reference = json.loads(args.reference.read_text())
    emit(compare(frozen,reference))
    emit(corruptions(frozen,reference))

    expected=[parse_receipt(line) for line in (here/'library_evidence.jsonl').read_text().splitlines()]
    if not (len(receipts)==len(expected)):
        raise AssertionError('library receipt inventory differs')
    for actual, saved in zip(receipts, expected):
        # Generation wording is descriptive metadata; every control/count,
        # status and authenticated library identity remains compared.
        actual={k:v for k,v in actual.items() if k!='generation'}
        saved={k:v for k,v in saved.items() if k!='generation'}
        compare_receipt(actual, saved, 'library.json')


if __name__ == '__main__':
    main()
