"""Semantic corruptions must be rejected by both independent snub checkers."""
import copy
import json
from pathlib import Path
import time
from snub_check import check as primary
from snub_check_rational import check as independent

HERE = Path(__file__).resolve().parent


def run():
    base = json.loads((HERE/'snub_certificate.json').read_text())
    controls = []
    def put(name, fn):
        bad = copy.deepcopy(base)
        fn(bad)
        controls.append((name, bad))
    put('source digest', lambda b: b['sources'].__setitem__('geom.py', '0'*64))
    put('deleted hull facet', lambda b: b['models']['B3']['faces'].pop())
    put('duplicate hull facet', lambda b: b['models']['H3']['faces'].append(b['models']['H3']['faces'][0]))
    put('wrong exact generator index', lambda b: b['models']['B3']['permutations'][0].__setitem__(0, 0))
    put('wrong group construction word', lambda b: b['models']['H3']['parents'].__setitem__(1, [0, 1]))
    put('wrong unit-edge seed', lambda b: b['models']['H3']['seeds'].__setitem__(0, 0))
    def nonplanar(b):
        faces = b['models']['H3']['faces']
        f = next(f for f in faces if len(f) == 5)
        f[0] = next(i for i in range(60) if i not in f)
    put('nonplanar pentagon', nonplanar)
    put('collapsed triangle', lambda b: b['models']['B3']['faces'][0].__setitem__(1, b['models']['B3']['faces'][0][0]))
    put('wrong root box', lambda b: b['models']['B3']['root_box'].__setitem__(0, ['0', '1/1000']))
    rows = []
    for name, bad in controls:
        row = {'corruption': name}
        for label, check in [('primary', primary), ('independent', independent)]:
            start = time.monotonic()
            try:
                check(bad)
            except (AssertionError, ZeroDivisionError, ValueError, IndexError, KeyError) as e:
                row[label] = {'rejected': True, 'reason': str(e), 'seconds': round(time.monotonic()-start, 6)}
            else:
                raise AssertionError(f'{label} accepted {name}')
        rows.append(row)
    return rows


if __name__ == '__main__':
    rows = run()
    print(json.dumps({'outcome': 'CERTIFIED', 'corruptions_rejected_by_both': len(rows), 'controls': rows}, sort_keys=True))
