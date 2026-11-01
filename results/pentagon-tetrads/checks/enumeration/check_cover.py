"""Cover check for the closure stage (n = 5).

1. The closure cases (data/closure-cases-n5.json) are exactly the
   length-feasible members of the angle survivors (data/angle-survivors-n5.jsonl),
   decided with the exact rational LP.
2. The relabeling groups recomputed from the cases equal
   data/closure-groups-n5.json, and partition the cases.
3. Every group has a member closed either by a certificate in certs/ (whose
   case data equals the case's) or by an exact proof script
   (group of case 8: checks/enumeration/group4.py).
4. Every case has an explicit relabeling onto its group's closing member,
   and these equal data/closure-relabelings-n5.json.
Prints a summary; exit code 1 on any failure.
"""
import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from lengths import MapData, build_problem  # noqa: E402
from exact_linear import length_margin  # noqa: E402
from groups import key, transform, relabelings  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(HERE))
PROOF_SCRIPTS = {8: 'checks/enumeration/group4.py'}


def main():
    ok = True
    map_lines = [json.loads(l) for l in open(os.path.join(ROOT, 'data/maps-h0.jsonl'))]
    maps = [MapData(m) for m in map_lines]
    surv = [json.loads(l) for l in open(os.path.join(ROOT, 'data/angle-survivors-n5.jsonl'))]
    cases = json.load(open(os.path.join(ROOT, 'data/closure-cases-n5.json')))
    ident = lambda r: (r['map'], r['placement'], json.dumps(r['labs']), json.dumps(r['pattern']))
    feasible = []
    arows_of = {}
    rec_of = {ident(r): r for r in surv}
    for r in surv:
        cs, bends, labs, segs, lrows, arows = build_problem(maps[r['map']], r, 5)
        if length_margin(5, len(segs), lrows) > 0:
            feasible.append(ident(r))
            arows_of[ident(r)] = arows
    if sorted(feasible) != sorted(ident(c) for c in cases):
        print('FAIL: closure cases differ from the length-feasible angle survivors')
        ok = False
    print('length-feasible survivors:', len(feasible), 'closure cases:', len(cases))
    groups = {}
    for k, c in enumerate(cases):
        groups.setdefault(json.dumps(key(c, arows_of[ident(c)])), []).append(k)
    recomputed = sorted(groups.values())
    stored = json.load(open(os.path.join(ROOT, 'data/closure-groups-n5.json')))
    if recomputed != stored:
        print('FAIL: groups differ from data/closure-groups-n5.json')
        ok = False
    flat = sorted(k for g in stored for k in g)
    if flat != list(range(len(cases))):
        print('FAIL: groups do not partition the cases')
        ok = False
    certified = {}
    for f in sorted(glob.glob(os.path.join(ROOT, 'data/certificates/*.jsonl'))):
        for l in open(f):
            d = json.loads(l)
            c = cases[d['case']]
            r = rec_of[ident(c)]
            same = (d['map'] == map_lines[c['map']] and d['placement']['cs'] == r['cs']
                    and d['placement']['bends'] == r['bends'] and d['labs'] == c['labs'] and d['pattern'] == c['pattern'] and d['rays'] == c['rays']
                    and d['free'] == c['free'] and d['sol'] == c['sol'])
            if not same:
                print('FAIL: certificate case data differ for case', d['case'])
                ok = False
            certified[d['case']] = os.path.basename(f)
    for k, s in PROOF_SCRIPTS.items():
        certified.setdefault(k, s)
    maps_out = {}
    for i, g in enumerate(stored):
        closers = [k for k in g if k in certified]
        status = 'closed by case %d (%s)' % (closers[0], certified[closers[0]]) if closers else 'OPEN'
        if not closers:
            ok = False
        else:
            # explicit relabeling from every member onto the closing member
            k0 = closers[0]
            target = transform(cases[k0], arows_of[ident(cases[k0])], list(range(5)), list(range(5)))
            for k in g:
                found = None
                for t, (vm, em) in enumerate(relabelings(5)):
                    if transform(cases[k], arows_of[ident(cases[k])], vm, em) == target:
                        found = (t, vm, em)
                        break
                if found is None:
                    print('FAIL: no relabeling maps case', k, 'onto case', k0)
                    ok = False
                else:
                    maps_out[k] = dict(onto=k0, corner_map=found[1], side_map=found[2])
        print('group %2d (%d cases): %s' % (i, len(g), status))
    stored_maps = json.load(open(os.path.join(ROOT, 'data/closure-relabelings-n5.json')))
    if {str(k): v for k, v in maps_out.items()} != stored_maps:
        print('FAIL: relabelings differ from data/closure-relabelings-n5.json')
        ok = False
    print('explicit relabelings found for', len(maps_out), 'cases')
    print('COVER CHECK', 'PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
