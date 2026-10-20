"""Print the verdict digest of a result file (no timings): per class, vertex
figure and realisation the verdict, the identified names, the kind of every
embedding test, radius uniqueness, forcing; then the summary counts that do
not depend on timing.

usage: python digest.py result_pP.json"""
import json
import sys

r = json.load(open(sys.argv[1]))
for c in r['classes']:
    for k, v in enumerate(c['vfs']):
        for j, x in enumerate(v.get('realisations', [])):
            emb = ' '.join('%s:%s' % (n, e[0]) for n, e in sorted(x['embedding'].items()))
            print(c['index'], k, j, x['verdict'], ','.join(x['known_names']) or '-',
                  'root=%s' % x['unique_root'], 'forced=%s' % x['local_uniqueness']['forced'],
                  'states=%d' % x['search_states'], emb)
        if 'error' in v:
            print(c['index'], k, 'ERROR', v['error'])
s = r['summary']
# Historical results reported zero uncertainty in RESULT.md but predate these
# explicit counters. New replay acceptance separately requires both keys.
s.setdefault('search_undecided', 0)
s.setdefault('development_undecided', 0)
s.setdefault('model_guard_undecided', 0)
for key in sorted(s):
    if key.startswith('cpu') or key.startswith('wall') or key == 'template_certificates':
        continue
    print('summary', key, json.dumps(s[key],sort_keys=True))
for n, k in sorted(r['known'].items()):
    if 'outside_library' in k:
        print('outside_library', n, ','.join(k['outside_library']))
    elif 'neighbours' in k:
        nb = k['neighbours']
        print('neighbours', n, nb['upper'], nb['exact_from_construction'], nb['exact'])
