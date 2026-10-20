"""corruption (b): the vertex figure with one chiral facet mirrored must not
keep its verdict."""
import json
import sys
a = json.load(open(sys.argv[1]))
b = json.load(open(sys.argv[2]))
ci, vi, ft = sys.argv[3].split(':')
ci, vi = (int(ci), int(vi))

def get(r):
    c = next((c for c in r['classes'] if c['index'] == ci))
    return [(x['verdict'], x['known_names'], x.get('development', {}).get('stuck_reasons')) for x in c['vfs'][vi]['realisations']]
va, vb = (get(a), get(b))
print('corruption (b): class %d vertex figure %d, one %s mirrored' % (ci, vi, ft))
print('  original :', va)
print('  corrupted:', vb)
if not [x[0] for x in va] != [x[0] for x in vb]:
    raise AssertionError('verdict unchanged')
print('corruption (b): verdict changed')
