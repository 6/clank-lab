"""Seven semantic certificate corruptions, independent of either checker."""
import copy
KINDS = ["coordinate", "active-label", "input", "cover", "edge", "distance", "endpoint"]

def mutate(cert, kind):
    bad = copy.deepcopy(cert)
    if kind == 'coordinate':
        bad['vertices'][0][1] = '987654321'
    elif kind == 'active-label':
        bad['labels'][0].pop()
    elif kind == 'input':
        bad['matrix'][0][0] = '987654321'
    elif kind == 'edge':
        bad['edges'].pop()
    elif kind == 'distance':
        bad['potential'][bad['endpoints'][1]] += 1
    elif kind == 'endpoint':
        bad['endpoints'].reverse()
    elif kind == 'cover':
        remove = next(i for i in range(len(bad['labels'])) if i not in set(bad['endpoint_path']))
        for key in ['labels', 'vertices', 'potential']:
            bad[key].pop(remove)
        def shift(i):
            return i - (i > remove)
        bad['edges'] = [[shift(u), shift(v)] for u, v in bad['edges'] if remove not in [u, v]]
        bad['endpoints'] = list(map(shift, bad['endpoints']))
        bad['endpoint_path'] = list(map(shift, bad['endpoint_path']))
    return bad

