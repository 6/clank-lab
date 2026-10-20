"""Driver: certify the wedge lemma (W) fan by fan.

    python3 wrun.py list                 # fan identifiers
    python3 wrun.py run FAN [FAN ...]    # certify, one JSON line per fan on stdout
    python3 wrun.py all [-j 2]           # every fan -> results.jsonl

A fan is certified when its parameter domain is covered by parameter boxes
each of which passes Tree.pairs() and Tree.vertices() (wbnb.py).  Parameter
boxes are bisected adaptively (widest side); a box that still fails at the
minimal parameter width is retried at finer s-resolution, and if it still
fails the fan is reported FAILED with the undecided boxes (and a float
witness search, wfloat.py, is run separately).
"""
import json
import sys
import time
from flint import arb
import wgeom
from wgeom import float_upper, PI, Undecided, OutOfDomain, NotClosable, type_i, solve_alpha, TypeII, TypeIII, PairedPolar, paired_i_fixed, paired_i_rays, iv, S17, dot
from wbnb import Reduced, Tree, L2
from wconfigs import type_i_configs, PAIRED_UNBOUNDED, PAIRED_BOUNDED, PAIRED_NOT_CLOSABLE, TYPE_III, domain_summary
import wroots
DEGENERATE = {(3, 3, 4): '1 + 1 = 2', (3, 4, 6): '1 + 2 = 3', (3, 5, 10): '1 + (2 + 2cos 72) = 2 + 2cos 36'}

def fan_ids():
    ids = ['i:' + ','.join(map(str, c)) for c in type_i_configs()]
    ids += ['ii:%d' % q for q in range(3, 17)]
    ids += ['iii:%d,%d' % c for c in TYPE_III]
    ids += ['pi:m,' + ','.join(map(str, r)) for r in PAIRED_UNBOUNDED]
    for r, ms in PAIRED_BOUNDED.items():
        ids += ['pi:%d,%s' % (m, ','.join(map(str, r))) for m in ms]
    ids += ['pnc:m,' + ','.join(map(str, r)) for r in PAIRED_NOT_CLOSABLE]
    ids += ['pii:m']
    return ids

def build(fid):
    """Return (geometry callable with .pbox, adjacency info) or a status string."""
    kind, spec = fid.split(':')
    if kind == 'i':
        qs = tuple((int(t) for t in spec.split(',')))
        if qs in DEGENERATE:
            c = [4 * (PI / q).cos() ** 2 for q in qs]
            if not (c[0] + c[1] - c[2]).contains(0):
                raise AssertionError()
            return 'DEGENERATE (right triangle %s: the q=%d facet contains c)' % (DEGENERATE[qs], qs[2])
        F = type_i(qs)
        if F is None:
            return 'NOT CLOSABLE (f(alpha_min) < 0 certified)'
        k = len(qs)
        F.vpairs = [(i, (i + 1) % k) for i in range(k)]
        F.vnames = ['x%d' % (i + 1) for i in range(k)]
        return F
    if kind == 'ii':
        F = TypeII(int(spec))
        F.vnames = ['x', 'y', 'z1', 'z2']
        F.vpairs = [(i, j) for i in range(4) for j in range(i + 1, 4)]
        return F
    if kind == 'iii':
        q1, q2 = (int(t) for t in spec.split(','))
        roots = wroots.all_roots(q1, q2)
        if any((len(r[2]) != 1 for r in roots)):
            return 'ROOTS %s' % [len(r[2]) for r in roots]
        F = TypeIII(q1, q2, [(a, b, r[0]) for a, b, r in roots])
        F.vnames = ['x', 'y', 'z1', 'z2', 'w']
        F.vpairs = [(i, j) for i in range(5) for j in range(i + 1, 5)]
        return F
    if kind == 'pi':
        parts = spec.split(',')
        rest = tuple((int(t) for t in parts[1:]))
        k = len(rest) + 1
        if parts[0] == 'm':
            F = PairedPolar('i', rest)
        else:
            F = paired_i_fixed(rest, int(parts[0]))
            if F is None:
                return 'NOT CLOSABLE'
        F.vnames = ['x%d' % (i + 1) for i in range(k)]
        F.vpairs = [(i, (i + 1) % k) for i in range(1, k)]
        return F
    if kind == 'pnc':
        rest = tuple((int(t) for t in spec.split(',')[1:]))
        return paired_not_closable(rest)
    if kind == 'pii':
        F = PairedPolar('ii')
        F.vnames = ['x', 'y', 'z1', 'z2']
        F.vpairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]
        return F
    raise ValueError(fid)

def paired_not_closable(rest, nu=64):
    """(m, q2, q3) with (q2, q3) in (3,3), (3,4), (3,5): the closure function
    f(alpha) = 2 asin(cos u/sin a) + 2 asin(cos(pi/q2)/sin a) + 2 asin(cos(pi/q3)/sin a) - 2 pi
    is decreasing in alpha, so the configuration closes iff f(alpha_min) >= 0,
    sin(alpha_min) = cos u (the m-term is pi there).  Certify f(alpha_min) < 0
    for all u = pi/m in [0, pi/17] (u-boxes)."""
    U = float_upper(PI / 17)
    worst = None
    for i in range(nu):
        u = iv(U * i / nu, U * (i + 1) / nu)
        cu = u.cos()
        f = PI - 2 * PI
        for q in rest:
            f = f + 2 * ((PI / q).cos() / cu).asin()
        if not f < 0:
            return 'UNDECIDED'
        worst = f if worst is None else worst.union(f)
    return 'NOT CLOSABLE (f(alpha_min) in %s < 0 for all m >= 17)' % worst.str(4)

def width(P):
    return max((b - a for a, b in P))

def split(P):
    j = max(range(len(P)), key=lambda i: P[i][1] - P[i][0])
    a, b = P[j]
    m = (a + b) / 2
    return [P[:j] + [(a, m)] + P[j + 1:], P[:j] + [(m, b)] + P[j + 1:]]

def vertex_distances(F, G):
    """Upper bound of |x - x'| over the listed pairs of fan vertices."""
    xs = {name: x for name, x, al in G.verts}
    out = []
    for i, j in F.vpairs:
        a, b = (F.vnames[i], F.vnames[j])
        d2 = 2 - 2 * dot(xs[a], xs[b])
        out.append(d2)
    return out

def certify(F, minw0=2.0 ** (-10), minw_floor=2.0 ** (-10), pmin=2.0 ** (-14), crmax=None, drop=(), L2override=None, budget=30000000, time_budget=1800):
    """Cover F's parameter domain by certified boxes.
    A box is first bisected until the coefficient spread (Reduced.coefrad)
    is <= crmax.  Then s-boxes down to width minw0, minw0/2, ..., minw_floor
    are tried; if all fail the box is bisected (down to width pmin).  The
    fan is FAILED at the first box that fails at width pmin, or when the
    CPU time exceeds time_budget."""
    if crmax is None:
        crmax = 0.01 if len(F.pbox) == 1 else 0.02
    queue = [[tuple(t) for t in F.pbox]]
    stats = dict(boxes=0, outside=0, nodes=0, pairtests=0, retries=0, splits=0, finest_s=2.0)
    vmax = None
    failures = []
    certified = []
    t0 = time.process_time()
    while queue:
        if time.process_time() - t0 > time_budget:
            failures.append(dict(kind='time budget', P=queue[-1]))
            break
        P = queue.pop()
        try:
            G = F(P)
            red = Reduced(G, drop=drop)
        except OutOfDomain:
            stats['outside'] += 1
            continue
        except Undecided as e:
            if width(P) > pmin:
                queue += split(P)
                continue
            failures.append(dict(kind='geometry undecided: %s' % e, P=P))
            break
        if L2override is not None:
            red.E = 4 - L2override / (1 - G.kappa * G.kappa)
        if red.coefrad > crmax and width(P) > pmin:
            stats['splits'] += 1
            queue += split(P)
            continue
        minw = minw0
        while True:
            T = Tree(red, minw)
            bad = T.pairs(budget)
            badv = T.vertices(budget) if bad is None else None
            stats['nodes'] += T.nodes
            stats['pairtests'] += T.pairtests
            if bad is None and badv is None:
                break
            if minw > minw_floor:
                minw /= 2
                stats['retries'] += 1
                continue
            break
        if bad is None and badv is None:
            distances = vertex_distances(F, G)
            threshold = L2 if L2override is None else L2override
            if len(distances) != len(F.vpairs) or not all((d2 < threshold for d2 in distances)):
                if width(P) > pmin:
                    stats['splits'] += 1
                    queue += split(P)
                    continue
                failures.append(dict(P=P, kind='fan-vertex distance undecided'))
                break
            stats['boxes'] += 1
            stats['finest_s'] = min(stats['finest_s'], T.finest)
            certified.append((P, minw))
            for d2 in distances:
                vmax = d2 if vmax is None else vmax.max(d2)
            continue
        if width(P) > pmin:
            stats['splits'] += 1
            queue += split(P)
            continue
        if bad == 'budget' or badv == 'budget':
            failures.append(dict(P=P, kind='pair-test budget'))
        elif bad is not None:
            A, B = bad
            failures.append(dict(P=P, kind='pair', A=[A.lo, A.hi], B=[B.lo, B.hi]))
        else:
            A, name = badv
            failures.append(dict(P=P, kind='vertex ' + name, A=[A.lo, A.hi]))
        break
    cpu = time.process_time() - t0
    status = 'CERTIFIED' if not failures and (not queue) else 'FAILED'
    return dict(status=status, cpu=round(cpu, 1), remaining=len(queue), failures=failures[:3], vmax=None if vmax is None else float(vmax.sqrt().upper()), certified=certified, **stats)

def run(fid, **kw):
    t0 = time.process_time()
    try:
        F = build(fid)
    except NotClosable:
        return dict(fan=fid, status='NOT CLOSABLE (c_perp outside the cone)', cpu=0.0)
    except Exception as e:
        return dict(fan=fid, status='ERROR %r' % e, cpu=round(time.process_time() - t0, 1))
    if isinstance(F, str):
        return dict(fan=fid, status=F, cpu=round(time.process_time() - t0, 1))
    res = certify(F, **kw)
    res['fan'] = fid
    return res
if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'domain':
        print(json.dumps(domain_summary(), sort_keys=True))
    elif cmd == 'list':
        print('\n'.join(fan_ids()))
    elif cmd == 'run':
        for fid in sys.argv[2:]:
            print(json.dumps(run(fid)), flush=True)
    elif cmd == 'all':
        from multiprocessing import get_context
        j = int(sys.argv[sys.argv.index('-j') + 1]) if '-j' in sys.argv else 2
        out = sys.argv[sys.argv.index('-o') + 1] if '-o' in sys.argv else 'results.jsonl'
        ids = fan_ids()
        with get_context('spawn').Pool(j) as pool, open(out, 'w') as fh:
            for res in pool.imap_unordered(run, ids):
                fh.write(json.dumps(res) + '\n')
                fh.flush()
                print(res['fan'], res['status'], res.get('cpu'), flush=True)
