"""Diagnostic cross-check of B2; check_b2/b2check.py supplies the proof.

The endpoint offset in config_radius, ordinary-float cutoffs and fixed
Omega lookup window are heuristic. This producer is not an exhaustive
certified exclusion, even when its output agrees with the proof checker.

P has an n-gon F, n >= 17.  Cells at F are P_n or A_n, facets at F are {n}x{q} or A_n x {}, and the
angle sum leaves three cycle types around F:
 (i)  {n}x{q_1}, ..., {n}x{q_k} (k = 3..5, sum(1 - 2/q_i) < 2): all cell rays have d = 1/2 and the
      closure is the vertex closure of the configuration c = (q_1..q_k), so
      R^2 = r_n^2 + R_c^2 with R_c the configuration radius (cert_poly3), independent of n;
 (ii) A_n x {}, A_n x {}, {n}x{q};
 (iii) A_n x {}, A_n x {}, {n}x{q1}, {n}x{q2}, (q1, q2) in {(3,3), (3,4), (3,5)}.
Omega = the certified roots of all stage-1 cycles of the p_max = 16 library (every cycle whose
facets have all parameters <= 16), flat and degenerate cycles excluded.  If P's radius is not in
Omega, every cycle at a vertex contains a facet with a polygon of >= 17 sides (B3).  This script
reports diagnostic (n, cycle) hits against Omega (candidates for B4), using
an approximate finite cutoff. Exhaustive exclusion is check_b2's obligation.
usage: caseb_coinc.py -> caseb_coinc.json
"""
import json, math, itertools, sys
from fractions import Fraction
from flint import arb, ctx
from mpmath import mpf
import cert_poly3 as cp
from cert_stage1 import certify_cycle
from export_omega import project_intervals

ctx.prec = 200
PI = arb.pi()


def omega(input_dir='.', pmax=16):
    from pathlib import Path
    def load(name):
        return json.loads((Path(input_dir) / name).read_text())
    rows = project_intervals(load(f'cert_stage1_5d_p{pmax}.json'),
                             load(f'exact_flat_p{pmax}.json'),
                             load(f'exact_boundary_p{pmax}.json'), pmax)
    iv = [(arb(lo), arb(hi), i) for lo, hi, i in rows]
    iv.sort(key=lambda t: float(t[0].mid()))
    return iv


def config_radius(conf):
    """R_c of a vertex configuration (circumradius of the would-be polyhedron), or None if the
    vertex closure has no solution.  F(rho) = sum 2 asin(cos(pi/q)/rho) - 2 pi is decreasing on
    (max cos(pi/q), 1]; a root exists iff F > 0 just above the left end and F(1) < 0."""
    cs = [(PI / q).cos() for q in conf]
    lo = max(c.upper() for c in cs)
    F = lambda r: sum((2 * (c / r).asin() for c in cs), arb(0)) - 2 * PI
    f1 = F(arb(1))
    if not (f1 < 0):
        return None                       # angle sum >= 2 pi (or undecided: treated as no polyhedron? no:)
    a = arb(lo) + arb(10) ** -40
    fa = F(a)
    if not (fa > 0):
        if fa < 0:
            return None
        raise RuntimeError('undecided configuration %s' % (conf,))
    return cp.data(list(conf))['R']


def configs(qmax):
    """Cyclic configurations (up to rotation/reflection) with k = 3..5 and angle sum < 2 pi."""
    out = set()
    for k in (3, 4, 5):
        def rec(seq, tot):
            if len(seq) == k:
                c = tuple(seq)
                rots = [c[i:] + c[:i] for i in range(k)]
                rots += [tuple(reversed(r)) for r in rots]
                out.add(min(rots))
                return
            for q in range(3, qmax + 1):
                t = tot + Fraction(q - 2, q)        # angle / pi
                if t + Fraction(1, 3) * (k - len(seq) - 1) >= 2:
                    break
                rec(seq + [q], t)
        rec([], Fraction(0))
    return sorted(out)


def main():
    Om = omega()
    Rmax = max(float(t[1].mid()) for t in Om)
    N = 17
    while 1 / (2 * math.sin(math.pi / N)) <= Rmax:
        N += 1
    qmax = N
    print('Omega', len(Om), 'max', Rmax, '-> n <=', N - 1, file=sys.stderr, flush=True)
    import bisect
    keys = [float(t[0].mid()) for t in Om]

    def hits(Rb):
        x = float(Rb.mid())
        j = bisect.bisect_left(keys, x - 1e-6)
        out = []
        while j < len(Om) and keys[j] <= x + 1e-6:
            lo, hi, i = Om[j]
            if Rb.overlaps(lo.union(hi)):
                out.append(i)
            j += 1
        return out
    res = []
    # type (i)
    cfg = configs(qmax)
    print(len(cfg), 'configurations', file=sys.stderr, flush=True)
    Rc = {}
    for c in cfg:
        if 1 / (2 * math.sin(math.pi / max(c))) > Rmax:
            continue
        r = config_radius(c)
        if r is None:
            continue
        Rc[c] = r
    print(len(Rc), 'closable configurations with R_c <= Rmax', file=sys.stderr, flush=True)
    for n in range(17, N):
        rn = 1 / (2 * (PI / n).sin())
        for c, r in Rc.items():
            Rb = (rn * rn + r * r).sqrt()
            if float(Rb.mid()) > Rmax + 1:
                continue
            h = hits(Rb)
            if h:
                res.append(dict(type='i', n=n, config=list(c), R=Rb.str(25), omega=h))
    print('type (i) coincidences:', len(res), file=sys.stderr, flush=True)
    # types (ii) and (iii): certified closure roots around the n-gon
    for n in range(17, N):
        rn = 1 / (2 * (PI / n).sin())
        RA = cp.data([3, 3, 3, n])['R']
        RP = (rn * rn + arb(1) / 4).sqrt()
        alpha_D = lambda q: PI * (1 - arb(2) / q)
        for qs in [(q,) for q in range(3, qmax + 1)] + [(3, 3), (3, 4), (3, 5)]:
            # rays: A_n, then P_n cells; sides: (last P_n -> A_n) and (A_n -> P_n) are A_n x {}
            # (angle pi/2 at F), then {n}x{q} sides between consecutive P_n rays
            rayR = [RA] + [RP] * (1 + len(qs))
            alphas = [PI / 2, PI / 2] + [alpha_D(q) for q in qs]
            if sum(float(a.mid()) for a in alphas) >= 2 * math.pi - 1e-12:
                continue
            facR = [(RA * RA + arb(1) / 4).sqrt()] + [(rn * rn + (1 / (2 * (PI / q).sin())) ** 2).sqrt() for q in qs]
            Rmin = max(facR, key=lambda b: float(b.mid()))
            roots, nb = certify_cycle(rn, rayR, alphas, 1 / Rmin)
            if roots is None:
                res.append(dict(type='ii/iii', n=n, qs=list(qs), status='UNDECIDED'))
                continue
            for a, b in roots:
                Rb = (1 / b).union(1 / a) if a > 0 else None
                if Rb is None:
                    continue
                if float(Rb.mid()) > Rmax + 1:
                    continue
                h = hits(Rb)
                if h:
                    res.append(dict(type='ii' if len(qs) == 1 else 'iii', n=n, qs=list(qs), R=Rb.str(25), omega=h))
    print('total coincidences:', len(res), file=sys.stderr, flush=True)
    json.dump(dict(N=N, Rmax=Rmax, coincidences=res), open('caseb_coinc.json', 'w'), indent=0)


if __name__ == '__main__':
    main()
