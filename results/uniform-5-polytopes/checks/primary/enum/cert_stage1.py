"""Certified stage 1 for the 4-D control: edge neighbourhoods and the radii they allow.

Independent of geom.py: cell data come from vertex configurations
(cert_poly3), arithmetic is arb (python-flint).  In the variable s = 1/R the
closure function g(s) = sum_i omega_i - 2 pi is evaluated on boxes of
[0, s_max]; a box is discharged when g's enclosure excludes 0 or when some
triangle is certified impossible (acos argument outside [-1, 1]); the
remaining leaves are shrunk below a width threshold and their connected
covering unions are reported as root intervals. Merged intervals may be wider
than the leaf threshold; no root existence or uniqueness follows from retention.  Output: one record per cycle with its root intervals in R.
"""
import json, sys, math
from flint import arb, ctx
import cert_poly3 as cp

ctx.prec = 160
PI = arb.pi()
TWO_PI = 2 * PI


def cell_configs(pmax):
    arch = {
        'tet': [3, 3, 3], 'oct': [3, 3, 3, 3], 'cube': [4, 4, 4], 'ico': [3, 3, 3, 3, 3], 'doe': [5, 5, 5],
        'tut': [3, 6, 6], 'co': [3, 4, 3, 4], 'tic': [3, 8, 8], 'toe': [4, 6, 6], 'sirco': [3, 4, 4, 4],
        'girco': [4, 6, 8], 'id': [3, 5, 3, 5], 'tid': [5, 6, 6], 'ti': [3, 10, 10], 'srid': [3, 4, 5, 4],
        'grid': [4, 6, 10], 'snic': [3, 3, 3, 3, 4], 'snid': [3, 3, 3, 3, 5],
    }
    for n in range(3, pmax + 1):
        if n != 4:
            arch['P%d' % n] = [4, 4, n]
        if n != 3:
            arch['A%d' % n] = [3, 3, 3, n]
    return arch


def library(pmax):
    lib = {}
    for name, conf in cell_configs(pmax).items():
        d = cp.data(conf)
        # distinct edge orbits by (qa, qb, alpha): merge balls that overlap
        orbs = []
        for qa, qb, al in d['edges']:
            key = tuple(sorted((qa, qb)))
            hit = False
            for o in orbs:
                if o[0] == key and o[1].overlaps(al):
                    hit = True
                    break
            if not hit:
                orbs.append((key, al))
        lib[name] = dict(R=d['R'], orbits=orbs)
    return lib


def rho_poly(q):
    return 1 / (2 * (PI / q).sin())


def g_of_s(s, rhoF, rayR, alphas):
    """Closure function at s (arb ball, s = 1/R). Returns (value, status) where status is
    'ok', 'impossible' (certified no configuration in the whole ball) or 'unknown'."""
    # h^2 = R^2 - rhoF^2 -> cos(delta_G) = dG / h = dG * s / sqrt(1 - rhoF^2 s^2)
    den2 = 1 - rhoF * rhoF * s * s
    if den2 < 0:
        return None, 'impossible'
    den = den2.sqrt() if den2 > 0 else None
    if den is None:
        return None, 'unknown'
    cosd = []
    for RG in rayR:
        dG = (RG * RG - rhoF * rhoF).sqrt()
        c = dG * s / den
        if c > 1:
            return None, 'impossible'
        if not (c <= 1):
            return None, 'unknown'
        cosd.append(c)
    sind = [(1 - c * c).sqrt() for c in cosd]
    tot = arb(0)
    k = len(alphas)
    for i in range(k):
        ca, cb = cosd[i - 1], cosd[i]
        sa, sb = sind[i - 1], sind[i]
        num = alphas[i].cos() - ca * cb
        dd = sa * sb
        if not (dd > 0):
            return None, 'unknown'
        x = num / dd
        if x > 1 or x < -1:
            return None, 'impossible'
        # Clip below at -1: on the domain s <= 1/R_max every side has delta_a + delta_b >= alpha
        # (equality exactly when the centre lies in that facet's hyperplane; delta decreases in s),
        # so the true x is >= -1 there and the clipped enclosure still contains every genuine value.
        if x.lower() < -1 and x <= 1:
            # acos is decreasing: enclose acos over [-1, x.upper()] from the endpoints
            tot += arb(x.upper()).acos().union(arb(-1).acos())
            continue
        if not (x >= -1 and x <= 1):
            return None, 'unknown'
        tot += x.acos()
    return tot - TWO_PI, 'ok'


def certify_cycle(rhoF, rayR, alphas, s_max, width=1e-20, max_boxes=200000):
    """Partition [0, s_max] into discharged boxes and root boxes (s-intervals).
    s_max: an arb ball (or number) for 1/R_min; the domain runs to its upper end, so the true
    endpoint is covered (beyond it no configuration exists). The width bound
    applies to retained leaves only, before merging adjacent leaves. Unknown
    evaluations are retained; a box-cap failure returns None, never no roots.
    """
    if not arb(width).is_finite() or not arb(width) > 0:
        raise ValueError("positive finite leaf width required")
    if type(max_boxes) is not int or max_boxes < 1:
        raise ValueError("positive box cap required")
    if not arb(s_max).is_finite() or not arb(s_max) > 0:
        raise ValueError("positive finite reciprocal radius required")
    s_max = arb(arb(s_max).upper())
    roots, stack, nboxes = [], [(arb(0), s_max)], 0
    while stack:
        a, b = stack.pop()
        nboxes += 1
        if nboxes > max_boxes:
            return None, nboxes
        box = arb(a).union(arb(b))
        val, st = g_of_s(box, rhoF, rayR, alphas)
        if st == 'impossible':
            continue
        if st == 'ok' and not val.contains(0):
            continue
        if (b - a).upper() < width:
            roots.append((a, b))
            continue
        m = (a + b) / 2
        stack.append((a, m))
        stack.append((m, b))
    return merge_root_boxes(roots), nboxes


def exact_endpoint(x):
    """Exact dyadic point key: no decimal or float sort-key rounding."""
    from fractions import Fraction
    mantissa, exponent = x.man_exp()
    return Fraction(int(mantissa)) * Fraction(2) ** int(exponent)


def merge_root_boxes(roots):
    """Cover every retained leaf, including unknowns, by connected hulls.

    Bounds are Arb point endpoints. A union of many narrow leaves need not
    itself be narrow (all-unknown evaluation can retain the entire domain).
    """
    roots = [(arb(a.lower()), arb(b.upper())) for a, b in roots]
    roots.sort(key=lambda ab: exact_endpoint(ab[0]))
    merged = []
    for a, b in roots:
        if exact_endpoint(a) > exact_endpoint(b):
            raise ValueError('reversed root box')
        if merged and exact_endpoint(a) <= exact_endpoint(merged[-1][1]):
            hi = b if exact_endpoint(b) > exact_endpoint(merged[-1][1]) else merged[-1][1]
            merged[-1] = (merged[-1][0], hi)
        else:
            merged.append((a, b))
    return merged


def r_interval(a, b):
    """Outward-rounded decimal bounds [1/b, 1/a] for an s-box [a, b] (strings; 'inf' if a <= 0)."""
    # the 1e-32 margin absorbs the 45-digit decimal rounding of the printed bounds
    lo = ((1 / arb(b)).lower() - arb(10) ** -32).lower().str(45, radius=False)
    if not (a > 0):
        return [lo, 'inf']
    hi = ((1 / arb(a)).upper() + arb(10) ** -32).upper().str(45, radius=False)
    return [lo, hi]


def enumerate_cycles(lib):
    sides = []
    for name, d in lib.items():
        for (qa, qb), al in d['orbits']:
            sides.append((name, qa, qb, al))
            if qa != qb:
                sides.append((name, qb, qa, al))
    found = {}

    def canon(seq):
        k = len(seq)
        c = []
        for r in range(k):
            rot = seq[r:] + seq[:r]
            c.append(tuple((x[0], x[1], x[2]) for x in rot))
            rev = [(x[0], x[2], x[1]) for x in reversed(rot)]
            c.append(tuple(rev))
        return min(c)

    def dfs(seq, tot):
        if len(seq) >= 3 and seq[-1][2] == seq[0][1]:
            found.setdefault(canon(seq), list(seq))
        if len(seq) == 6:
            return
        for s in sides:
            if seq and s[1] != seq[-1][2]:
                continue
            t2 = tot + s[3]
            if t2 >= TWO_PI:      # certified at least 2 pi: no convex neighbourhood
                continue
            seq.append(s)
            dfs(seq, t2)
            seq.pop()
    dfs([], arb(0))
    return list(found.values())


if __name__ == '__main__':
    pmax = int(sys.argv[1])
    lib = library(pmax)
    cycles = enumerate_cycles(lib)
    out = []
    rhoF = arb(1) / 2
    for seq in cycles:
        rayR = [rho_poly(s[2]) for s in seq]
        alphas = [s[3] for s in seq]
        Rmin = max([lib[s[0]]['R'] for s in seq] + [arb(1) / 2], key=lambda b: float(b.mid()))
        s_max = 1 / Rmin
        roots, nb = certify_cycle(rhoF, rayR, alphas, s_max)
        rec = dict(cells=[s[0] for s in seq], faces=[s[2] for s in seq], boxes=nb)
        if roots is None:
            rec['status'] = 'UNDECIDED'
        else:
            rec['status'] = 'ROOT' if roots else 'NOROOT'
            rec['R'] = [r_interval(a, b) for a, b in roots]
        out.append(rec)
    print(len(cycles), 'cycles;', sum(r['status'] == 'ROOT' for r in out), 'with roots;',
          sum(r['status'] == 'UNDECIDED' for r in out), 'undecided', file=sys.stderr)
    json.dump(out, open('cert_stage1_4d_p%d.json' % pmax, 'w'), indent=0)
