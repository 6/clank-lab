#!/usr/bin/env python3
"""Independent rigorous checker (python-flint ball arithmetic only) for the claim:
the 1-1-1 ABC flow  x'=sin z+cos y, y'=sin x+cos z, z'=sin y+cos x  has a periodic orbit
whose first-return map P to z=2*pi has an elliptic fixed point with nonzero first Birkhoff coefficient.

usage: check_arb.py CERT [--N n] [--hinv m] [--prec bits]
Exit 0 iff every check passes.  Cert key `flow control` selects the integrable control flow
x'=cos y, y'=sin x, z'=13/10 (then the identity is used instead of Phi and the claimed tau is -tau0/4).

RIGOR POLICY.  Every number that enters a conclusion is an arb/acb ball.  Python floats are used only
for (a) choosing inflation radii inside the a-priori-enclosure search (the Picard containment test that
follows is performed in ball arithmetic, so a bad guess can only cause failure, never a false pass),
(b) the Newton iteration whose output is merely a *candidate* centre, re-verified by Krawczyk.
"""
import sys, time, resource, math
from itertools import product
from flint import arb, acb, ctx, arb_mat, acb_mat

T_WALL0 = time.perf_counter(); T_CPU0 = time.process_time()


def ledger(tag):
    ru = resource.getrusage(resource.RUSAGE_SELF)
    print("[ledger] %-34s wall=%7.1fs cpu=%7.1fs peakRSS(cumulative)=%.0f MB" % (
        tag, time.perf_counter() - T_WALL0, time.process_time() - T_CPU0, ru.ru_maxrss / 1024.0), flush=True)


class CheckFail(Exception):
    pass


# ----------------------------------------------------------------------------------------------
# 1. Truncated multivariate power series ("jets"): sum c_e x^e, |e| <= D.  Truncation is exact for
#    all Taylor coefficients up to total degree D (the ring of jets is a quotient ring).
# ----------------------------------------------------------------------------------------------
_tabs = {}


def tables(nv, D):
    key = (nv, D)
    if key not in _tabs:
        mons = sorted((e for e in product(range(D + 1), repeat=nv) if sum(e) <= D),
                      key=lambda e: (sum(e), tuple(-x for x in e)))
        idx = {e: i for i, e in enumerate(mons)}
        pairs = [[] for _ in mons]
        for i, a in enumerate(mons):
            for j, b in enumerate(mons):
                s = tuple(x + y for x, y in zip(a, b))
                if sum(s) <= D:
                    pairs[idx[s]].append((i, j))
        _tabs[key] = (mons, idx, pairs)
    return _tabs[key]


class Jet:
    __slots__ = ('c', 'nv', 'D')

    def __init__(s, c, nv, D):
        s.c = c; s.nv = nv; s.D = D

    @staticmethod
    def const(v, nv, D):
        z = v * 0
        return Jet([v] + [z] * (len(tables(nv, D)[0]) - 1), nv, D)

    @staticmethod
    def var(k, nv, D, one=None):
        one = arb(1) if one is None else one
        mons, idx, _ = tables(nv, D)
        j = Jet.const(one * 0, nv, D)
        e = [0] * nv; e[k] = 1
        j.c[idx[tuple(e)]] = one
        return j

    def __add__(s, o):
        if isinstance(o, Jet):
            return Jet([a + b for a, b in zip(s.c, o.c)], s.nv, s.D)
        c = list(s.c); c[0] = c[0] + o
        return Jet(c, s.nv, s.D)
    __radd__ = __add__

    def __sub__(s, o):
        if isinstance(o, Jet):
            return Jet([a - b for a, b in zip(s.c, o.c)], s.nv, s.D)
        c = list(s.c); c[0] = c[0] - o
        return Jet(c, s.nv, s.D)

    def __rsub__(s, o):
        c = [-a for a in s.c]; c[0] = c[0] + o
        return Jet(c, s.nv, s.D)

    def __neg__(s):
        return Jet([-a for a in s.c], s.nv, s.D)

    def __mul__(s, o):
        if isinstance(o, Jet):
            pairs = tables(s.nv, s.D)[2]
            a = s.c; b = o.c; out = []
            for pl in pairs:
                i, j = pl[0]
                t = a[i] * b[j]
                for i, j in pl[1:]:
                    t += a[i] * b[j]
                out.append(t)
            return Jet(out, s.nv, s.D)
        return Jet([a * o for a in s.c], s.nv, s.D)
    __rmul__ = __mul__

    def inv(s):
        """1/J for J with invertible constant term a0:  1/J = (1/a0) sum_m (-E)^m, E=(J-a0)/a0."""
        a0 = s.c[0]
        ia = 1 / a0
        E = Jet([a0 * 0] + [x * ia for x in s.c[1:]], s.nv, s.D)
        one = Jet.const(a0 * 0 + 1, s.nv, s.D)
        res = one; p = one
        for m in range(1, s.D + 1):
            p = p * (-E)
            res = res + p
        return res * ia

    def __truediv__(s, o):
        if isinstance(o, Jet):
            return s * o.inv()
        return s * (1 / o)


def jet_sincos(J):
    """sin and cos of a jet: sin(a0+H)=sin a0 cos H + cos a0 sin H with H=J-a0 nilpotent (H^(D+1)=0)."""
    nv, D = J.nv, J.D
    a0 = J.c[0]
    s0, c0 = a0.sin_cos()
    H = Jet([a0 * 0] + J.c[1:], nv, D)
    one = Jet.const(a0 * 0 + 1, nv, D)
    P = [one]
    for m in range(1, D + 1):
        P.append(P[-1] * H)
    sH = Jet.const(a0 * 0, nv, D); cH = Jet.const(a0 * 0, nv, D)
    for m in range(0, D + 1):
        co = arb(1) / math.factorial(m)
        if m % 2 == 0:
            cH = cH + P[m] * (co if (m // 2) % 2 == 0 else -co)
        else:
            sH = sH + P[m] * (co if ((m - 1) // 2) % 2 == 0 else -co)
    return s0 * cH + c0 * sH, c0 * cH - s0 * sH


def compose(J, subs):
    """J(subs): J a jet in len(subs) variables, subs jets (all with ZERO constant term) in some nv_out
    variables.  Exact in the jet ring (chain rule to total degree D)."""
    mons = tables(J.nv, J.D)[0]
    nvo, D = subs[0].nv, J.D
    one = Jet.const(J.c[0] * 0 + 1, nvo, D)
    pw = []
    for s in subs:
        l = [one]
        for e in range(1, D + 1):
            l.append(l[-1] * s)
        pw.append(l)
    cache = {}
    out = Jet.const(J.c[0] * 0, nvo, D)
    for coef, e in zip(J.c, mons):
        if e not in cache:
            t = None
            for i, ei in enumerate(e):
                if ei:
                    t = pw[i][ei] if t is None else t * pw[i][ei]
            cache[e] = one if t is None else t
        out = out + cache[e] * coef
    return out


def jet_inverse(g, mat_inv):
    """Inverse of a jet map g (list of nv jets, zero constant terms, linear part invertible).
    mat_inv(A) returns the inverse of the linear-part matrix (list of lists).  Degree by degree:
    g(h+delta_k) = g(h) + A delta_k + O(deg k+1)  =>  delta_k = -A^{-1}[g(h)]_k."""
    nv, D = g[0].nv, g[0].D
    mons, idx, _ = tables(nv, D)
    A = [[g[i].c[idx[tuple(1 if t == j else 0 for t in range(nv))]] for j in range(nv)] for i in range(nv)]
    Ai = mat_inv(A)
    one = g[0].c[0] * 0 + 1
    vars_ = [Jet.var(j, nv, D, one) for j in range(nv)]
    h = []
    for i in range(nv):
        t = vars_[0] * Ai[i][0]
        for j in range(1, nv):
            t = t + vars_[j] * Ai[i][j]
        h.append(t)
    for k in range(2, D + 1):
        R = [compose(gi, h) for gi in g]
        for m, e in enumerate(mons):
            if sum(e) != k:
                continue
            for i in range(nv):
                d = R[0].c[m] * Ai[i][0]
                for j in range(1, nv):
                    d = d + R[j].c[m] * Ai[i][j]
                h[i].c[m] = h[i].c[m] - d
    return h


def mat2_inv(A):
    det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    return [[A[1][1] / det, -A[0][1] / det], [-A[1][0] / det, A[0][0] / det]]


# ----------------------------------------------------------------------------------------------
# Flows.  Each flow provides F(u) (jet vector field) and the k-th Taylor coefficient of F(u(t))
# from the sin/cos Taylor coefficients S[v][k], C[v][k] of the components.
# ----------------------------------------------------------------------------------------------
class ABC:
    name = 'abc'; need = (True, True, True)

    def fz(self, x, y):
        return y.sin() + x.cos()

    def F(self, u):
        (sx, cx), (sy, cy), (sz, cz) = [jet_sincos(w) for w in u]
        return [sz + cy, sx + cz, sy + cx]

    def coef(self, S, C, k, u0):
        return [S[2][k] + C[1][k], S[0][k] + C[2][k], S[1][k] + C[0][k]]


class Control:
    name = 'control'; need = (True, True, False)

    def fz(self, x, y):
        return arb(13) / 10

    def F(self, u):
        sx, cx = jet_sincos(u[0]); sy, cy = jet_sincos(u[1])
        return [cy, sx, Jet.const(arb(13) / 10, u[0].nv, u[0].D)]

    def coef(self, S, C, k, u0):
        z = u0[2].c[0] * 0
        if k == 0:
            return [C[1][0], S[0][0], Jet.const(arb(13) / 10, u0[0].nv, u0[0].D)]
        return [C[1][k], S[0][k], Jet.const(z, u0[0].nv, u0[0].D)]


# ----------------------------------------------------------------------------------------------
# 2. Taylor method with rigorous remainder.
# ----------------------------------------------------------------------------------------------
def taylor(flow, u0, K, scale=None):
    """Time-Taylor coefficients X[v][0..K] (jets) of the solution of u'=scale*F(u), u(0)=u0, via the
    sin/cos recurrences  s_k=(1/k) sum_{j=1..k} j x_j c_{k-j},  c_k=-(1/k) sum j x_j s_{k-j}
    and x_{k+1}=(1/(k+1)) [scale*F(u)]_k.  These are exact identities of formal power series."""
    X = [[u0[v]] for v in range(3)]
    S = [[] for _ in range(3)]; C = [[] for _ in range(3)]; JX = [[] for _ in range(3)]
    for k in range(K):
        for v in range(3):
            if not flow.need[v]:
                continue
            if k == 0:
                s, c = jet_sincos(X[v][0]); S[v].append(s); C[v].append(c)
            else:
                JX[v].append(X[v][k] * k)           # j*x_j for j=k
                ss = None; cc = None
                for j in range(1, k + 1):
                    a = JX[v][j - 1] * C[v][k - j]
                    b = JX[v][j - 1] * S[v][k - j]
                    ss = a if ss is None else ss + a
                    cc = b if cc is None else cc + b
                ik = arb(1) / k
                S[v].append(ss * ik); C[v].append(-(cc * ik))
        G = flow.coef(S, C, k, u0)
        ik1 = arb(1) / (k + 1)
        for v in range(3):
            g = G[v] if scale is None else G[v] * scale
            X[v].append(g * ik1)
    return X


def apriori(flow, u0, hh, scale):
    """A-priori enclosure B (jet vector, ball coefficients) with u0 + [0,hh]*scale*F(B) subset B.
    RIGOR: if B satisfies this inclusion (Moore/Picard test, verified coefficient-wise in ball
    arithmetic) then the solution (and, since the jet coefficients solve the variational equations
    with the same Picard operator, every jet coefficient) exists on [0,hh] and stays in B."""
    hhf = float(hh)
    Ih = arb(0.5 * hhf, 0.5 * hhf)

    def Fs(B):
        Fv = flow.F(B)
        return Fv if scale is None else [f * scale for f in Fv]

    n = len(u0[0].c); nv, D = u0[0].nv, u0[0].D
    F0 = Fs(u0)
    floor = 1e-12 * hhf * max(float(f.abs_upper()) for v in range(3) for f in F0[v].c) + 2.0 ** -90
    B = []
    for v in range(3):
        B.append(Jet([arb(c.mid(), float(c.rad()) + 2 * hhf * float(f.abs_upper()) + floor)
                      for c, f in zip(u0[v].c, F0[v].c)], nv, D))
    ok = False
    for it in range(200):
        FB = Fs(B)
        Cn = [Jet([u0[v].c[i] + FB[v].c[i] * Ih for i in range(n)], nv, D) for v in range(3)]
        if all(B[v].c[i].contains(Cn[v].c[i]) for v in range(3) for i in range(n)):
            ok = True; break
        # next trial: the Picard image inflated (NOT cumulative: avoids runaway growth of unrelated coefficients)
        nb = []
        for v in range(3):
            nb.append(Jet([arb(c.mid(), float(c.rad()) * 1.3 + floor) for c in Cn[v].c], nv, D))
        B = nb
    if not ok:
        raise CheckFail("a-priori enclosure not found")
    # tighten: if C subset B then F(C) subset F(B) so u0+[0,h]F(C) subset C (still verified explicitly)
    for _ in range(2):
        B = Cn
        FB = Fs(B)
        Cn = [Jet([u0[v].c[i] + FB[v].c[i] * Ih for i in range(n)], nv, D) for v in range(3)]
        if not all(B[v].c[i].contains(Cn[v].c[i]) for v in range(3) for i in range(n)):
            Cn = B; break
    return Cn


def step(flow, u0, hh, N, scale=None, rem_prec=96):
    """One Taylor step of length hh (arb, a power of 2).  Returns B, Taylor coefficients, remainder
    coefficient jets and the enclosure of the state at time hh.
    RIGOR: for every jet coefficient a (itself a solution of the variational ODE), Taylor's theorem
    gives a(t)=sum_{k<=N} a_k t^k + a^{(N+1)}(theta)/(N+1)! t^{N+1}, theta in [0,t]; a^{(N+1)}/(N+1)!
    at time theta equals the (N+1)-st recurrence coefficient computed from the data u(theta), and
    u(theta) is in B (Picard test), so computing that coefficient with the ball data B encloses it."""
    B = apriori(flow, u0, hh, scale)
    xs = taylor(flow, u0, N, scale)
    p0 = ctx.prec
    ctx.prec = rem_prec            # lower precision is still rigorous (ball arithmetic rounds outward)
    xb = taylor(flow, B, N + 1, scale)
    ctx.prec = p0
    rem = [xb[v][N + 1] for v in range(3)]
    Ih = arb(0.5 * float(hh), 0.5 * float(hh))
    hp = [hh ** k for k in range(N + 2)]
    # rem already includes 1/(N+1)!: multiply by [0,hh^(N+1)], not hh^(N+2).
    # This factor is shared by every state and variational-jet coefficient.
    remfac = Ih * hp[N]
    end = []
    for v in range(3):
        t = xs[v][0]
        for k in range(1, N + 1):
            t = t + xs[v][k] * hp[k]
        end.append(t + rem[v] * remfac)
    return dict(B=B, xs=xs, rem=rem, end=end)


# ----------------------------------------------------------------------------------------------
# 3. First-return map with jets.
# ----------------------------------------------------------------------------------------------
def return_map(flow, cx, cy, D, N, hh, tag, verbose=True):
    """cx, cy: arb (exact point or ball).  Initial jet (cx+xi, cy+eta, 0).  Returns jets (2 variables,
    degree D) of P=(x,y)(first time z=2pi), plus the return-time enclosure."""
    t0 = time.perf_counter()
    twopi = 2 * arb.pi()
    xi = Jet.var(0, 2, D); eta = Jet.var(1, 2, D)
    u = [xi + cx, eta + cy, Jet.const(arb(0), 2, D)]
    k = 0; maxrem = 0.0; vzmin = float('inf')
    while True:
        if k > 2000:
            raise CheckFail("no crossing found")
        st = step(flow, u, hh, N)
        maxrem = max(maxrem, max(float(r.abs_upper()) for v in range(3) for r in st['rem'][v].c) * float(hh) ** (N + 1))
        # z' = sin y + cos x > 0 on every step's enclosure: z strictly increasing along the whole
        # segment, so it meets each plane z = c (0 <= c <= 2pi) exactly once, for every start in the box.
        Fk = flow.fz(st['B'][0].c[0], st['B'][1].c[0])
        if not Fk.lower() > 0:
            raise CheckFail("z' not > 0 on step %d: %s" % (k, Fk.str(10)))
        vzmin = min(vzmin, float(Fk.lower()))
        zB = st['B'][2].c[0]
        if zB.upper() < twopi:
            # z < 2pi on the whole step [t_k,t_{k+1}] for all points of the box: no crossing here
            u = st['end']; k += 1
            continue
        break
    # k-th step is the crossing step; u is the state at t_a = k*hh
    t_a = hh * k
    za = u[2].c[0]
    if not za.upper() < twopi:
        raise CheckFail("z(t_a) not < 2pi")
    zend = st['end'][2].c[0]
    if not zend.lower() > twopi:
        raise CheckFail("z at end of crossing step not > 2pi: z=" + zend.str(10))
    Bc = st['B']
    Fz = flow.fz(Bc[0].c[0], Bc[1].c[0])
    if not Fz.lower() > 0:
        raise CheckFail("z' not > 0 on crossing step: " + Fz.str(10))
    # => z strictly increasing on [t_a,t_a+hh], z(t_a)<2pi<z(t_a+hh): exactly one crossing, and since
    # z<2pi on [0,t_a] (every earlier step had sup z < 2pi) it is the FIRST time z=2pi (for every point
    # of the box); z(0)=0<2pi.
    xs = st['xs']; rem = st['rem']

    def evalu(s, v):
        r = xs[v][N].c[0]
        for j in range(N - 1, -1, -1):
            r = r * s + xs[v][j].c[0]
        return r + rem[v].c[0] * s ** (N + 1)

    # 1-D interval Newton for the constant term of the return time s0 in [0,hh]:
    # s* = m - Z(m)/Z'(xi) for some xi in S, hence s* in m - Z(m)/Z'(S), Z' = sin y + cos x > 0.
    S = arb(0.5 * float(hh), 0.5 * float(hh))
    for it in range(40):
        m = S.mid()
        zm = evalu(m, 2) - twopi
        uS = [evalu(S, v) for v in range(2)]
        der = flow.fz(uS[0], uS[1])
        if not der.lower() > 0:
            raise CheckFail("Z' not positive in Newton")
        new = m - zm / der
        S2 = S.intersection(new)
        if S2 is None or not (float(S2.rad()) < 0.99 * float(S.rad()) or it < 4):
            if S2 is not None:
                S = S2
            break
        S = S2
    S0 = S
    # Stage C: flow for time s=S0+zeta from u(t_a) as a 3-variable jet (xi,eta,zeta): rescale time
    # tau=s_/(S0+zeta): dv/dtau=(S0+zeta)F(v), tau in [0,1].  The constant term S0 of the time offset is a
    # ball containing s*(q) for every q in the box, so the jets are valid at the point (q,s*(q)).
    mons2, idx2, _ = tables(2, D); mons3, idx3, _ = tables(3, D)
    v0 = []
    for v in range(3):
        c3 = [u[v].c[0] * 0] * len(mons3)
        for i, e in enumerate(mons2):
            c3[idx3[e + (0,)]] = u[v].c[i]
        v0.append(Jet(c3, 3, D))
    sc = Jet.const(S0, 3, D); sc.c[idx3[(0, 0, 1)]] = arb(1)
    st3 = step(flow, v0, arb(1), N, scale=sc)
    Psi = st3['end']
    # root jet  zeta=sigma(xi,eta):  Z(xi,eta,sigma)=0,  sigma_k = sigma_{k-1} - [Z(.,sigma_{k-1})]_k / Z_zeta
    Z = Psi[2] - twopi
    Zz = Z.c[idx3[(0, 0, 1)]]
    if not Zz.lower() > 0:
        raise CheckFail("Z_zeta not positive")
    zero2 = Jet.const(arb(0), 2, D)
    sig = zero2
    for kk in range(1, D + 1):
        R = compose(Z, [xi, eta, sig])
        for i, e in enumerate(mons2):
            if sum(e) == kk:
                sig.c[i] = sig.c[i] - R.c[i] / Zz
    Pj = [compose(Psi[0], [xi, eta, sig]), compose(Psi[1], [xi, eta, sig])]
    T = t_a + S0
    if verbose:
        print("  [%s] steps=%d t_a=%s s0=%s (rad %.2e) T=%s maxTaylorRemainder~%.1e  min z' lower bound %.6f  %.1fs" % (
            tag, k, t_a.str(8), S0.str(8), float(S0.rad()), T.str(14), maxrem, vzmin, time.perf_counter() - t0), flush=True)
    return dict(P=Pj, T=T, S0=S0, t_a=t_a)


# ----------------------------------------------------------------------------------------------
# 4. Fixed point: non-rigorous Newton + rigorous Krawczyk.
# ----------------------------------------------------------------------------------------------
def dyadic(x, bits):
    return arb((x * 2 ** bits).floor().unique_fmpz()) / arb(2) ** bits


def newton_centre(flow, cx, cy, N, hh):
    for it in range(8):
        r = return_map(flow, cx, cy, 1, N, hh, "newton %d" % it, verbose=False)
        P = r['P']
        gx = P[0].c[0].mid() - cx; gy = P[1].c[0].mid() - cy
        a = P[0].c[1].mid() - 1; b = P[0].c[2].mid(); c = P[1].c[1].mid(); d = P[1].c[2].mid() - 1
        det = a * d - b * c
        dx = (d * gx - b * gy) / det; dy = (-c * gx + a * gy) / det
        cx = (cx - dx).mid(); cy = (cy - dy).mid()
        print("  newton it=%d step=%.3e residual=%.3e" % (it, max(abs(float(dx)), abs(float(dy))),
                                                       max(abs(float(gx)), abs(float(gy)))), flush=True)
        if max(abs(float(dx)), abs(float(dy))) < 1e-37:
            break
    return dyadic(cx, 120), dyadic(cy, 120)


def mat_from_jets(P):
    return [[P[0].c[1], P[0].c[2]], [P[1].c[1], P[1].c[2]]]


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__); return 2
    opts = dict(N=36, hinv=32, prec=256)
    cert_path = args[0]
    i = 1
    while i < len(args):
        opts[args[i].lstrip('-')] = int(args[i + 1]); i += 2
    ctx.prec = opts['prec']
    N = opts['N']; hh = arb(1) / opts['hinv']
    import flint
    print("python-flint", flint.__version__, "python", sys.version.split()[0],
          "prec", ctx.prec, "N", N, "h 1/%d" % opts['hinv'])
    cert = {}
    for line in open(cert_path):
        line = line.split('#')[0].strip()
        if line:
            kk, vv = line.split(None, 1); cert[kk] = vv.strip()
    flowname = cert.get('flow', 'abc')
    flow = ABC() if flowname == 'abc' else Control()
    cx_cert = arb(int(cert['centre_num_x'])) / arb(2) ** 40
    cy_cert = arb(int(cert['centre_num_y'])) / arb(2) ** 40
    rad_cert = arb(2) ** int(cert['radius_log2'])
    tlo, thi = arb(cert['time_lo']), arb(cert['time_hi'])
    trlo, trhi = arb(cert['trace_lo']), arb(cert['trace_hi'])
    print("cert:", cert)
    results = []

    def check(name, cond, detail=""):
        print("%s: %s %s" % ("PASS" if cond else "FAIL", name, detail), flush=True)
        results.append(bool(cond))
        return bool(cond)

    def abort():
        print("ABORT: dependent checks meaningless; exit 1"); ledger("end"); sys.exit(1)

    try:
        # --- fixed point
        print("== Newton (non-rigorous) from certificate centre")
        cx, cy = newton_centre(flow, cx_cert, cy_cert, N, hh)
        ledger("newton")
        r = arb(2) ** -100
        print("candidate centre c=(%s, %s), box radius 2^-100=%.3e" % (cx.str(40), cy.str(40), float(r)))
        inside = (abs(cx - cx_cert) + r <= rad_cert) and (abs(cy - cy_cert) + r <= rad_cert)
        if not check("(1a) X' = c+[-2^-100,2^-100]^2 is contained in certificate box X", inside,
                     "|c-centre|=(%.3e,%.3e) vs radius 2^%s" % (float(abs(cx - cx_cert)), float(abs(cy - cy_cert)), cert['radius_log2'])):
            abort()
        print("== Krawczyk on X'")
        rc = return_map(flow, cx, cy, 1, N, hh, "point c, D=1")
        ledger("point run")
        Xb = [arb(cx, 2.0 ** -100), arb(cy, 2.0 ** -100)]
        rb = return_map(flow, Xb[0], Xb[1], 3, N, hh, "box X', D=3")
        ledger("box run D=3")
        Pc = rc['P']; Pb = rb['P']
        G = [Pc[0].c[0] - cx, Pc[1].c[0] - cy]
        Jc = mat_from_jets(Pc); Jc[0][0] -= 1; Jc[1][1] -= 1
        Jb = mat_from_jets(Pb); Jb[0][0] -= 1; Jb[1][1] -= 1
        A = mat2_inv([[Jc[a][b].mid() for b in range(2)] for a in range(2)])
        A = [[A[a][b].mid() for b in range(2)] for a in range(2)]
        # Krawczyk: K = c - A G(c) + (I - A J(X'))(X'-c)
        M = [[(1 if a == b else 0) - (A[a][0] * Jb[0][b] + A[a][1] * Jb[1][b]) for b in range(2)] for a in range(2)]
        dX = [arb(0, 2.0 ** -100), arb(0, 2.0 ** -100)]
        K = [cx - (A[0][0] * G[0] + A[0][1] * G[1]) + M[0][0] * dX[0] + M[0][1] * dX[1],
             cy - (A[1][0] * G[0] + A[1][1] * G[1]) + M[1][0] * dX[0] + M[1][1] * dX[1]]
        okK = (K[0].lower() > cx - r and K[0].upper() < cx + r and K[1].lower() > cy - r and K[1].upper() < cy + r)
        check("(1b) Krawczyk K(X') strictly inside X'  => unique zero of P-id in X' (P(p)=p exactly in R^2)", okK,
              "|K-c|=(%.2e,%.2e) vs r=%.2e; |I-AJ|~%.2e" % (float(abs(K[0] - cx).upper()), float(abs(K[1] - cy).upper()),
                                                           float(r), max(float(abs(M[a][b]).upper()) for a in range(2) for b in range(2))))
        if not okK:
            abort()
        T = rb['T']
        check("(1c) return time T=%s in [%s,%s] (and crossing is the first, z'>0: proved in run)" % (T.str(12), cert['time_lo'], cert['time_hi']),
              T.lower() >= tlo and T.upper() <= thi)
        # --- trace
        DP = mat_from_jets(Pb)
        tr = DP[0][0] + DP[1][1]; det = DP[0][0] * DP[1][1] - DP[0][1] * DP[1][0]
        print("  DP(p) =", [[x.str(18) for x in row] for row in DP])
        check("(2a) trace DP(p)=%s in [%s,%s]" % (tr.str(18), cert['trace_lo'], cert['trace_hi']),
              tr.lower() >= trlo and tr.upper() <= trhi)
        if flowname == 'abc':
            check("(2b) cert trace interval inside (-2,-1)", trlo > -2 and trhi < -1)
        else:
            check("(2b) cert trace interval inside (-2,2)", trlo > -2 and trhi < 2)
        th = (tr / 2).acos()
        okq = True
        for q in range(1, 5):
            x = q * th / (2 * arb.pi())
            fl, fu = x.lower().floor(), x.upper().floor()
            good = (fl == fu) and (x.lower() != fl)
            okq &= good
            print("   q=%d: q*theta/(2pi) in %s -> %s" % (q, x.str(12), "non-integer" if good else "MAY BE INTEGER"))
        check("(2c) lambda^q != 1 for q=1..4 (and |lambda|=1 since |trace|<2, det=1)", okq and abs(tr).upper() < 2)
        check("(2d) det DP(p) = %s contains 1" % det.str(15), det.contains(1))
        ledger("checks 1-2")
        # --- area-preserving coordinates
        print("== area-preserving coordinates")
        D = 3
        xi = Jet.var(0, 2, D); eta = Jet.var(1, 2, D)
        Pj = [Jet([arb(0)] + Pb[0].c[1:], 2, D), Jet([arb(0)] + Pb[1].c[1:], 2, D)]   # P(p+xi)-p : p is the exact fixed point
        if flowname == 'abc':
            px = arb(cx, 2.0 ** -100); py = arb(cy, 2.0 ** -100)
            X = xi + px; Y = eta + py
            sY, cY = jet_sincos(Y); sX, cX = jet_sincos(X)
            Phi = [X * sY + sX, Y]
            Phij = [Jet([arb(0)] + f.c[1:], 2, D) for f in Phi]    # Phi(p+zeta)-Phi(p)
            Phiinv = jet_inverse(Phij, mat2_inv)
            Mt = [compose(compose(Phij[a], Pj), Phiinv) for a in range(2)]
            print("   Phi*(dX^dY)=(sin y+cos x)dx^dy: det DPhi = sin y+cos x, checked symbolically: dPhi=[[sin y+cos x, x cos y],[0,1]]")
        else:
            Mt = Pj
        for a in range(2):
            Mt[a].c[0] = arb(0)
        # sanity: Jacobian determinant of M is 1 up to degree 2
        mons, idx, _ = tables(2, D)

        def dd(Jt, var):
            out = [Jt.c[0] * 0] * len(mons)
            for ii, e in enumerate(mons):
                if e[var] > 0:
                    e2 = list(e); e2[var] -= 1
                    out[idx[tuple(e2)]] = Jt.c[ii] * e[var]
            return Jet(out, 2, D)
        Jd = dd(Mt[0], 0) * dd(Mt[1], 1) - dd(Mt[0], 1) * dd(Mt[1], 0)
        ok2 = all(Jd.c[ii].contains(1 if sum(e) == 0 else 0) for ii, e in enumerate(mons) if sum(e) <= 2)
        LM = mat_from_jets(Mt)
        dett = LM[0][0] * LM[1][1] - LM[0][1] * LM[1][0]
        check("(6a) det D(P~)(Phi(p)) = %s contains 1" % dett.str(15), dett.contains(1))
        check("(6b) Jacobian determinant of the 3-jet of P~ equals 1 up to degree 2 (area preservation sanity)", ok2)
        ledger("area-preserving coords")
        # --- Birkhoff normal form
        print("== third order Birkhoff normal form")
        trt = LM[0][0] + LM[1][1]
        disc = trt * trt - 4 * dett
        sq = acb(disc).sqrt()
        lam_a = (trt + sq) / 2; lam_b = (trt - sq) / 2    # lam_a has Im>0
        cands = []
        for lam, oth in ((lam_a, lam_b), (lam_b, lam_a)):
            v0 = acb(LM[0][1]); v1 = lam - LM[0][0]
            nu = (v0 * v1.conjugate()).imag
            cands.append((nu, lam, oth, v0, v1))
        cands.sort(key=lambda t: -float(t[0]))
        nu, lamA, lamB, v0, v1 = cands[0]
        if not nu.lower() > 0:
            raise CheckFail("cannot orient eigenvector")
        # normalisation: x~ = v w + conj(v) wbar, Im(v0 conj(v1)) = 1/2.  Then dx^dy = 4*Im(v0 conj v1) rho drho dphi =
        # 2 rho drho dphi, area(|w|=rho) = 2 pi rho^2, action I = area/(2 pi) = |w|^2 (+O(|w|^4)).
        sc = 1 / (2 * nu).sqrt()
        vA = (v0 * sc, v1 * sc)
        vB = (acb(LM[0][1]) * sc, (lamB - LM[0][0]) * sc)
        print("   lambda =", lamA.str(20), " |lambda|^2-1 enclosure:", (lamA * lamB - 1).str(5))
        V = acb_mat(2, 2, [vA[0], vB[0], vA[1], vB[1]])
        Vi = V.inv()
        w1 = Jet.var(0, 2, D, acb(1)); w2 = Jet.var(1, 2, D, acb(1))
        Mc = [Jet([acb(x) for x in Mt[a].c], 2, D) for a in range(2)]
        subs = [w1 * V[0, 0] + w2 * V[0, 1], w1 * V[1, 0] + w2 * V[1, 1]]
        Mw = [compose(Mc[a], subs) for a in range(2)]
        Nj = [Mw[0] * Vi[0, 0] + Mw[1] * Vi[0, 1], Mw[0] * Vi[1, 0] + Mw[1] * Vi[1, 1]]
        lams = [lamA, lamB]
        h = []
        for a in range(2):
            c = [acb(0)] * len(mons)
            for ii, e in enumerate(mons):
                if sum(e) == 2:
                    c[ii] = Nj[a].c[ii] / (lamA ** e[0] * lamB ** e[1] - lams[a])
            h.append(Jet(c, 2, D))
        phi = [w1 + h[0], w2 + h[1]]
        phi0 = [Jet([acb(0)] + p.c[1:], 2, D) for p in phi]
        phinv = jet_inverse(phi0, mat2_inv)
        NphiC = [compose(Nj[0], phi0), compose(Nj[1], phi0)]
        Nt = [compose(phinv[a], NphiC) for a in range(2)]
        maxquad = max(float(Nt[a].c[ii].abs_upper()) for a in range(2) for ii, e in enumerate(mons) if sum(e) == 2)
        print("   after normalisation: linear part N~1 = (%s)*w + (%s)*wbar ; max|quadratic coefficient| <= %.2e" % (
            Nt[0].c[idx[(1, 0)]].str(12), Nt[0].c[idx[(0, 1)]].str(5), maxquad))
        beta = Nt[0].c[idx[(2, 1)]]
        tau = acb(0, -1) * beta / lamA
        print("   beta (coeff of w^2 wbar in N~1) =", beta.str(25))
        print("   tau = -i beta/lambda: Re =", tau.real.str(30), "  Im =", tau.imag.str(10))
        check("(7a) 0 not in Re tau (first Birkhoff coefficient nonzero)", not tau.real.contains(0))
        check("(7b) Im tau small ball containing 0", tau.imag.contains(0) and float(tau.imag.rad()) < 1e-20)
        check("(7c) quadratic terms eliminated (all |coeff| < 1e-20)", maxquad < 1e-20)
        if flowname == 'control':
            tau0 = 2 * arb.pi() / (arb(13) / 10)
            expect = -tau0 / 4
            diff = tau.real - expect
            print("   expected -tau0/4 =", expect.str(30), " computed Re tau - expected =", diff.str(8))
            check("(8) control: tau = -tau0/4 (action I=|w|^2, rotation angle tau0(1-I/4))", diff.contains(0) and float(diff.abs_upper()) < 1e-24)
        ledger("birkhoff")
    except CheckFail as e:
        check("exception: " + str(e), False)
    allok = all(results) and len(results) > 0
    print("RESULT:", "ALL CHECKS PASS" if allok else "FAILURE")
    ledger("end")
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main())
