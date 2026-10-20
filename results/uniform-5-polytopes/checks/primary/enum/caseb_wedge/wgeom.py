"""Fan geometry for the wedge lemma (W) of CASEB.md, in arb interval arithmetic.

Written independently of enum/caseb_explore/.  Every function takes a
parameter box (arb balls) and returns enclosures, valid for every parameter
point of the box that lies in the fan's domain.

Coordinates: v = 0 in R^5, L = span(e1, e2) (the large n-gon F), L-perp =
span(e3, e4, e5).  theta = pi/n, n >= 17 (theta in [0, pi/17], theta = 0 is
n = infinity).  P's centre c = (0, r_n, c3, c4, c5), r_n = 1/(2 sin theta).
A VF vertex p satisfies |p| = 1 and p.c = 1/2, i.e. p.chat = kappa with
chat = c/|c| and kappa = 1/(2R).  The geometry is returned as

    Geom(kappa, chat, verts, normals)

verts: list of (name, x in R^5, allowed) -- the fan vertices (unit vectors on
the VF sphere); allowed = may be one end of a long VF-edge in (W).
normals: list of (name, N in R^5): admissible p satisfy N.p >= 0; each N is
oriented so that N.c > 0 (certified here, else Undecided is raised).
"""
import math
from flint import arb
from wconfigs import require_bounded_slice, PAIRED_UNBOUNDED
PI = arb.pi()
S17 = (PI / 17).sin()
ZERO, ONE, HALF = (arb(0), arb(1), arb(1) / 2)

class Undecided(Exception):
    """An enclosure was too wide to certify a sign: split the parameter box."""

class OutOfDomain(Exception):
    """The parameter box contains no point of the fan's domain."""

class NotClosable(Exception):
    """Certified: c_perp is not inside the cone of the rays."""

def float_upper(x):
    """Binary64 endpoint >= the Arb upper bound, at any working precision.

    float(Arb) rounds to nearest; compare the exact dyadics before using
    the result as a domain endpoint. At native 53 bits this preserves the
    historical endpoint whenever it is already representable.
    """
    bound = x.upper()
    value = float(bound)
    if not math.isfinite(value):
        raise ValueError('nonfinite binary64 domain endpoint')
    if arb(value) < bound:
        value = math.nextafter(value, math.inf)
    if not arb(value) >= bound:
        raise ValueError('uncertified upper endpoint conversion')
    return value

def float_lower(x):
    """Binary64 endpoint <= the Arb lower bound; see float_upper."""
    bound = x.lower()
    value = float(bound)
    if not math.isfinite(value):
        raise ValueError('nonfinite binary64 domain endpoint')
    if arb(value) > bound:
        value = math.nextafter(value, -math.inf)
    if not arb(value) <= bound:
        raise ValueError('uncertified lower endpoint conversion')
    return value

def iv(lo, hi):
    return arb(lo).union(arb(hi))

def clip(x, lo, hi):
    """x intersected with [lo, hi]; OutOfDomain if certainly disjoint."""
    box = arb(lo).union(arb(hi))
    if not x.overlaps(box):
        raise OutOfDomain()
    return x.intersection(box)

def sqrt_nn(x):
    """sqrt of a ball known (mathematically) to be >= 0 at the true point."""
    if x < 0:
        raise OutOfDomain()
    return x.nonnegative_part().sqrt()

def dot(u, v):
    s = ZERO
    for a, b in zip(u, v):
        s = s + a * b
    return s

def cross(u, v):
    return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]

def lift(q):
    """L-perp 3-vector -> R^5."""
    return [ZERO, ZERO] + list(q)

class Geom:

    def __init__(self, kappa, chat, verts, normals):
        self.kappa, self.chat, self.verts, self.normals = (kappa, chat, verts, normals)

def ab_vertices(sinth):
    costh = sqrt_nn(1 - sinth * sinth)
    return [('a', [costh, sinth, ZERO, ZERO, ZERO], False), ('b', [-costh, sinth, ZERO, ZERO, ZERO], False)]

def closure_f(qs, sina):
    """sum_i 2 asin(cos(pi/q_i)/sin alpha) - 2 pi (decreasing in alpha)."""
    s = -2 * PI
    for q in qs:
        s = s + 2 * ((PI / q).cos() / sina).asin()
    return s

def solve_alpha(qs, iters=60):
    """Certified enclosure of the unique root alpha in (0, pi/2) of the closure
    equation (every asin argument <= 1), or None if certified not closable.
    f is decreasing in alpha on [alpha_min, pi/2] (each term is), with
    sin(alpha_min) = max_i cos(pi/q_i); closable iff f(alpha_min) >= 0, and
    f(pi/2) = -2 pi sum(1/q_i) + pi (k - 2) < 0 when sum(1 - 2/q_i) < 2."""
    cmax = (PI / max(qs)).cos()
    f0 = closure_f([q for q in qs if q != max(qs)], cmax) + PI * sum((1 for q in qs if q == max(qs)))
    if f0 < 0:
        return None
    if not f0 > 0:
        raise Undecided('closure at alpha_min undecided for %s' % (qs,))
    lo, hi = (cmax.asin(), PI / 2)
    if not closure_f(qs, hi.sin()) < 0:
        raise Undecided('closure at pi/2')
    lo, hi = (float_upper(lo) + 1e-15, float_lower(hi))
    lo = arb(lo)
    if not closure_f(qs, lo.sin()) > 0:
        raise AssertionError()
    hi = arb(hi)
    if not closure_f(qs, hi.sin()) < 0:
        raise AssertionError()
    for _ in range(iters):
        mid = arb(float(((lo + hi) / 2).mid()))
        fm = closure_f(qs, mid.sin())
        if fm > 0:
            lo = mid
        elif fm < 0:
            hi = mid
        else:
            m = float(mid.mid())
            for eps in (1e-14, 1e-13, 1e-12, 1e-11):
                a, b = (arb(m - eps), arb(m + eps))
                if closure_f(qs, a.sin()) > 0 and closure_f(qs, b.sin()) < 0:
                    lo, hi = (a, b)
                    break
            else:
                raise Undecided('alpha bracket')
            break
    return lo.union(hi)

def type_i_cone(qs, alpha):
    """Rays u_1..u_k of a type (i) configuration and c_perp = (0, 0, R_c)."""
    sa, ca = (alpha.sin(), alpha.cos())
    psi, rays = (ZERO, [])
    for q in qs:
        rays.append([sa * psi.cos(), sa * psi.sin(), ca])
        psi = psi + 2 * ((PI / q).cos() / sa).asin()
    if not psi.contains(2 * PI):
        raise AssertionError()
    return (rays, [ZERO, ZERO, 1 / (2 * ca)])

def cdot(n, cdir):
    """n.cdir, skipping exact-zero entries of n (cdir may contain an
    unbounded ball, e.g. 1/(2 sin u) on a box containing u = 0)."""
    s = ZERO
    for a, b in zip(n, cdir):
        if not (a.is_exact() and a.is_zero()):
            s = s + a * b
    return s

def cone_normals(rays, cdir, names=None, fixed=None):
    """Normals n_i of consecutive ray pairs (r_i, r_{i+1}) (cyclic), oriented
    towards c.  n_i = r_i x r_{i+1}, or fixed[i], a positive multiple of it
    given in closed form.  All n_i.cdir must have one common sign (c_perp
    inside the cone spanned by the rays, i.e. the configuration closes around
    c); a certified mixed sign raises NotClosable.  cdir may be a list of
    several positive multiples of c_perp: a sign certified by any one counts."""
    k = len(rays)
    cdirs = cdir if isinstance(cdir[0], list) else [cdir]
    ns, signs = ([], [])
    for i in range(k):
        n = fixed[i] if fixed and i in fixed else cross(rays[i], rays[(i + 1) % k])
        sg = 0
        for cd in cdirs:
            d = cdot(n, cd)
            if d > 0 or d < 0:
                sg = 1 if d > 0 else -1
                break
        signs.append(sg)
        ns.append(n)
    if 0 in signs:
        if 1 in signs and -1 in signs:
            raise NotClosable()
        raise Undecided('normal orientation')
    if len(set(signs)) > 1:
        raise NotClosable()
    sg = signs[0]
    return [(names[i] if names else 'N%d' % (i + 1), lift([t * sg for t in ns[i]])) for i in range(k)]

class FixedCone:
    """Fan whose L-perp part (rays, c_perp) does not depend on theta: type (i)
    configurations, and the paired type (i) fans at a fixed integer m.
    Parameter: beta in [0, beta_max], tan(beta) = R_c / r_n = 2 R_c sin(theta),
    so chat = (0, cos beta, sin beta * c_perp/R_c), kappa = sin(beta)/(2 R_c)."""

    def __init__(self, rays, cperp, allowed, normals_fixed=None):
        self.rays, self.cperp, self.allowed = (rays, cperp, allowed)
        self.Rc = dot(cperp, cperp).sqrt()
        self.dir = [t / self.Rc for t in cperp]
        self.normals = cone_normals(rays, cperp, fixed=normals_fixed)
        self.xs = [('x%d' % (i + 1), lift(u), al) for i, (u, al) in enumerate(zip(rays, allowed))]
        bmax = (2 * self.Rc * S17).atan()
        self.pbox = [(0.0, float_upper(bmax))]

    def __call__(self, P):
        beta = iv(*P[0])
        sb, cb = (beta.sin(), beta.cos())
        sinth = clip(beta.tan() / (2 * self.Rc), 0, S17)
        chat = [ZERO, cb] + [sb * d for d in self.dir]
        kappa = sb / (2 * self.Rc)
        return Geom(kappa, chat, ab_vertices(sinth) + self.xs, self.normals)

def type_i(qs):
    alpha = solve_alpha(qs)
    if alpha is None:
        return None
    rays, cperp = type_i_cone(qs, alpha)
    return FixedCone(rays, cperp, [True] * len(qs))

def antiprism_data(theta):
    sinth = clip(theta.sin(), 0, S17)
    h2 = theta / 2
    tanh2 = h2.tan()
    hA = sqrt_nn(1 - 1 / (4 * h2.cos() ** 2))
    x = [HALF, tanh2 / 2, hA, ZERO, ZERO]
    y = [-HALF, tanh2 / 2, hA, ZERO, ZERO]
    return (sinth, hA, x, y)

def centre_theta(sinth, c3, c4):
    """c = (0, 1/(2 sin theta), c3, c4, 0): chat and kappa = 1/(2|c|)."""
    cp = [ZERO, ONE, 2 * sinth * c3, 2 * sinth * c4, ZERO]
    nrm = dot(cp, cp).sqrt()
    return ([t / nrm for t in cp], sinth / nrm)

class TypeII:
    """A_n x {}, A_n x {}, {n}x{q}; q = 3..16."""

    def __init__(self, q):
        self.q = q
        self.cphi, self.sphi = ((PI / q).sin(), (PI / q).cos())
        self.pbox = [(0.0, float_upper(PI / 17))]

    def __call__(self, P):
        theta = iv(*P[0])
        sinth, hA, x, y = antiprism_data(theta)
        cphi, sphi = (self.cphi, self.sphi)
        z1 = [ZERO, ZERO, ZERO, cphi, sphi]
        z2 = [ZERO, ZERO, ZERO, cphi, -sphi]
        cperp = [hA / 2, 1 / (2 * cphi), ZERO]
        normals = cone_normals([[ONE, ZERO, ZERO], z1[2:], z2[2:]], cperp, names=['h-z1', 'z1-z2', 'z2-h'], fixed={1: [-ONE, ZERO, ZERO]})
        chat, kappa = centre_theta(sinth, hA / 2, 1 / (2 * cphi))
        verts = ab_vertices(sinth) + [('x', x, True), ('y', y, True), ('z1', z1, True), ('z2', z2, True)]
        return Geom(kappa, chat, verts, normals)

class TypeIII:
    """A_n x {}, A_n x {}, {n}x{q1}, {n}x{q2}; phi = phi(theta) from the
    equation w.c = 1/2.  roots: list of (theta_lo, theta_hi, Phi) covering
    [0, pi/17], Phi an arb enclosure of every root phi for theta in the box
    (built by caseb_wedge/wroots.py)."""

    def __init__(self, q1, q2, roots):
        self.q1, self.q2, self.roots = (q1, q2, roots)
        self.cw1, self.cw2 = (-(2 * PI / q1).cos(), -(2 * PI / q2).cos())
        self.pbox = [(0.0, float_upper(PI / 17))]

    def w_of(self, phi):
        return w_vector(self.cw1, self.cw2, phi, self.q1 == self.q2)

    def phi_enclosure(self, tlo, thi):
        res = None
        for a, b, Phi in self.roots:
            if b >= tlo and a <= thi:
                res = Phi if res is None else res.union(Phi)
        return res

    def refine(self, theta, hA, phi, steps=4):
        """Interval Newton on g(theta, .) (wroots.py): every root in phi stays
        in mid - g(mid)/g'(phi), g' != 0 being certified on phi."""
        import wroots
        C1, C2, eq = (self.cw1, self.cw2, self.q1 == self.q2)
        for _ in range(steps):
            d = wroots.g_der(C1, C2, eq, hA, phi)
            if not (d > 0 or d < 0):
                break
            m = arb(phi.mid())
            new = m - wroots.g_val(C1, C2, eq, hA, m) / d
            if not new.overlaps(phi):
                raise Undecided('Newton step left the root enclosure')
            phi = new.intersection(phi)
        return phi

    def __call__(self, P):
        theta = iv(*P[0])
        sinth, hA, x, y = antiprism_data(theta)
        phi = self.refine(theta, hA, self.phi_enclosure(*P[0]))
        cphi, sphi = ((phi / 2).cos(), (phi / 2).sin())
        w = self.w_of(phi)
        z1 = [ZERO, cphi, sphi]
        z2 = [ZERO, cphi, -sphi]
        cperp = [hA / 2, 1 / (2 * cphi), ZERO]
        h = [ONE, ZERO, ZERO]
        normals = cone_normals([h, z1, w, z2], cperp, names=['h-z1', 'z1-w', 'w-z2', 'z2-h'])
        chat, kappa = centre_theta(sinth, hA / 2, 1 / (2 * cphi))
        verts = ab_vertices(sinth) + [('x', x, True), ('y', y, True), ('z1', lift(z1), True), ('z2', lift(z2), True), ('w', lift(w), True)]
        return Geom(kappa, chat, verts, normals)

def w_vector(cw1, cw2, phi, equal):
    """w = (w3, w4, w5) in L-perp; equal: q1 == q2 (then w5 = 0 exactly)."""
    cphi, sphi = ((phi / 2).cos(), (phi / 2).sin())
    w4 = (cw1 + cw2) / (2 * cphi)
    w5 = ZERO if equal else (cw1 - cw2) / (2 * sphi)
    w3 = -sqrt_nn(1 - w4 * w4 - w5 * w5)
    return [w3, w4, w5]

def paired_i_rays(rest, sinu, cosu):
    """Rays and c_perp * 2 sin(u) for the paired configuration (m, *rest),
    rest in {(4,4), (3,6), (3,7), (3,8), (3,9), (4,5), (3,3,3)} (or (3,3),
    (3,4), (3,5), which are not closable).  Returns (rays, C4, ok) where
    c_perp = (0, C4, 1/(2 sin u)); ok False if certified not closable, else
    the rays with their e5-component divided by sin u (continuous at u = 0)."""
    u1 = [cosu, ZERO, sinu]
    u2 = [-cosu, ZERO, sinu]
    if len(rest) == 3:
        if not rest == (3, 3, 3):
            raise AssertionError()
        cosh2sq = (1 + cosu) / 2
        c = sinu / (4 * cosh2sq)
        b = sqrt_nn(arb(3) / 4 - c * c)
        u3 = [-HALF, b, c]
        u4 = [HALF, b, c]
        C4 = (HALF - 1 / (8 * cosh2sq)) / b
        cs = 1 / (4 * cosh2sq)
        scaled = [[cosu, ZERO, ONE], [-cosu, ZERO, ONE], [-HALF, b, cs], [HALF, b, cs]]
        return ([u1, u2, u3, u4], C4, scaled)
    q2, q3 = rest
    g2, g3 = (-(2 * PI / q2).cos(), -(2 * PI / q3).cos())
    a3 = (g3 - g2) / (2 * cosu)
    if (q2, q3) in ((4, 4), (3, 6), (6, 3)):
        c3 = ZERO
        csu = ZERO
    else:
        c3 = (g3 + g2) / (2 * sinu)
        csu = (g3 + g2) / (4 * sinu * sinu)
    b2 = 1 - a3 * a3 - c3 * c3
    if b2 < 0:
        return (None, None, False)
    if not b2 > 0:
        raise Undecided('paired closability')
    b3 = b2.sqrt()
    u3 = [a3, b3, c3]
    C4 = (HALF - csu) / b3
    scaled = [[cosu, ZERO, ONE], [-cosu, ZERO, ONE], [a3, b3, 2 * csu]]
    return ([u1, u2, u3], C4, scaled)

def paired_i_fixed(rest, m):
    """Paired type (i) fan at a fixed integer m (bounded families)."""
    m = require_bounded_slice(rest, m)
    u = PI / m
    rays, C4, ok = paired_i_rays(rest, u.sin(), u.cos())
    if not ok:
        return None
    cperp = [ZERO, C4, 1 / (2 * u.sin())]
    allowed = [False, False] + [True] * (len(rays) - 2)
    return FixedCone(rays, cperp, allowed, normals_fixed={0: [ZERO, -ONE, ZERO]})

class PairedPolar:
    """Paired fans for all m >= 17 including m = infinity: parameters
    (beta, rho) with sin(theta) = rho cos(beta), sin(u) = rho sin(beta),
    beta in [0, pi/2], rho in [0, sqrt(2) sin(pi/17)] clipped to the domain
    sin(theta), sin(u) <= sin(pi/17).  kind 'i' (rest = the other entries of
    the configuration) or 'ii' (type (ii) with q = m)."""

    def __init__(self, kind, rest=None):
        if kind not in ('i', 'ii') or (kind == 'i' and tuple(rest or ()) not in PAIRED_UNBOUNDED):
            raise ValueError('polar chart covers only the four unbounded families')
        self.kind, self.rest = (kind, rest)
        self.pbox = [(0.0, float_upper(PI / 2)), (0.0, float_upper((2 * S17 * S17).sqrt()))]

    def __call__(self, P):
        beta, rho = (iv(*P[0]), iv(*P[1]))
        sb, cb = (beta.sin(), beta.cos())
        sinth = clip(rho * cb, 0, S17)
        sinu = clip(rho * sb, 0, S17)
        cosu = sqrt_nn(1 - sinu * sinu)
        if self.kind == 'i':
            rays, C4, scaled = paired_i_rays(self.rest, sinu, cosu)
            if not scaled:
                raise OutOfDomain()
            cp = [ZERO, sb, ZERO, 2 * rho * sb * cb * C4, cb]
            cdir = [[ZERO, 2 * sinu * C4, ONE], [ZERO, C4, 1 / (2 * sinu)]]
            normals = cone_normals(rays, cdir, fixed={0: [ZERO, -ONE, ZERO]})
            allowed = [False, False] + [True] * (len(rays) - 2)
            verts = [('x%d' % (i + 1), lift(r), al) for i, (r, al) in enumerate(zip(rays, allowed))]
            D, Cb = (4, {2: ZERO, 3: C4})
            ctil = [ZERO, C4, HALF]
            names = ['N%d' % (i + 1) for i in range(len(rays))]
        else:
            _, hA, x, y = antiprism_data(sinth.asin())
            z1 = [ZERO, sinu, cosu]
            z2 = [ZERO, sinu, -cosu]
            cp = [ZERO, sb, hA * rho * sb * cb, cb, ZERO]
            cdir = [[hA * sinu, ONE, ZERO], [hA / 2, 1 / (2 * sinu), ZERO]]
            normals = cone_normals([[ONE, ZERO, ZERO], z1, z2], cdir, names=['h-z1', 'z1-z2', 'z2-h'], fixed={1: [-ONE, ZERO, ZERO]})
            verts = [('x', x, True), ('y', y, True), ('z1', lift(z1), False), ('z2', lift(z2), False)]
            D, Cb = (3, {2: hA / 2, 4: ZERO})
            ctil = [hA / 2, HALF, ZERO]
            scaled = [[ONE, ZERO, ZERO], [ZERO, ONE, cosu], [ZERO, ONE, -cosu]]
            names = ['h-z1', 'z1-z2', 'z2-h']
        Q = dot(cp, cp)
        nrm = Q.sqrt()
        chat = [t / nrm for t in cp]
        kappa = rho * sb * cb / nrm
        G = Geom(kappa, chat, ab_vertices(sinth) + verts, normals)
        Nt = cone_normals(scaled, ctil, names=names)
        G.scaled = lambda F, r: scaled_facets(F, r, kappa, chat, rho, sb, Q, nrm, D, Cb, Nt)
        return G

def scaled_facets(F, r, kappa, chat, rho, sb, Q, nrm, D, Cb, Nt):
    """Facet constraints of a paired polar fan, non-degenerate at u = 0.

    c = (0, r_n, ., ., .) has one L-perp entry 1/(2 sin u) on the axis e_D
    (D = e5 for type (i), e4 for type (ii)), the others C_j bounded.  On the
    VF sphere p_D / sin u = 1 - 2 r_n p_2 - 2 sum_{j != D} C_j p_j.  The map
    q -> q~ (D-entry divided by sin u) takes the cone K_u onto the cone K~_u
    of the scaled rays, with normals N~ (oriented towards c~, c_perp with its
    D-entry times sin u).  So N.p >= 0 for all facets iff N~.q~ >= 0, i.e.

        sum_{j != D} (N~_j - 2 N~_D C_j) p_j + N~_D - 2 N~_D r_n p_2 >= 0,

    multiplied by sin(theta)/cos(beta) = rho > 0:

        rho [sum_{j != D} M_j p_j + N~_D] - N~_D p_2/cos(beta) >= 0,
        p_2/cos(beta) = rho sb^2/Q - (r/sqrt Q)(s_D + 2 rho sb sum_{j != D} C_j s_j)

    (chat = c'/sqrt Q, c' = (0, sb, 2 rho sb cb C_3, ., .) with c'_D = cb).
    A facet with N~_D exactly 0 (the partner facet) has N~.q~ = N~.q and is
    kept in the plain form N~.p >= 0 (the factor rho would lose it at rho = 0).
    Returns [(name, g0, G)] with the constraint g0 + G.s >= 0."""
    out = []
    sidx = {0: 0, 2: 1, 3: 2, 4: 3}
    for name, N5 in Nt:
        Nt3 = {2: N5[2], 3: N5[3], 4: N5[4]}
        ND = Nt3[D]
        if ND.is_exact() and ND.is_zero():
            out.append(('facet~ ' + name, kappa * dot(N5, chat), [r * dot(N5, f) for f in F]))
            continue
        M = {j: Nt3[j] - 2 * ND * Cb[j] for j in Cb}
        g0 = rho * (sum((M[j] * kappa * chat[j] for j in M), ZERO) + ND) - ND * rho * sb * sb / Q
        G = []
        for k in (0, 2, 3, 4):
            t = rho * r * sum((M[j] * F[sidx[k]][j] for j in M), ZERO)
            extra = ONE if k == D else 2 * rho * sb * Cb[k] if k in Cb else ZERO
            G.append(t + ND * (r / nrm) * extra)
        out.append(('facet~ ' + name, g0, G))
    return out
