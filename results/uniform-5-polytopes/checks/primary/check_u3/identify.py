"""Step 3 (KNOWN, first half): which listed known polytope Q has a given
realisation as its vertex figure.

For Q (built from its definition in geom.py, centre 0) take a base vertex q0,
its exact radius R_Q = |q0| (an enclosure of an algebraic number) and its
local vertex set: the vertices within distance 2 of q0.

A realisation X (its star: v0, the vertex-figure points and the vertices
within distance 2 of v0 of every facet through v0) *embeds* in Q if an
isometry phi fixing the centre with phi(v0) = q0 maps every star point onto a
vertex of Q.  phi is determined by v0 and four vertex-figure points a1..a4
(a frame), whose images must be neighbours b1..b4 of q0 with the same
pairwise distances.  A frame image is excluded when some star point is
certified apart from every vertex of Q.  'NO' (every frame image excluded)
and 'NO-COUNT' (X has a different number of vertex-figure points from the
exact number of neighbours of q0) are certified; 'MATCH' (some frame image
puts every star point on an overlapping vertex enclosure) is not a proof of
anything and is used only as a consistency check.

Identification (exact, by elimination): if R_Q lies in the class interval
and every facet type of Q is in the input library (run.py checks this), the
star of Q at q0 is one of the realisations of the class (stage 2 lists every
signature; step 1 lists every realisation of each).  If every realisation of
the class but X is certified not to embed in Q, the star of Q is X.
"""
import itertools
import numpy as np
from mpmath import iv
from ivla import ZERO, ONE, dot, norm2, dist2, vsub, matvec, inverse, matmul, transpose, vmid
import geom
import tcert

def _disjoint(a, b):
    return a.b < b.a or b.b < a.a

def apart_from_vertices(y, vertices):
    """Certified distinct from every listed vertex, without a float cutoff.

    Coordinate disjointness cheaply excludes most vertices. Every
    remaining vertex is tested by interval squared distance. A possible
    identity returns False even for wide or badly conditioned images.
    """
    for v in vertices:
        if any((_disjoint(a, b) for a, b in zip(y, v))):
            continue
        if dist2(y, v).a <= 0:
            return False
    return True

class Known:
    """the listed known polytope Q: local vertex set and the neighbours of q0.
    nb: the local vertices whose distance enclosure contains 1 (every other
    one is certified at distance != 1), so the true neighbours are among them
    (a neighbour is at distance 1 < 2 from q0, so it is local) and len(nb) is
    a certified upper bound on their number.  n_exact: the exact number of
    neighbours when the model of Q's construction (tcert.model5) exhibits
    len(nb) vertices at exact distance 1, else None."""

    def __init__(self, name):
        self.name = name
        self.full = None
        V, idx = local_vertices(name, return_index=True)
        self.q0 = V[0]
        self.R2 = norm2(self.q0)
        self.R = iv.sqrt(self.R2)
        self.V = V
        self.Vf = np.array([[float(c.mid) for c in v] for v in V])
        nb = []
        for i in range(1, len(V)):
            d = dist2(V[0], V[i])
            if d.a <= 1 <= d.b:
                nb.append(i)
            elif not (d.a > 1 or d.b < 1):
                raise AssertionError((name, i))
        self.nb = nb
        loc = {g: k for k, g in enumerate(idx)}
        exact = {loc[g] for g in tcert.model5(name).nbrs()}
        if not exact <= set(nb):
            raise AssertionError(name)
        self.n_lower = len(exact)
        self.n_exact = len(nb) if len(exact) == len(nb) else None
        self.grid = {}
        for i, v in enumerate(self.Vf):
            self.grid.setdefault(tuple(np.floor(v * 2).astype(int)), []).append(i)

    def near(self, xf, tol=1e-06):
        c = np.floor(np.array(xf) * 2).astype(int)
        out = []
        for d in itertools.product((-1, 0, 1), repeat=5):
            for i in self.grid.get(tuple(c + np.array(d)), ()):
                if np.max(np.abs(self.Vf[i] - xf)) < tol:
                    out.append(i)
        return out

def local_vertices(name, rad2=4 + 1e-06, return_index=False):
    """Base first, then every possibly local vertex (interval rejection).

    The radius includes the template patch threshold 4+1e-9. A vertex
    whose squared-distance enclosure reaches the cutoff is retained.
    This verifies omitted vertices too, before any local width checks.
    """
    V = geom.polytope5(name)
    limit = iv.mpf(rad2)
    if not limit.a > 4 + iv.mpf('1e-9'):
        raise ValueError('local radius must contain the template patch')
    idx = [0] + [i for i in range(1, len(V)) if dist2(V[0], V[i]).a <= limit.b]
    if return_index:
        return ([V[i] for i in idx], idx)
    return [V[i] for i in idx]

def star_points(s):
    """v0, then the VF points, then every facet's vertices within distance 2
    of v0 (deduplicated by the separation lemma)."""
    pts = list(s.pts)
    fl = [vmid(p) for p in pts]
    for F in s.facets:
        for t in F.T.patch:
            if t == 0 or t in F.m:
                continue
            x = F.apply(F.T.V[t])
            xm = vmid(x)
            dup = False
            for k, ym in enumerate(fl):
                if sum(((a - b) ** 2 for a, b in zip(xm, ym))) < 0.25:
                    d = dist2(x, pts[k])
                    if d.b < 0.25:
                        dup = True
                        break
            if not dup:
                pts.append(x)
                fl.append(xm)
    return pts

def frame_choice(s):
    """v0 and four VF points with a well conditioned 5x5 matrix."""
    v0 = vmid(s.pts[0])
    ids = list(range(1, len(s.pts)))
    best = None
    for q in itertools.combinations(ids, 4):
        M = np.array([v0] + [vmid(s.pts[i]) for i in q])
        dv = abs(np.linalg.det(M))
        if best is None or dv > best[0]:
            best = (dv, q)
    return best[1]

def embed(s, Q, spts=None):
    """('NO-COUNT', n) if X's vertex figure has a number of points different
    from the exact number n of neighbours of q0 (or more points than the
    certified upper bound); ('NO', nframes) when every frame image is
    certified to fail; ('MATCH', maxdev) if some frame image puts every star
    point on an overlapping vertex enclosure (a consistency check only, not
    a proof that the star of q0 is the realisation: identification is by
    elimination, see the module docstring); else ('UNDECIDED', n)."""
    nX = len(s.pts) - 1
    if Q.n_exact is not None and nX != Q.n_exact:
        return ('NO-COUNT', Q.n_exact)
    if nX > len(Q.nb):
        return ('NO-COUNT', len(Q.nb))
    if spts is None:
        spts = star_points(s)
    fr = frame_choice(s)
    A = [s.pts[0]] + [s.pts[i] for i in fr]
    Af = np.array([vmid(a) for a in A])
    G = np.array([[np.dot(a - Af[0], b - Af[0]) for b in Af[1:]] for a in Af[1:]])
    Giv = None
    try:
        Ainv = inverse(transpose(A))
    except ZeroDivisionError:
        return ('UNDECIDED', 1)
    nb = Q.nb
    nframes = 0
    undecided = 0
    found = None
    for img in itertools.permutations(nb, 4):
        Bf = np.array([Q.Vf[i] for i in img])
        H = np.array([[np.dot(a - Q.Vf[0], b - Q.Vf[0]) for b in Bf] for a in Bf])
        discrepancy = np.abs(G - H)
        if np.max(discrepancy) > 1e-06:
            if Giv is None:
                delta = [vsub(v, A[0]) for v in A[1:]]
                Giv = [[dot(a, b) for b in delta] for a in delta]
            i, j = np.unravel_index(np.argmax(discrepancy), discrepancy.shape)
            gij = dot(vsub(Q.V[img[i]], Q.V[0]), vsub(Q.V[img[j]], Q.V[0]))
            if _disjoint(Giv[i][j], gij):
                continue
        nframes += 1
        B = [Q.V[0]] + [Q.V[i] for i in img]
        phi = matmul(transpose(B), Ainv)
        ok = True
        cert_fail = False
        maxdev = 0.0
        for p in spts:
            y = matvec(phi, p)
            try:
                cand = Q.near(vmid(y), 1e-06)
            except (OverflowError, ValueError):
                cand = []
            if cand:
                d = dist2(y, Q.V[cand[0]])
                if d.a <= 0:
                    maxdev = max(maxdev, float(d.b))
                    continue
            ok = False
            if apart_from_vertices(y, Q.V):
                cert_fail = True
            break
        if cert_fail:
            continue
        if ok:
            found = maxdev
            break
        undecided += 1
    if found is not None:
        return ('MATCH', found)
    if undecided:
        return ('UNDECIDED', undecided)
    return ('NO', nframes)
