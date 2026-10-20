"""Step 3 (KNOWN, second half): the star of v0 forces every neighbouring star.

At a neighbour w of v0 fix one facet F* of the star through v0 and w, with w
the template vertex t_w of F*.  Every congruence g with g(v0) = w and
g(star) containing F* maps some facet F of the star (of the same type) onto
F*; with g(centre) = centre it is
    g = [L_F* S | c_F*/|c_F*|] [L_F | c_F/|c_F|]^T,
S running over the template symmetries with S(base) = t_w (all of them: the
coset of the stabiliser found from frames).  g is *valid* when g(star)
contains every facet of the star through w: each facet through
u = g^-1(v0) must go onto a facet through w (same centre, and template map
differing by a symmetry of the template).  Pairs (F, S) failing this with a
certified mismatch are not valid; all others are kept.

For each kept g the star g(star) is written as an exact encoding: the star of
v0 seen from the frame of F composed with S^-1 (canon.encode).  If all kept g
give the same encoding, then (Build determinism, canon.py) all valid g give
the same star at w: equal encodings are an exact proof, intervals are used
only to discard.
"""
from mpmath import iv
from ivla import ZERO, dot, norm2, matmul, transpose, vmid
import canon


def frame5(F):
    cn = iv.sqrt(F.c2)
    # 5x5: columns = L columns, then unit centre
    return [list(F.L[r]) + [F.c[r] / cn] for r in range(5)]


def _overlap_vec(a, b):
    return all(not (x.b < y.a or y.b < x.a) for x, y in zip(a, b))


def _overlap_mat(A, B):
    return all(_overlap_vec(r1, r2) for r1, r2 in zip(A, B))


def perfect_matching(edges, nright):
    """Whether every left vertex has a distinct compatible right vertex.

    Edges express possible interval matches, not exact equalities. An
    augmenting path revisits earlier choices, so ambiguous overlaps never
    make a genuine facet bijection disappear through a greedy choice.
    """
    if len(edges) != nright:
        return False
    owner = [-1] * nright

    def augment(left, seen):
        for right in edges[left]:
            if right in seen:
                continue
            seen.add(right)
            if owner[right] < 0 or augment(owner[right], seen):
                owner[right] = left
                return True
        return False

    return all(augment(left, set()) for left in range(len(edges)))


def check(s, adj=None, max_report=3):
    if adj is None:
        adj = canon.facet_adjacency(s)
    through = {}
    for fi, F in enumerate(s.facets):
        for j, p in F.m.items():
            through.setdefault(p, []).append((fi, j))
    frames = [frame5(F) for F in s.facets]
    framesT = [transpose(A) for A in frames]
    result = {'neighbours': 0, 'unique': 0, 'valid_g': 0, 'tested_g': 0,
              'failures': [], 'no_valid': []}
    for w in range(1, len(s.pts)):
        result['neighbours'] += 1
        fs, tw = through[w][0]
        Fs = s.facets[fs]
        Ts = Fs.T
        mats, perms = Ts.trans[tw], Ts.trans_perm[tw]
        encs = set()
        nvalid = 0
        for fi, F in enumerate(s.facets):
            if F.type != Fs.type:
                continue
            for S, perm in zip(mats, perms):
                result['tested_g'] += 1
                inv0 = [j for j in F.T.nb if int(perm[j]) == 0]
                u = F.m[inv0[0]]
                LS = matmul(Fs.L, S)
                cn = iv.sqrt(Fs.c2)
                B = [list(LS[r]) + [Fs.c[r] / cn] for r in range(5)]
                g = matmul(B, framesT[fi])
                if not valid(s, g, u, w, through):
                    continue
                nvalid += 1
                frame = {F.m[j]: int(perm[j]) for j in F.T.nb}
                encs.add(canon.encode(s, fi, frame, adj))
        result['valid_g'] += nvalid
        if nvalid == 0:
            result['no_valid'].append(w)
        elif len(encs) == 1:
            result['unique'] += 1
        else:
            if len(result['failures']) < max_report:
                result['failures'].append((w, len(encs)))
            else:
                result['failures'].append((w, len(encs)))
    result['forced'] = (result['unique'] == result['neighbours'])
    return result


def valid(s, g, u, w, through):
    Fu = through[u]
    Fw = through[w]
    if len(Fu) != len(Fw):
        return False
    compatible = []
    for fi, _ in Fu:
        F = s.facets[fi]
        gc = [dot(row, F.c) for row in g]
        gL = matmul(g, F.L)
        possible = []
        for target, (fk, tk) in enumerate(Fw):
            H = s.facets[fk]
            if H.type != F.type:
                continue
            if not _overlap_vec(gc, H.c):
                continue
            M = matmul(transpose(H.L), gL)
            if any(_overlap_mat(M, S) for S in H.T.trans[tk]):
                possible.append(target)
        if not possible:
            return False
        compatible.append(possible)
    return perfect_matching(compatible, len(Fw))
