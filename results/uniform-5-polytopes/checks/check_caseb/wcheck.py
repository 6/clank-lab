"""Independent checker for the Case B wedge lemma (W).

For every fan of the CASEB.md list and all n >= 17 (including n = oo; for the
unbounded paired families also all m >= 17 including m = oo) it certifies,
with the interval branch-and-bound of bnb.py. Bounded paired families
use only integer m slices (17..41, 17..23, 17, 17..19 respectively);
the seven exceptional restrictions use the integer point n=m:

  (V)  for every fan vertex u and every p in S:  p.u > -cos(2pi/17)
       (no long VF-edge from a non-fan vertex to a fan vertex);
  (D)  for every p in S:  p.u_dir > sin(pi/17) |u_dir|  for one direction
       u_dir (fixed per fan / per parameter): then p.p' > -cos(2pi/17) for
       all p, p' in S, because (p + p').u_dir <= |p + p'| |u_dir| and
       |p + p'|^2 = 2 + 2 p.p';
  (F)  pairs of fan vertices other than e = ab and the partner edge are
       shorter than 2cos(pi/17) (type (i) diagonals reported separately).

S = points of the VF sphere on the inner side of every fan facet and at
distance >= 1 from every fan vertex.  Usage:
  python3 wcheck.py [--only NAME,...] [--quick] [--corrupt KIND] [--out FILE]
"""
import argparse
import json
import sys
import time

import numpy as np
from mpmath import iv, mpf

import bnb
import fans
import ia
import p1check
import partner
import witness
from ia import I

KAP = ia.const(fans.KAPPA)


# --------------------------------------------------------------------------
def cap_direction(S, iters=4000):
    """maximise min_p p.u over unit u (float heuristic, used only to choose
    the direction; the certificate re-checks it rigorously)."""
    u = S.mean(0)
    u /= np.linalg.norm(u)
    best, bu, step = (S @ u).min(), u, 0.05
    for _ in range(iters):
        i = (S @ u).argmin()
        u = u + step * S[i]
        u /= np.linalg.norm(u)
        m = (S @ u).min()
        if m > best:
            best, bu = m, u
        step *= 0.999
    return np.round(bu * 1024) / 1024     # exact binary floats


def sample_S(fan, P, n=150000, seed=1):
    """Non-proof samples used only to choose a direction for interval checking."""
    rng = np.random.default_rng(seed)
    out = []
    for sign in (1, -1):
        F = [I(rng.uniform(lo, hi, n)) for lo, hi in fan.free_box()]
        PP = [I(np.full(n, x)) for x in P]
        g = fan.evaluate(PP, F, sign)
        ok = g.rad.lo >= 0
        for fv in g.facets:
            ok &= fv.lo >= 0
        for _, u in g.verts:
            ok &= fans.dot5(g.p, u).hi <= 0.5
        out.append(np.stack([np.broadcast_to(c.mid, (n,)) for c in g.p], axis=1)[ok])
    return np.concatenate(out)


# --------------------------------------------------------------------------
def build_fans(p1_list, corrupt=None):
    L = []
    for c in p1_list:
        L.append(("unpaired", fans.FanTypeI(c)))
    for q in range(3, 17):
        L.append(("unpaired", fans.FanTypeII(q)))
    for q in [(3, 3), (3, 4), (3, 5)]:
        L.append(("unpaired", fans.FanTypeIII(*q)))
    bounded = [((m, 3, 7), m) for m in range(17, 42)] + [((m, 3, 8), m) for m in range(17, 24)] + \
              [((17, 3, 9), 17)] + [((m, 4, 5), m) for m in range(17, 20)]
    for c, m in bounded:
        f = fans.FanBounded(m, c[1:])
        L.append(("paired", f))
    for k in ["44", "333", "36", "ii"]:
        L.append(("paired", fans.FanFamily(k)))
    return L


def setup(fan):
    """orientation and pair-test direction."""
    if isinstance(fan, fans.FanTypeIII):
        # locate the (narrow) feasible cphi window by a float scan
        c = np.linspace(0.001, 0.999, 200001)
        ok, cc, sp, w, h, C, s, t = fan.geometry([I(c)])
        hq = np.where(-w[0].mid > 0, (w[1].mid / c - 1) / np.maximum(-w[0].mid, 1e-300), -1)
        good = ok & (hq >= fan.h17.lo) & (hq <= fan.hmax.hi)
        cs = c[good]
        fans.orient_iii(fan, float(np.median(cs)))
        good_o, nfeas = fans.check_orient_iii(fan)
        if not (good_o):
            raise AssertionError()
        S = np.concatenate([sample_S(fan, [x]) for x in (cs.min(), np.median(cs), cs.max())])
        fan.u = tuple(float(x) for x in cap_direction(S)) if len(S) else (0.0, 0.0, 0.0, 1.0, 0.0)
        return f"cphi window [{cs.min():.6f}, {cs.max():.6f}], orientation {fan.orient}"
    if isinstance(fan, fans.FanTypeII):
        S = np.concatenate([sample_S(fan, [x]) for x in (0.0, 0.09, 0.18)])
        fan.u = tuple(float(x) for x in cap_direction(S)) if len(S) else (0.0, 0.0, 0.0, 1.0, 0.0)
        return f"u_dir {fan.u}"
    if isinstance(fan, fans.FanFamily):
        fans.orient_family(fan)
        if not (fans.check_orient_family(fan)):
            raise AssertionError()
        return f"orientation {fan.orient}"
    return ""


def vertex_pairs(fan):
    """(F): fan-vertex pairs other than e and the partner edge: u.u' > -kappa
    over the whole parameter box (interval bisection of the parameters)."""
    pb = fan.param_box()
    P0 = [I(np.array([lo]), np.array([hi])) for lo, hi in pb]
    names = [n for n, _ in fan.vertices(P0)]
    skip = {frozenset(("a", "b"))}
    if isinstance(fan, fans.FanFamily):
        skip.add(frozenset(("z1", "z2") if fan.kind == "ii" else ("x1", "x2")))
    elif getattr(fan, "partner", None):
        skip.add(frozenset(fan.partner))
    diag = set()
    if isinstance(fan, fans.FanTypeI) and len(fan.x) >= 4:
        k = len(fan.x)
        for i in range(k):
            for j in range(i + 2, k):
                if not (i == 0 and j == k - 1):
                    diag.add(frozenset((f"x{i+1}", f"x{j+1}")))
    if isinstance(fan, fans.FanFamily) and fan.kind == "333":
        diag |= {frozenset(("x1", "x3")), frozenset(("x2", "x4"))}
    pairs = [(a, b) for i, a in enumerate(names) for b in names[i + 1:] if frozenset((a, b)) not in skip]
    # parameter grid fine enough; refine adaptively
    lo = np.array([[l for l, _ in pb]])
    hi = np.array([[h for _, h in pb]])
    res = {}
    for a, b in pairs:
        L, H = lo.copy(), hi.copy()
        worst = np.inf
        ok = True
        for depth in range(40):
            P = [I(L[:, j], H[:, j]) for j in range(L.shape[1])]
            V = dict(fan.vertices(P))
            d = fans.dot5(V[a], V[b])
            if isinstance(fan, fans.FanTypeIII):
                okp = fan.geometry(P)[0]
            else:
                okp = np.ones(len(L), bool)
            und = (d.lo <= -KAP.lo) & okp
            if not und.any():
                break
            L, H = L[und], H[und]
            sc = hi - lo
            sc = np.where(sc < 1e-9, np.inf, sc)
            w = (H - L) / sc
            k = w.argmax(1)
            idx = np.arange(len(L))
            m = 0.5 * (L[idx, k] + H[idx, k])
            H1 = H.copy(); H1[idx, k] = m
            L2 = L.copy(); L2[idx, k] = m
            L, H = np.concatenate([L, L2]), np.concatenate([H1, H])
            if len(L) > 200000:
                ok = False
                break
        else:
            ok = False
        if und.any():
            ok = False
        # float estimate of the largest length over a parameter grid
        if isinstance(fan, fans.FanTypeIII):
            cg = np.linspace(pb[0][0], pb[0][1], 400001)
            okc = fan.geometry([I(cg)])[0]
            grid = cg[okc][:, None]
        else:
            grid = np.stack(np.meshgrid(*[np.linspace(l, h, 129) for l, h in pb], indexing="ij"), -1).reshape(-1, len(pb))
        Pg = [I(grid[:, j]) for j in range(len(pb))]
        Vg = dict(fan.vertices(Pg))
        okg = fan.geometry(Pg)[0] if isinstance(fan, fans.FanTypeIII) else np.ones(len(grid), bool)
        dg = np.broadcast_to(fans.dot5(Vg[a], Vg[b]).mid, (len(grid),))[okg]
        maxlen = float(np.sqrt(max(0.0, 2 - 2 * dg.min()))) if len(dg) else None
        res[f"{a}{b}"] = {"ok": ok, "max_len_approx": None if maxlen is None else round(maxlen, 6), "diagonal": frozenset((a, b)) in diag}
    return res


PAIR_BUDGET = 150_000_000


def check_fan(fan, quick=False):
    """V tests on both branches; the pair condition by the dual-tree test P on
    the branch classes (+,+) and (+,-) (every fan is symmetric under
    e2 -> -e2: a <-> b, x <-> y, L-perp fixed, so (-,-) ~ (+,+), and (-,+) is
    (+,-) with p and p' exchanged); the direction test D (+ branch) is run
    and reported as a second sufficient condition."""
    t0 = time.process_time()
    info = setup(fan)
    P0 = [I(np.array([lo]), np.array([hi])) for lo, hi in fan.param_box()]
    vnames = [n for n, _ in fan.vertices(P0)]
    out = {"fan": fan.name, "setup": info, "tests": {},
           "parameter_domain": fans.parameter_domain(fan)}
    vok = True
    for sign in (1, -1):
        for name in vnames:
            r = bnb.run(fan, bnb.obj_vertex(name), sign)
            out["tests"][f"V:{name}:{'+' if sign > 0 else '-'}"] = r
            vok &= r["ok"]
    # direction test (a second, independent sufficient condition; reported)
    r = bnb.run(fan, bnb.obj_udir(), 1)
    out["tests"]["D:+"] = r
    out["direction_test"] = "CERTIFIED" if r["ok"] else "not sufficient"
    # pair condition proper: dual-tree test on the classes (+,+), (+,-)
    pok = True
    for sg in ((1, 1), (1, -1)):
        rp = bnb.run_pair(fan, sg, max_boxes=PAIR_BUDGET)
        out["tests"][f"P:{sg[0]:+d}{sg[1]:+d}"] = rp
        pok &= rp["ok"]
    if not pok and not any("witness" in out["tests"][k] for k in out["tests"] if k.startswith("P:")):
        out["pair_witness"] = witness.pair_witness(fan)
    out["vertex_pairs"] = vertex_pairs(fan)
    vp_ok = all(v["ok"] for v in out["vertex_pairs"].values() if not v["diagonal"])
    for t in out["tests"].values():
        t["cpu"] = round(t["cpu"], 3)
    out["boxes"] = sum(t["boxes"] for t in out["tests"].values())
    out["cpu"] = round(time.process_time() - t0, 3)
    out["verdict"] = "CERTIFIED" if (vok and pok and vp_ok) else "FAILED"
    out["V_ok"], out["P_ok"], out["F_ok"] = vok, pok, vp_ok
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="")
    ap.add_argument("--p1", default="p1_closable.txt")
    ap.add_argument("--out", default="w_results.jsonl")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--supplementary", action="store_true",
                    help="run the type-(i) configurations EXCLUDED by (P1) instead (not needed by the reduction)")
    args = ap.parse_args()
    p1_list = [tuple(map(int, l.split(","))) for l in open(args.p1) if l.strip()]
    if args.supplementary:
        L = [("excluded-by-P1", fans.FanTypeI(c)) for c in p1_list]
    else:
        L = build_fans(p1_list)
    only = set(x for x in args.only.split(";") if x)
    with open(args.out, "w") as fo:
        for kind, fan in L:
            if only and fan.name not in only:
                continue
            todo = [fan]
            while todo:
                fan = todo.pop()
                r = check_fan(fan, quick=args.quick)
                r["kind"] = kind
                if r["verdict"] == "FAILED" and isinstance(fan, fans.FanTypeI) and getattr(fan, "m", None) \
                        and fan.pbox is None:
                    d1, allowed = partner.allowed(fan.m, fan.config[1:])
                    r["partner_filter"] = {"delta_c1(m)": d1, "allowed": [list(map(str, a)) for a in allowed]}
                    if allowed == [(tuple(fan.config[1:]), fan.m)]:
                        g = fans.FanBounded(fan.m, fan.config[1:])
                        g.restrict_n(fan.m)
                        todo.append(g)
                    else:
                        r["partner_filter"]["note"] = "other (c2, n) allowed: not handled"
                fo.write(json.dumps(r) + "\n")
                fo.flush()
                bad = [k for k, v in r["tests"].items() if not v["ok"] and not k.startswith("D")]
                print(f"{fan.name:26s} {r['verdict']:9s} boxes={r['boxes']:>11d} cpu={r['cpu']:9.2f}s"
                      + (f"  failing={bad}" if bad else ""), flush=True)


if __name__ == "__main__":
    main()
