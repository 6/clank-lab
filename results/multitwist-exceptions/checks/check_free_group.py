#!/usr/bin/env python3
"""Checker A for the finite facts F0-F4 of the paper (free-group model).

Model: S_{0,5} is the disc with four punctures 1..4 on a line, the boundary
being the fifth hole. pi_1 is free on x1..x4 (x_i a loop around puncture i,
x1x2x3x4 the boundary). Mapping classes act on conjugacy classes; a simple
closed curve is its conjugacy class up to inversion. Half twists act by the
Artin automorphisms
    s_i: x_i -> x_i x_{i+1} x_i^-1,  x_{i+1} -> x_i,  x_j -> x_j otherwise,
and the Dehn twist about the round curve around punctures {i..j} is the full
twist of the strands i..j: s_i^2 for two strands, (s_i s_{i+1})^3 for three.

Words are tuples of nonzero ints: g means x_g, -g means x_g^-1.
Exact; no floating point; imports nothing but the standard library.
"""
import argparse
import json
import sys


def reduce(w):
    out = []
    for g in w:
        if out and out[-1] == -g:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def inverse(w):
    return tuple(-g for g in reversed(w))


def cyclic_reduce(w):
    w = list(reduce(w))
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return tuple(w)


def curve_key(w):
    """Canonical form of a conjugacy class up to inversion."""
    w = cyclic_reduce(w)
    if not w:
        return ()
    cands = []
    for v in (w, cyclic_reduce(inverse(w))):
        cands.extend(v[i:] + v[:i] for i in range(len(v)))
    return min(cands)


class Aut:
    """An endomorphism of F_4 given by the images of x1..x4."""

    def __init__(self, images):
        self.img = {g: reduce(images[g]) for g in (1, 2, 3, 4)}

    def __call__(self, w):
        out = []
        for g in w:
            out.extend(self.img[g] if g > 0 else inverse(self.img[-g]))
        return reduce(out)

    def __mul__(self, other):
        """(self * other)(w) = self(other(w)): apply other first."""
        return Aut({g: self(other.img[g]) for g in (1, 2, 3, 4)})

    def __eq__(self, other):
        return self.img == other.img

    def power(self, n):
        assert n >= 0
        result = IDENTITY
        for _ in range(n):
            result = self * result
        return result


def _gen(i):
    images = {g: (g,) for g in (1, 2, 3, 4)}
    images[i] = (i, i + 1, -i)
    images[i + 1] = (i,)
    return Aut(images)


def _gen_inv(i):
    images = {g: (g,) for g in (1, 2, 3, 4)}
    images[i] = (i + 1,)
    images[i + 1] = (-(i + 1), i, i + 1)
    return Aut(images)


IDENTITY = Aut({g: (g,) for g in (1, 2, 3, 4)})
S = {i: _gen(i) for i in (1, 2, 3)}
S_INV = {i: _gen_inv(i) for i in (1, 2, 3)}
for i in (1, 2, 3):
    assert S[i] * S_INV[i] == IDENTITY and S_INV[i] * S[i] == IDENTITY


def _register(a, b):
    assert a * b == IDENTITY and b * a == IDENTITY


# Dehn twists about the five curves.
T = {}
T_INV = {}
T["a"], T_INV["a"] = S[1] * S[1], S_INV[1] * S_INV[1]
T["d"], T_INV["d"] = S[2] * S[2], S_INV[2] * S_INV[2]
T["c"], T_INV["c"] = S[3] * S[3], S_INV[3] * S_INV[3]
T["Cp"] = (S[1] * S[2]).power(3)
T_INV["Cp"] = (S_INV[2] * S_INV[1]).power(3)
T["C"] = (S[2] * S[3]).power(3)
T_INV["C"] = (S_INV[3] * S_INV[2]).power(3)
for k in T:
    _register(T[k], T_INV[k])

CURVES = {
    "a": (1, 2),        # around punctures {1,2}
    "d": (2, 3),        # around {2,3}
    "c": (3, 4),        # around {3,4}
    "Cp": (1, 2, 3),    # C': around {1,2,3}, i.e. around {4,5}
    "C": (2, 3, 4),     # C: around {2,3,4}, i.e. around {1,5}
}
PENTAGON = ["a", "d", "c", "Cp", "C"]  # cyclic order


def same_curve(u, v):
    return curve_key(u) == curve_key(v)


def tw(name, n):
    return T[name].power(n) if n >= 0 else T_INV[name].power(-n)


def check(curves, kmax, log):
    ok = True

    def expect(cond, what):
        nonlocal ok
        log.append(("PASS " if cond else "FAIL ") + what)
        if not cond:
            ok = False

    # F0: each twist fixes its own curve (sanity of the model and of the input).
    for n in PENTAGON:
        expect(same_curve(T[n](curves[n]), curves[n]), f"F0 T_{n} fixes {n}")
    # F1: the pentagon pattern. For essential curves u, v:
    # T_u(v) = v  iff  i(u, v) = 0   (Farb-Margalit, Prop. 3.2).
    for x in range(5):
        for y in range(5):
            if x == y:
                continue
            u, v = PENTAGON[x], PENTAGON[y]
            adjacent = (x - y) % 5 in (1, 4)
            fixed = same_curve(T[u](curves[v]), curves[v])
            expect(fixed != adjacent,
                   f"F1 i({u},{v}) {'!= 0' if adjacent else '= 0'}")
    # F1': the five curves are pairwise distinct.
    keys = [curve_key(curves[n]) for n in PENTAGON]
    expect(len(set(keys)) == 5, "F1' five distinct curves")
    # F2: disjoint twists T_a, T_c commute (as automorphisms).
    expect(T["a"] * T["c"] == T["c"] * T["a"], "F2 T_a T_c = T_c T_a")
    # F3/F4: for each k, eps, the two exceptional members and the filling.
    for k in range(1, kmax + 1):
        f_k = tw("a", k) * T["d"]
        for eps in (1, -1):
            t = T["a"] * tw("c", eps)

            def member(j):
                return t.power(j) * f_k if j >= 0 else \
                    (T_INV["a"] * tw("c", -eps)).power(-j) * f_k

            m0, mk = member(0), member(-k)
            expect(m0 == tw("a", k) * T["d"], f"F3 k={k} eps={eps} t^0 f_k = T_a^k T_d")
            expect(mk == tw("c", -eps * k) * T["d"],
                   f"F3 k={k} eps={eps} t^-k f_k = T_c^(-eps k) T_d")
            expect(same_curve(m0(curves["Cp"]), curves["Cp"]),
                   f"F3 k={k} eps={eps} j=0 member fixes C'")
            expect(same_curve(mk(curves["C"]), curves["C"]),
                   f"F3 k={k} eps={eps} j=-k member fixes C")
        fa = f_k(curves["a"])
        expect(not same_curve(T["a"](fa), fa), f"F4 k={k} i(a, f_k(a)) != 0")
        expect(not same_curve(T["c"](fa), fa), f"F4 k={k} i(c, f_k(a)) != 0")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=12)
    ap.add_argument("--curves", help="JSON file overriding curve words (corruption tests)")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    curves = dict(CURVES)
    if args.curves:
        with open(args.curves) as fh:
            curves.update({k: tuple(v) for k, v in json.load(fh).items()})
    log = []
    ok = check(curves, args.kmax, log)
    fails = [l for l in log if l.startswith("FAIL")]
    if not args.quiet:
        for l in fails[:20]:
            print(l)
    print(json.dumps({"checker": "A-free-group", "kmax": args.kmax,
                      "checks": len(log), "failures": len(fails),
                      "verdict": "ACCEPT" if ok else "REJECT"}))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
