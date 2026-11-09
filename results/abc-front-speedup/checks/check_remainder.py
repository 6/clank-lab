#!/usr/bin/env python3
"""Check Taylor remainder propagation against an exactly integrable flow."""
import check_arb as c
from flint import arb, ctx


class SineFlow:
    # x' = cos y, y' = 1, z' = 0; x(t) = x(0) + sin(y(0)+t) - sin(y(0)).
    need = (False, True, False)

    def F(self, u):
        _, cy = c.jet_sincos(u[1])
        one = c.Jet.const(arb(1), u[0].nv, u[0].D)
        return [cy, one, one * 0]

    def coef(self, S, C, k, u0):
        one = c.Jet.const(arb(1), u0[0].nv, u0[0].D)
        return [C[1][k], one if k == 0 else one * 0, one * 0]


def main():
    ctx.prec = 256
    h = arb(1) / 32
    xi, eta = (c.Jet.var(i, 2, 3) for i in range(2))
    zero = c.Jet.const(arb(0), 2, 3)
    expected = [xi + c.jet_sincos(eta + h)[0] - c.jet_sincos(eta)[0],
                eta + h, zero]
    # Order 2 leaves a nonzero cubic remainder. The erroneous extra h excludes
    # sin(h) in the ordinary step; order 36 would make this regression too small.
    for length, scale in ((h, None), (arb(1), c.Jet.const(h, 2, 3))):
        end = c.step(SineFlow(), [xi, eta, zero], length, 2, scale=scale)['end']
        for actual, exact in zip(end, expected):
            assert all(a.contains(e) for a, e in zip(actual.c, exact.c)), \
                'Taylor step excludes the exact solution or its degree-3 jet'
    print('ok: ordinary and rescaled Taylor steps enclose the exact sine flow and its degree-3 jet')


if __name__ == '__main__':
    main()
