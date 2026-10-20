"""Solved controls and semantic corruptions for the new closure engine."""
import unittest
import json
from fractions import Fraction
from pathlib import Path
import sympy as sp
from flint import arb
from arithmetic import evaluate, endpoints, Undecided, decimal_bounds, hull
from stage1 import Edge, Solver, enumerate_cycles, prove_flat, canonical, certify_monotonicity

Q=sp.Rational


def edge(name,r2,c):
    return Edge(name,3,'tet','tet',evaluate(r2),evaluate(c),r2,c)


class Controls(unittest.TestCase):
    def test_derivative_identity(self):
        A, B, c, u = sp.symbols('A B c u', positive=True)
        d = sp.sqrt(A*B)
        denom = (1-A*u)*(1-B*u)
        f = (c-d*u)/sp.sqrt(denom)
        numerator = -d+c*(A+B)/2+u*(d*(A+B)/2-c*A*B)
        self.assertEqual(sp.simplify(sp.diff(f,u)*denom**sp.Rational(3,2)-numerator), 0)

    def test_monotonicity_whole_domain(self):
        certify_monotonicity(arb(4), arb(1), arb(5), arb(0))
        # Constant term negative, derivative changes sign before the endpoint.
        with self.assertRaises(Undecided):
            certify_monotonicity(arb(4), arb(1), arb(5), evaluate(Q(7,10)))
        # Equality at the endpoint does not establish a strict bound.
        with self.assertRaises(Undecided):
            certify_monotonicity(arb(4), arb(1), arb(5), evaluate(Q(10,17)))
        with self.assertRaises(Undecided):
            certify_monotonicity(arb(4), arb(1), arb(5), evaluate(Q(9,10)))
        for A,B,T in [(0,1,5),(4,0,5),(4,1,4),(4,1,1)]:
            with self.subTest(domain=(A,B,T)), self.assertRaises(Undecided):
                certify_monotonicity(arb(A), arb(B), arb(T), arb(0))

    def test_recorded_word_derivative_bounds(self):
        # Small operand check; full library regeneration remains verify_library's job.
        library = json.loads((Path(__file__).parent/'library.json').read_text())
        def interval(pair):
            return hull(*map(Fraction, pair))
        cells = {name: interval(row['bracket'])
                 for name,row in library['cell_radius_squared'].items()}
        count = 0
        for row in library['records']:
            r2 = interval(row['radius_squared_bracket'])
            for word in row['words']:
                rho2 = 1/(4*(arb.pi()/word['p']).sin()**2)
                certify_monotonicity(cells[word['A']]-rho2, cells[word['B']]-rho2,
                                     r2-rho2, interval(word['cos_alpha_bracket']))
                count += 1
        self.assertEqual(count, 558)

    def setUp(self):
        self.simplex=edge('simplex',Q(2,5),Q(1,4))
        self.cross=edge('cross',Q(1,2),Q(-1,2))
        self.large=edge('large',Q(3,4),Q(-4,5))
        self.s=Solver([self.simplex,self.cross,self.large],
                      {'tet':evaluate(Q(3,8))},{'tet':Q(3,8)})

    def test_simplex_triangle(self):
        result=self.s.solve(3,(('simplex','tet'),)*3)
        self.assertEqual(result['status'],'ROOT')
        target=evaluate(Q(5,12)).sqrt()
        lo,hi=map(arb,result['R'])
        self.assertTrue(lo<target and target<hi)

    def test_four_facets(self):
        result=self.s.solve(3,(('simplex','tet'),)*4)
        target=evaluate(Q(1,2)).sqrt()
        lo,hi=map(arb,result['R'])
        self.assertTrue(lo<target and target<hi)

    def test_flat(self):
        self.assertEqual(self.s.solve(3,(('cross','tet'),)*3)['status'],'FLAT')
        self.assertTrue(prove_flat((sp.Integer(0),)*4))

    def test_degenerate(self):
        self.assertEqual(self.s.solve(3,(('simplex','tet'),)*2+(('cross','tet'),))['status'],
                         'DEGENERATE')

    def test_no_root(self):
        self.assertEqual(self.s.solve(3,(('simplex','tet'),)*2+(('large','tet'),))['status'],
                         'NO_ROOT')

    def test_enumeration(self):
        self.assertEqual([len(c) for p,c in enumerate_cycles([self.simplex])],[3,4])

    def test_flat_corruption(self):
        # Angle changed while retaining an apparent flat claim.
        with self.assertRaises(Undecided):
            prove_flat((Q(-1,2),Q(-1,2),Q(-1,2)+Q(1,10**20)))

    def test_input_corruption(self):
        # A facet smaller than its cells cannot feed the proof.
        bad=edge('bad',Q(1,3),Q(1,4))
        solver=Solver([bad],{'tet':evaluate(Q(3,8))},{'tet':Q(3,8)})
        with self.assertRaises(Undecided):
            solver.solve(3,(('bad','tet'),)*3)

    def test_unknown_sign_fails(self):
        with self.assertRaises(Undecided):
            self.s.algebraic_sign(arb(0,1),Q(1,100))

    def test_duplicate_word_fails(self):
        with self.assertRaises(ValueError):
            Solver([self.simplex,self.simplex],{}, {})


if __name__=='__main__':
    unittest.main()
