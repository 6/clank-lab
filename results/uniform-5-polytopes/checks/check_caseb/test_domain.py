"""G4 and integer-slice controls. No whole-family search or optimization."""
import copy
import unittest


import fans
import wcheck
from ia import I
import summary


class DomainControls(unittest.TestCase):
    def test_all_four_actual_gamma0_bounds(self):
        for kind in ("44", "333", "36", "ii"):
            with self.subTest(kind=kind):
                fan = fans.FanFamily(kind)
                cert = fans.certify_family_chart(fan, fan.free_box())
                self.assertLess(cert["Pi_abs_upper"], 1.41)

    def test_truncated_chart_rejected_for_every_family(self):
        for kind in ("44", "333", "36", "ii"):
            fan = fans.FanFamily(kind)
            fan.pi_box = (-1.0, 1.0)
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "truncates"):
                fan.free_box()

    def test_truncation_loses_a_strictly_admissible_point(self):
        # Exact binary inputs. theta=3/2, tau=0.18, Pi=33/32, f=(0,0.01).
        # Both n,m are finite in the continuous unbounded-family domain.
        fan = fans.FanFamily("44")
        fans.orient_family(fan)
        pi = I(33 / 32)
        g = fan.evaluate([I(0.18), I(1.5)], [pi, I(0), I(0.01)], 1)
        self.assertGreater(float(g.rad.lo), 0)
        self.assertTrue(all(float(v.lo) > 0 for v in g.facets))
        self.assertTrue(all(float(fans.dot5(g.p, u).hi) < 0.5 for _, u in g.verts))
        self.assertGreater(float(pi.lo), 1)
        # sqrt(rad) puts p exactly on the sphere. Re-evaluating in intervals
        # also encloses its unit norm and the rescaled VF equation.
        unit = fans.dot5(g.p, g.p)
        self.assertLessEqual(float(unit.lo), 1)
        self.assertGreaterEqual(float(unit.hi), 1)
        self.assertLessEqual(float((g.p[0] + pi - I(0.18) * (1 - I(0.01))).lo), 0)
        self.assertGreaterEqual(float((g.p[0] + pi - I(0.18) * (1 - I(0.01))).hi), 0)

    def test_corrupt_gamma_or_tau_rejected(self):
        fan = fans.FanFamily("36")
        original = fan.structure
        def corrupt(P):
            st = list(original(P))
            st[8] = (I(0), I(1))
            return tuple(st)
        fan.structure = corrupt
        with self.assertRaisesRegex(ValueError, "gamma0"):
            fan.free_box()
        fan = fans.FanFamily("44")
        fan.param_box = lambda: [(0.0, 0.25), (0.0, 2.0)]
        with self.assertRaisesRegex(ValueError, "tau"):
            fan.free_box()

    def test_36_integer_slices_and_endpoints(self):
        count = 0
        for rest, upper in fans.BOUNDED_LIMITS.items():
            for m in range(17, upper + 1):
                f = fans.FanBounded(m, rest)
                d = fans.parameter_domain(f)
                self.assertEqual(d["m"]["kind"], "integer_slice")
                self.assertEqual(d["m"]["value"], m)
                self.assertEqual(d["n"]["kind"], "real")
                count += 1
            for bad in (16, upper + 1, 17.0, 17.5, True, "17"):
                with self.subTest(rest=rest, m=bad), self.assertRaises(ValueError):
                    fans.FanBounded(bad, rest)
        self.assertEqual(count, 36)
        actual = {(f.m, f.config[1:]) for _, f in wcheck.build_fans([])
                  if isinstance(f, fans.FanBounded)}
        expected = {(m, rest) for rest, upper in fans.BOUNDED_LIMITS.items()
                    for m in range(17, upper + 1)}
        self.assertEqual(actual, expected)

    def test_generic_configuration_cannot_smuggle_fractional_m(self):
        for m in (17.0, 17.5):
            with self.assertRaisesRegex(ValueError, "integer"):
                fans.FanTypeI((m, 3, 7))

    def test_restricted_point_is_integer(self):
        f = fans.FanBounded(38, (3, 7))
        for n in (38.0, 38.5, 16, True):
            with self.assertRaises(ValueError):
                f.restrict_n(n)
        f.restrict_n(38)
        self.assertEqual(fans.parameter_domain(f)["n"], {"kind": "integer_point", "value": 38})

    def test_summary_rejects_real_m_overclaim(self):
        # Scope acceptance is checked before inspecting numerical verdicts.
        row = {"fan": "(i)(17,3,7)", "parameter_domain":
               fans.parameter_domain(fans.FanBounded(17, (3, 7)))}
        summary.validate_domains([row])
        for domain in (None, {"m": {"kind": "real", "min": 17, "max": 41}}):
            corrupt = copy.deepcopy(row)
            corrupt["parameter_domain"] = domain
            with self.assertRaisesRegex(ValueError, "integer slice"):
                summary.validate_domains([corrupt])
        bad = copy.deepcopy(row)
        bad["parameter_domain"]["n"] = {"kind": "integer_point", "value": 17}
        with self.assertRaisesRegex(ValueError, "full n domain"):
            summary.validate_domains([bad])
        bad = copy.deepcopy(row)
        bad["fan"] = "(i)(17.5,3,7)"
        bad["parameter_domain"]["m"]["value"] = 17.5
        with self.assertRaisesRegex(ValueError, "integer"):
            summary.validate_domains([bad])
        row["fan"] = "(i)(17,3,7)@n=17"
        with self.assertRaisesRegex(ValueError, "integer point"):
            summary.validate_domains([row])
        row["parameter_domain"]["n"] = {"kind": "integer_point", "value": 17}
        summary.validate_domains([row])


if __name__ == "__main__":
    unittest.main()
