import ABC.Twist

/-!
# Certified facts (checked import)

Both checkers certify these facts about the fixed point `p` of the first-crossing map
(`checks/` in the result's folder). Checker 2 (`checks/check_arb.py`, python-flint) proves them for the unique zero
of `P − id` in a box of radius `2⁻¹⁰⁰` inside `X`. Checker 1 (`checks/bnf.cpp`, CAPD 6.1.0) proves
them for the unique zero of `P − id` in `X`. The numbers are those of `checks/cert.txt`, and
`checks/cert_import.py` checks that they match the certificate. The twist is certified
nonzero in raw coordinates by checker 1 and in the coordinates `Φ` by checker 2; the two are
equivalent by `ABC.S4.twist_phi_iff`. `z′ ≥ 1.92` is the weaker of
the two certified lower bounds: 1.9215 (CAPD, all of `X`) and 1.9378 (arb, its box run
`[box X', D=3]`).

CAPD's `computePlanarEllipticNormalForm` is labelled "area-preserving", and the raw map `P`
preserves `V_z dx∧dy`, not `dx∧dy`. Its coded formula uses only `λ̄ = 1/λ`, which holds at the
fixed point (`det DP(p) = V_z(p)/V_z(P p) = 1`), and returns `a1 = −iβ/λ` with `β` the
`birkhoffBeta` of `ABC.Twist` for its eigenvector; so "Re a1 excludes 0" gives
`TwistNonzero retMap p`. Checker 2's twist, in the coordinates `Φ`, gives it independently
through `ABC.S4.twist_phi_iff`.
-/

open Set

namespace ABC

/-- The certified facts at a point `p`. -/
structure CertFacts (p : E 2) : Prop where
  mem_box : p ∈ certBox
  orbit : ∃ γ : ℝ → E 3, ∃ T : ℝ, IsOrbit γ ∧ γ 0 = lift p 0 ∧
    32352 / 10000 ≤ T ∧ T ≤ 32354 / 10000 ∧ γ T = lift p (2 * Real.pi) ∧
    ∀ t ∈ Icc 0 T, 192 / 100 ≤ abcField (γ t) 2
  trace : ∃ M : E 2 →L[ℝ] E 2, HasFDerivAt retMap M p ∧
    -19650 / 10000 ≤ LinearMap.trace ℝ (E 2) (M : E 2 →ₗ[ℝ] E 2) ∧
    LinearMap.trace ℝ (E 2) (M : E 2 →ₗ[ℝ] E 2) ≤ -19640 / 10000
  twist : TwistNonzero retMap p

/-- **Certificate axiom** (computer-assisted, two independent checkers). -/
axiom Cert.fixed_point : ∃ p, CertFacts p

end ABC
