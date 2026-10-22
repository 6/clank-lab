import EKG.PrimeEstimates

/-! Exact P3 interfaces from `tail/discharge/INPUTS.md`. Real prime counts
include the integer endpoint, as in `Statement/TheoremT.lean`. -/
namespace EKG3

noncomputable def p3C : ℝ := 103883 / 100000
noncomputable def p3A : ℝ := 92129 / 100000

def primesBelow256 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
   59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
   191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

noncomputable def p3F (x : ℝ) : ℝ :=
  x / Real.log x *
    (1 + 1 / Real.log x + 2 / Real.log x ^ 2 + 24 / Real.log x ^ 3)

noncomputable def p3J : ℝ :=
  EKG.realPrimeCount 256 - Chebyshev.theta 256 / Real.log 256 +
    p3C * (256 / Real.log 256 - p3F 256)

noncomputable def R3 (x : ℝ) : ℝ :=
  p3C * Real.sqrt x + (p3C / Real.log 2) * x ^ (1 / 3 : ℝ) * Real.log x

noncomputable def U3 (x : ℝ) : ℝ := p3C * p3F x + p3J

noncomputable def L3 (x : ℝ) : ℝ :=
  max 0 ((p3A * x - 5 * Real.log x + 5 - R3 x) / Real.log x)

/-- The exact finite list, its real counting convention below 256, the
R3 remainder, and both pi bounds on the entire real domain x ≥ 256.
This definition does not assert that its analytic inequalities are proved. -/
def PiBoundsP3 : Prop :=
  (∀ n : ℕ, n ∈ primesBelow256 ↔ n.Prime ∧ n < 256) ∧
  (∀ x : ℝ, 0 ≤ x → x < 256 →
    EKG.realPrimeCount x =
      ((primesBelow256.filter (fun p => p ≤ ⌊x⌋₊)).length : ℝ)) ∧
  (∀ x : ℝ, 256 ≤ x →
    Chebyshev.psi x - Chebyshev.theta x ≤ R3 x ∧
    L3 x ≤ EKG.realPrimeCount x ∧ EKG.realPrimeCount x ≤ U3 x)

end EKG3
