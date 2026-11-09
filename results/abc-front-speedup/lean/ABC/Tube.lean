import ABC.Defs

/-!
# The vortex-tube first integral

`VortexTube W` says that `W` is a nonnegative, nonzero, Lipschitz, `2π`-periodic first
integral of the ABC field (`V·∇W = 0` almost everywhere), supported where `V_z ≥ c₀ > 0`, whose
support projects in `x` and in `y` into one compact interval of length less than `2π` per
period. This is the function `W` of the paper's tube construction.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace ABC

def VortexTube (W : E 3 → ℝ) : Prop :=
  (∃ C, LipschitzWith C W) ∧ Periodic (2 * Real.pi) W ∧ (∀ x, 0 ≤ W x) ∧ (∃ x, W x ≠ 0) ∧
  (∀ᵐ x, ⟪abcField x, gradient W x⟫ = 0) ∧
  (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x, W x ≠ 0 → c₀ ≤ abcField x 2) ∧
  ∃ a b δ : ℝ, 0 < δ ∧ ∀ x, W x ≠ 0 → ∃ m k : ℤ,
    x 0 ∈ Set.Icc (a + 2 * Real.pi * m + δ) (a + 2 * Real.pi * (m + 1) - δ) ∧
    x 1 ∈ Set.Icc (b + 2 * Real.pi * k + δ) (b + 2 * Real.pi * (k + 1) - δ)

end ABC
