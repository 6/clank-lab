import GR22.Defs

/-!
# Positional form of Question 1

Definition 2.8 of the source calls a sequence symmetric when its *nonzero* entries form a
palindrome (`Question1`). This stronger form keeps the zeros: for the iterated plethysm of
`n₁, …, n_k ≥ 1`, with `d` the product of the entries `≠ 1` other than the innermost one, every
β-sequence is the reflection `β ↦ d - 1 - γ - β` of itself, zero for `β + γ ≥ d` and (by the
definition of `hookCoeff`) for `β < 0`.
-/

namespace GR22

def Question1Positional : Prop :=
  ∀ (ns : List ℕ), (∀ n ∈ ns, 1 ≤ n) →
    ∀ (c : List ℕ →₀ ℚ), SchurExpansion ns.prod (iterated ns) c →
      (∀ (β : ℤ) (γ : ℕ), hookCoeff ns.prod c β γ =
          hookCoeff ns.prod c ((((ns.filter (· ≠ 1)).dropLast.prod : ℕ) : ℤ) - 1 - (γ : ℤ) - β) γ) ∧
      (∀ (β : ℤ) (γ : ℕ), (((ns.filter (· ≠ 1)).dropLast.prod : ℕ) : ℤ) ≤ β + (γ : ℤ) →
          hookCoeff ns.prod c β γ = 0)

/-- The off-by-one reflection, which is false (`Sanity.lean` refutes it in the kernel). -/
def FullEndpointOffByOne : Prop :=
  ∀ (d a : ℕ) (g : SF) (c : List ℕ →₀ ℚ),
    1 ≤ d → 2 ≤ a →
    MvPolynomial.IsWeightedHomogeneous (fun i : ℕ => i + 1) g d →
    SchurExpansion (a * d) (plethysm g (complete a)) c →
    ∀ (β : ℤ) (γ : ℕ), hookCoeff (a * d) c β γ = hookCoeff (a * d) c ((d : ℤ) - (γ : ℤ) - β) γ

end GR22
