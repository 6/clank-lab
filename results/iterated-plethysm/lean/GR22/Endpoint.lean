import GR22.Defs

/-!
# The endpoint statements

`FullEndpoint`: for every weighted-homogeneous `g` of degree `d ≥ 1` (no positivity assumed),
every `a ≥ 2` and every Schur expansion `c` of `g[h_a]` (degree `N = a d`), the hook+column
coefficients satisfy `b(β,γ) = b(d-1-γ-β, γ)`, vanish when `β + γ ≥ d`, and the column `(1^N)`
has coefficient `0`.

`ExpansionsExist`: every weighted-homogeneous element of degree `N` has a Schur expansion
(so the statements below aren't vacuous).

`Question1`: Gutiérrez–Rosas §4 Question 1, in the source's sense: for every nonempty list
`n₁, …, n_k` of positive integers, every Schur expansion of `h_(n₁) ∘ ⋯ ∘ h_(n_k)` (degree
`n₁ ⋯ n_k`) and every `γ ≥ 0`, the nonzero entries of `(b_β^γ)_(β ≥ 0)` form a palindrome.
-/

namespace GR22

def FullEndpoint : Prop :=
  ∀ (d a : ℕ) (g : SF) (c : List ℕ →₀ ℚ),
    1 ≤ d → 2 ≤ a →
    MvPolynomial.IsWeightedHomogeneous (fun i : ℕ => i + 1) g d →
    SchurExpansion (a * d) (plethysm g (complete a)) c →
    (∀ (β : ℤ) (γ : ℕ),
      hookCoeff (a * d) c β γ = hookCoeff (a * d) c ((d : ℤ) - 1 - (γ : ℤ) - β) γ) ∧
    (∀ (β : ℤ) (γ : ℕ), (d : ℤ) ≤ β + (γ : ℤ) → hookCoeff (a * d) c β γ = 0) ∧
    c (List.replicate (a * d) 1) = 0

def ExpansionsExist : Prop :=
  ∀ (N : ℕ) (f : SF), MvPolynomial.IsWeightedHomogeneous (fun i : ℕ => i + 1) f N →
    ∃ c, SchurExpansion N f c

def Question1 : Prop :=
  ∀ (ns : List ℕ), ns ≠ [] → (∀ n ∈ ns, 1 ≤ n) →
    ∀ (c : List ℕ →₀ ℚ), SchurExpansion ns.prod (iterated ns) c →
      ∀ γ : ℕ, NonzeroPalindrome (fun β : ℕ => hookCoeff ns.prod c (β : ℤ) γ)

end GR22
