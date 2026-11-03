import Mathlib

/-!
# Definitions for Gutiérrez–Rosas Question 1 (arXiv:2201.00240v2, §4)

Symmetric functions over `ℚ` as the polynomial ring `ℚ[p₁, p₂, …]` in the power sums,
which is how the source defines `Λ`. Variable `i` stands for `p_(i+1)`, of weight `i+1`.
Complete homogeneous functions come from Newton's identity, Schur functions from the
Jacobi–Trudi determinant, and plethysm from substituting Adams operations.
-/

noncomputable section
namespace GR22

open MvPolynomial

/-- Symmetric functions over `ℚ`: variable `i` is the power sum `p_(i+1)`. -/
abbrev SF := MvPolynomial ℕ ℚ

/-- The power sum `p_k` for `k ≥ 1` (and `0` for `k = 0`, never used). -/
def power (k : ℕ) : SF := if k = 0 then 0 else X (k - 1)

/-- Complete homogeneous `h_n`, by Newton's identity `n h_n = ∑_{k=1}^n p_k h_(n-k)`. -/
def complete : ℕ → SF
  | 0 => 1
  | n + 1 => C ((n + 1 : ℚ)⁻¹) *
      ∑ k : Fin (n + 1), power (k.val + 1) * complete (n - k.val)

/-- `h_k` for an integer index, zero when the index is negative. -/
def completeZ (k : ℤ) : SF := if 0 ≤ k then complete k.toNat else 0

/-- The Adams operation `p_j ↦ p_(k j)`, fixing rational constants. -/
def adams (k : ℕ) (f : SF) : SF := rename (fun i => k * (i + 1) - 1) f

/-- Plethysm `f[g]`: substitute `p_k[g] = adams k g` for each `p_k` in `f`. -/
def plethysm (f g : SF) : SF := eval₂ C (fun i => adams (i + 1) g) f

/-- The Schur function `s_μ` by the Jacobi–Trudi determinant `det (h_(μ_i - i + j))`. -/
def schur (μ : List ℕ) : SF :=
  Matrix.det (fun i j : Fin μ.length =>
    completeZ ((μ.get i : ℤ) - (i.val : ℤ) + (j.val : ℤ)))

/-- `μ` is a partition of `N`: weakly decreasing positive parts summing to `N`. -/
def IsPartitionOf (N : ℕ) (μ : List ℕ) : Prop :=
  μ.Pairwise (fun a b => b ≤ a) ∧ (∀ n ∈ μ, 0 < n) ∧ μ.sum = N

/-- `c` is a Schur expansion of `f` in degree `N`: `f = ∑ c_μ s_μ` over partitions of `N`. -/
def SchurExpansion (N : ℕ) (f : SF) (c : List ℕ →₀ ℚ) : Prop :=
  (∀ μ ∈ c.support, IsPartitionOf N μ) ∧ f = c.sum (fun μ q => C q * schur μ)

/-- The coefficient `b_β^γ` of `s_(N-2β-γ, 2^β, 1^γ)` in the Schur expansion `c`, read in the
source's convention (Warning 2.2): the first part is distinguished even when it is `2`; a first
part `1` occurs only with `β = 0` (the column `(1^N)`); otherwise the shape doesn't exist and
the coefficient is `0`. -/
def hookCoeff (N : ℕ) (c : List ℕ →₀ ℚ) (β : ℤ) (γ : ℕ) : ℚ :=
  let α : ℤ := (N : ℤ) - 2 * β - (γ : ℤ)
  if 0 ≤ β ∧ 1 ≤ α ∧ (β = 0 ∨ 2 ≤ α) then
    c (α.toNat :: (List.replicate β.toNat 2 ++ List.replicate γ 1))
  else 0

/-- The iterated plethysm `h_(n₁) ∘ h_(n₂) ∘ ⋯ ∘ h_(n_k)`, with `[]` giving `p₁ = h₁`,
the plethystic identity. -/
def iterated : List ℕ → SF
  | [] => power 1
  | n :: ns => plethysm (complete n) (iterated ns)

/-- The source's "symmetric" (Definition 2.8): the sequence has finite support and, for any
bound past its support, its nonzero entries, read in order, form a palindrome. -/
def NonzeroPalindrome (b : ℕ → ℚ) : Prop :=
  (∃ M, ∀ β, M ≤ β → b β = 0) ∧
  ∀ M, (∀ β, M ≤ β → b β = 0) →
    (((List.range M).map b).filter (· ≠ 0)).reverse = ((List.range M).map b).filter (· ≠ 0)

end GR22
