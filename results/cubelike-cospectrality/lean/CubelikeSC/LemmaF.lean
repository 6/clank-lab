import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Powerset

/-!
# Lemma F (the paper)

The finite statement, for general `(d, k)` as in §3 "Generalization", with
`LemmaF := LemmaFdk 7 3`. Cosets and elements of `H0` are numbered
`0 .. 2^k - 1` (bit `i` ↔ `e_{i+1}`).

A case is `(n, B, t)` with `n < 2^d`, `B ⊆ {1, …, 2^k - 1}`, `|B| ≤ n`,
`t ∈ {0, …, 2^k - 1}`. With `C = 2^(d-k)`, `m = |B|`,
`μ_u = Σ_{h∈B} (-1)^{u·h}`, the coset means are `M_0 = (C m - n)/(C - 1)` and
`M_u = μ_u` (`u ≠ 0`). The cost of a bracket `(α, β)` at coset `u` is
`n² + (C-1)(M_0² + (M_0-α)(β-M_0))` at `u = 0` and `C(μ_u² + (μ_u-α)(β-μ_u))`
otherwise. The budget is `2^d n`.
-/

namespace CubelikeSC

/-- `u·h ∈ {0,1}`, the dot product over `F_2` of the `k`-bit vectors `u` and `h`. -/
def bdot (k u h : ℕ) : ℕ := ((List.range k).countP fun i => u.testBit i && h.testBit i) % 2

section
variable (d k : ℕ)

/-- `μ_u = Σ_{h∈B} (-1)^{u·h}`. -/
def mu (B : Finset (Fin (2 ^ k))) (u : Fin (2 ^ k)) : ℤ := ∑ h ∈ B, (-1) ^ bdot k u h

/-- The coset mean: `M_0 = (C m - n)/(C - 1)`, `M_u = μ_u` for `u ≠ 0`, `C = 2^(d-k)`. -/
def mean (n : ℕ) (B : Finset (Fin (2 ^ k))) (u : Fin (2 ^ k)) : ℚ :=
  if u = 0 then ((2 ^ (d - k) : ℚ) * B.card - n) / (2 ^ (d - k) - 1) else mu k B u

/-- The cost of the bracket `(α, β)` at coset `u` (the paper, "Cost"). -/
def cost (n : ℕ) (B : Finset (Fin (2 ^ k))) (u : Fin (2 ^ k)) (α β : ℤ) : ℚ :=
  let M := mean d k n B u
  if u = 0 then (n : ℚ) ^ 2 + (2 ^ (d - k) - 1) * (M ^ 2 + (M - α) * (β - M))
  else 2 ^ (d - k) * (M ^ 2 + (M - α) * (β - M))

/-- An admissible bracket assignment `u ↦ (α_u, β_u)` for the case `(n, B, t)`:
conditions 1–5 of the paper. -/
def Admissible (n : ℕ) (B : Finset (Fin (2 ^ k))) (t : Fin (2 ^ k))
    (α β : Fin (2 ^ k) → ℤ) : Prop :=
  -- 1. `-n ≤ α_u ≤ M_u ≤ β_u ≤ n`
  (∀ u, -(n : ℤ) ≤ α u ∧ (α u : ℚ) ≤ mean d k n B u ∧ mean d k n B u ≤ β u ∧ β u ≤ n) ∧
  -- 2. `α_u = β_u` only if `α_u = M_u`
  (∀ u, α u = β u → (α u : ℚ) = mean d k n B u) ∧
  -- 3. `α_u ≡ β_u ≡ n - 2 (u·t) (mod 4)`
  (∀ u, α u ≡ n - 2 * bdot k u t [ZMOD 4] ∧ β u ≡ n - 2 * bdot k u t [ZMOD 4]) ∧
  -- 4. `n ∉ {α_u, β_u}` for `u ≠ 0`
  (∀ u, u ≠ 0 → α u ≠ n ∧ β u ≠ n) ∧
  -- 5. the sets `{α_u, β_u}` are pairwise disjoint
  (∀ u v, u ≠ v → α u ≠ α v ∧ α u ≠ β v ∧ β u ≠ α v ∧ β u ≠ β v)

/-- Lemma F at `(d, k)`: for every case, every admissible bracket assignment has
total cost `> 2^d n`. -/
def LemmaFdk : Prop :=
  ∀ n : ℕ, n < 2 ^ d → ∀ B : Finset (Fin (2 ^ k)), (0 : Fin (2 ^ k)) ∉ B → B.card ≤ n →
    ∀ t : Fin (2 ^ k), ∀ α β : Fin (2 ^ k) → ℤ, Admissible d k n B t α β →
      (2 ^ d * n : ℚ) < ∑ u, cost d k n B u (α u) (β u)

end

/-- Lemma F of the paper (`d = 7`, `k = 3`). -/
def LemmaF : Prop := LemmaFdk 7 3

end CubelikeSC
