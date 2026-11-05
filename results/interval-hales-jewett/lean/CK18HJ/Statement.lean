import Mathlib.Algebra.BigOperators.Fin

/-!
# The statement (check against the paper, Section 1)

Letters are `Fin m` = {0, ..., m-1}; a word of length `n` is `Fin n → Fin m`
(positions 0..n-1 here, 1..n in the paper). A root is `Fin n → Option (Fin m)`,
with `none` the wildcard ∗.
-/

namespace CK18HJ

variable {m n : ℕ}

/-- `w(t)`: every wildcard of the root `w` replaced by the letter `t`. -/
def point (w : Fin n → Option (Fin m)) (t : Fin m) : Fin n → Fin m :=
  fun i => (w i).getD t

/-- Position `i` starts a run of `w`: a wildcard that is the first position
or follows a letter. -/
abbrev RunStart (w : Fin n → Option (Fin m)) (i : Fin n) : Prop :=
  w i = none ∧ (i.val = 0 ∨ ∃ j : Fin n, j.val + 1 = i.val ∧ w j ≠ none)

/-- The number of runs (maximal intervals of wildcards) of `w`. -/
def runs (w : Fin n → Option (Fin m)) : ℕ :=
  (Finset.univ.filter fun i => RunStart w i).card

/-- The letter before position `i` of `x`, and `0` before the first. -/
def prev (x : Fin n → Fin m) (i : Fin n) : ℤ :=
  if h : i.val = 0 then 0 else ((x ⟨i.val - 1, by have := i.isLt; omega⟩).val : ℤ)

/-- `S(x) = Σ (x_i - x_{i-1})²` with `x` preceded by `0`. -/
def S (x : Fin n → Fin m) : ℤ :=
  ∑ i, (((x i).val : ℤ) - prev x i) ^ 2

/-- `χ_B(x) = ⌊S(x)/B⌋ mod 2` (`S x ≥ 0`, so `/` is the floor). -/
def colour (B : ℕ) (x : Fin n → Fin m) : Bool :=
  decide ((S x / (B : ℤ)) % 2 = 1)

/-- The theorem: for `Q ≥ 1`, `K² ≥ 32Q` and `m ≥ 2K + 2`, no line whose root
has at most `Q` runs is monochromatic under `χ_{32Q}`. -/
def MainStatement : Prop :=
  ∀ Q K m n : ℕ, 1 ≤ Q → 32 * Q ≤ K * K → 2 * K + 2 ≤ m →
    ∀ w : Fin n → Option (Fin m), (∃ i, w i = none) → runs w ≤ Q →
      ∃ s t : Fin m, colour (32 * Q) (point w s) ≠ colour (32 * Q) (point w t)

/-- The corollary: for every `Q` some alphabet size `m` has, for every `n`, a
2-colouring of `[m]^n` with no monochromatic line whose root has at most `Q`
runs. -/
def UnboundedStatement : Prop :=
  ∀ Q : ℕ, ∃ m : ℕ, ∀ n : ℕ, ∃ c : (Fin n → Fin m) → Bool,
    ∀ w : Fin n → Option (Fin m), (∃ i, w i = none) → runs w ≤ Q →
      ∃ s t : Fin m, c (point w s) ≠ c (point w t)

end CK18HJ
