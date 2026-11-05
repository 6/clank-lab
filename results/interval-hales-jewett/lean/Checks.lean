import CK18HJ

/-! Statement, axiom and example checks for the public build. -/
namespace CK18HJ.Checks

/-- Theorem 1, restated with its full type: for `Q ≥ 1`, `K² ≥ 32Q` and
`m ≥ 2K + 2`, no combinatorial line in `[m]^n` whose wildcard set has at most
`Q` runs is monochromatic under `x ↦ ⌊S(x)/(32Q)⌋ mod 2`. -/
example : ∀ Q K m n : ℕ, 1 ≤ Q → 32 * Q ≤ K * K → 2 * K + 2 ≤ m →
    ∀ w : Fin n → Option (Fin m), (∃ i, w i = none) → runs w ≤ Q →
      ∃ s t : Fin m, colour (32 * Q) (point w s) ≠ colour (32 * Q) (point w t) :=
  main

/-- Corollary 2, restated with its full type: for every `Q` some alphabet size
`m` has, for every `n`, a 2-coloring of `[m]^n` with no monochromatic line whose
wildcard set has at most `Q` runs. -/
example : ∀ Q : ℕ, ∃ m : ℕ, ∀ n : ℕ, ∃ c : (Fin n → Fin m) → Bool,
    ∀ w : Fin n → Option (Fin m), (∃ i, w i = none) → runs w ≤ Q →
      ∃ s t : Fin m, c (point w s) ≠ c (point w t) :=
  unbounded

/-- info: 'CK18HJ.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main

/-- info: 'CK18HJ.unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unbounded

/-! Small examples of the definitions, checked by the kernel. -/

/-- The root `∗ 2 ∗ ∗` over the letters `0, …, 4`. -/
def root4 : Fin 4 → Option (Fin 5) := ![none, some 2, none, none]

/-- Its wildcard set `{1, 3, 4}` (positions `0, 2, 3` here) has two runs. -/
example : runs root4 = 2 := by decide

/-- Its point at the letter `3` is the word `3 2 3 3`. -/
example : point root4 3 = ![3, 2, 3, 3] := by decide

/-- `S(3 2 3 3) = 3² + 1² + 1² + 0² = 11`, with the word preceded by `0`. -/
example : S (![3, 2, 3, 3] : Fin 4 → Fin 5) = 11 := by decide

/-- With block length `B = 4`, `⌊11/4⌋ = 2` is even, so the color is `false`;
with `B = 3`, `⌊11/3⌋ = 3` is odd, so it is `true`. -/
example : colour 4 (![3, 2, 3, 3] : Fin 4 → Fin 5) = false ∧
    colour 3 (![3, 2, 3, 3] : Fin 4 → Fin 5) = true := by decide

/-- The smallest instance of Theorem 1: `Q = 1`, `K = 6`, `m = 14`. A line in
`[14]^4` whose wildcard set is one interval is not monochromatic. -/
example (w : Fin 4 → Option (Fin 14)) (hw : ∃ i, w i = none) (hr : runs w ≤ 1) :
    ∃ s t : Fin 14, colour 32 (point w s) ≠ colour 32 (point w t) :=
  main 1 6 14 4 le_rfl (by norm_num) le_rfl w hw hr

end CK18HJ.Checks
