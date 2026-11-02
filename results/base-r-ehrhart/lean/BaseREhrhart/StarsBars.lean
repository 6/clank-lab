import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
The stars-and-bars component of the geometric
Ehrhart bridge. This module counts natural-coordinate vectors of a fixed
sum. It makes no geometric or certificate assumptions.
-/

namespace BaseREhrhart

/-- Natural-coordinate vectors of length `d + 1` and total `k`. -/
abbrev NatComposition (d k : ℕ) := {n : Fin (d + 1) → ℕ // ∑ i, n i = k}

noncomputable instance natCompositionFintype (d k : ℕ) :
    Fintype (NatComposition d k) :=
  Fintype.ofEquiv (Sym (Fin (d + 1)) k)
    (Sym.equivNatSumOfFintype (Fin (d + 1)) k)

/-- The finite set of weak compositions has the standard stars-and-bars size. -/
theorem natComposition_card (d k : ℕ) :
    Nat.card (NatComposition d k) = Nat.choose (k + d) d := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin (d + 1)) k)]
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : d + 1 + k - 1 = k + d := by omega
  rw [h]
  exact Nat.choose_symm_add

theorem natComposition_fintype_card (d k : ℕ) :
    Fintype.card (NatComposition d k) = Nat.choose (k + d) d := by
  rw [← Nat.card_eq_fintype_card]
  exact natComposition_card d k

/-- The six-coordinate specialization needed for the five-dimensional simplex. -/
theorem natComposition_six_card (k : ℕ) :
    Nat.card {n : Fin 6 → ℕ // ∑ i, n i = k} = Nat.choose (k + 5) 5 :=
  natComposition_card 5 k

end BaseREhrhart
