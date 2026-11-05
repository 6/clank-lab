import Harborth

/-! Main theorems. -/

open Finset

namespace Harborth

/-- Upper bound: every `(2p-1)`-subset of `(ZMod p)²` has `p` distinct elements summing to zero. -/
theorem upper (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p)
    (S : Finset (ZMod p × ZMod p)) (hS : S.card = 2 * p - 1) :
    HasZeroSumPSubset p S :=
  upper_aux p hp S hS

/-- Lower bound: for every odd prime there is a `(2p-2)`-subset with no such `p` elements. -/
theorem lower (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ∃ S : Finset (ZMod p × ZMod p), S.card = 2 * p - 2 ∧ ¬ HasZeroSumPSubset p S := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hcard : (univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  refine ⟨({0, 1} : Finset (ZMod p)) ×ˢ univ.erase (0 : ZMod p), ?_, ?_⟩
  · rw [card_product, card_pair h01, hcard]; omega
  · rintro ⟨T, hT, hTc, hTs⟩
    set U := T.filter (fun x => x.1 = 1) with hU
    set V := T.filter (fun x => ¬ x.1 = 1) with hV
    have hUV : U.card + V.card = p := by
      rw [hU, hV, card_filter_add_card_filter_not, hTc]
    have hUle : U.card ≤ p - 1 := by
      have : U ⊆ ({1} : Finset (ZMod p)) ×ˢ univ.erase (0 : ZMod p) := by
        intro x hx
        rw [hU, mem_filter] at hx
        have := mem_product.1 (hT hx.1)
        simp only [mem_product, mem_singleton]
        exact ⟨hx.2, this.2⟩
      have := card_le_card this
      rwa [card_product, card_singleton, hcard, one_mul] at this
    have hVle : V.card ≤ p - 1 := by
      have : V ⊆ ({0} : Finset (ZMod p)) ×ˢ univ.erase (0 : ZMod p) := by
        intro x hx
        rw [hV, mem_filter] at hx
        have := mem_product.1 (hT hx.1)
        simp only [mem_product, mem_singleton]
        refine ⟨?_, this.2⟩
        have := this.1
        simp only [mem_insert, mem_singleton] at this
        tauto
      have := card_le_card this
      rwa [card_product, card_singleton, hcard, one_mul] at this
    have hsumfst : ∑ x ∈ T, x.1 = (U.card : ZMod p) := by
      have : ∑ x ∈ T, x.1 = ∑ x ∈ T, if x.1 = 1 then (1 : ZMod p) else 0 := by
        refine sum_congr rfl fun x hx => ?_
        have := (mem_product.1 (hT hx)).1
        simp only [mem_insert, mem_singleton] at this
        rcases this with h | h <;> simp [h]
      rw [this, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have h0 : (U.card : ZMod p) = 0 := by
      rw [← hsumfst]
      have := congrArg Prod.fst hTs
      simpa [Prod.fst_sum] using this
    rw [ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    have : U.card = 0 := by
      rcases k with _ | k
      · simpa using hk
      · have : p ≤ U.card := hk ▸ Nat.le_mul_of_pos_right p (Nat.succ_pos k)
        omega
    omega

/-- The Harborth constant `g(C_p ⊕ C_p) = 2p - 1` for every prime `p ≥ 11`. -/
theorem harborth_constant (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) :
    sInf {k : ℕ | ∀ S : Finset (ZMod p × ZMod p), S.card = k → HasZeroSumPSubset p S}
      = 2 * p - 1 := by
  have hmem : 2 * p - 1 ∈ {k : ℕ | ∀ S : Finset (ZMod p × ZMod p), S.card = k →
      HasZeroSumPSubset p S} := fun S hS => upper p hp S hS
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  intro k hk
  by_contra hlt
  push Not at hlt
  obtain ⟨S, hS, hnS⟩ := lower p (by omega)
  obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq (s := S) (n := k) (by omega)
  obtain ⟨T, hT, hTc, hTs⟩ := hk S' hS'c
  exact hnS ⟨T, hT.trans hS'S, hTc, hTs⟩

end Harborth
