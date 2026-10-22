import Mathlib

namespace P16c

/-- Every divisor of the multiplicative-group cardinality occurs as an order. -/
lemma field_element_of_order_dvd {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hn : n ∣ Nat.card F - 1) : ∃ x : F, orderOf x = n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hd : n ∣ orderOf g := by simpa [hg, Nat.card_units] using hn
  have hne : orderOf g ≠ 0 := by
    rw [hg]
    exact Nat.card_pos.ne'
  refine ⟨↑(g ^ (orderOf g / n)), ?_⟩
  rw [orderOf_units]
  exact orderOf_pow_orderOf_div hne hd

/-- Odd periods coexist in a finite field of characteristic two. -/
theorem fields_exist (s u : ℕ) (hs : Odd s) (hu : Odd u) :
    ∃ (k : ℕ) (l m : GaloisField 2 k), orderOf l = s ∧ orderOf m = u := by
  let k := Nat.totient (s * u)
  have hsu : 0 < s * u := Nat.mul_pos hs.pos hu.pos
  have hk : k ≠ 0 := (Nat.totient_pos.mpr hsu).ne'
  have hd : s * u ∣ 2 ^ k - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow k 2 (by omega))).mp
      (Nat.ModEq.pow_totient (hs.mul hu).coprime_two_left).symm
  have hc : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k hk
  obtain ⟨l, hl⟩ := field_element_of_order_dvd (F := GaloisField 2 k)
    (hc ▸ (dvd_mul_right s u).trans hd)
  obtain ⟨m, hm⟩ := field_element_of_order_dvd (F := GaloisField 2 k)
    (hc ▸ (dvd_mul_left u s).trans hd)
  exact ⟨k, l, m, hl, hm⟩
end P16c
