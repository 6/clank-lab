import GR22.EndpointPositional
import GR22.UnitE

/-! `FullEndpoint → Question1Positional`, reusing unit E's lemmas. -/

namespace GR22

theorem question1Positional_of (hE : FullEndpoint) : Question1Positional := by
  intro ns hns c hc
  rw [unitE_prod_filter, unitE_iterated_filter] at hc
  rw [unitE_prod_filter]
  have hL : ∀ n ∈ ns.filter (· ≠ 1), 2 ≤ n := by
    intro n hn
    simp only [List.mem_filter, decide_eq_true_eq] at hn
    have := hns n hn.1
    omega
  generalize ns.filter (· ≠ 1) = L at hc hL ⊢
  rcases List.eq_nil_or_concat L with rfl | ⟨init, a, rfl⟩
  · simp only [List.dropLast_nil, List.prod_nil, Nat.cast_one]
    refine ⟨fun β γ => ?_, fun β γ hβ => unitE_hookCoeff_one c β γ (by omega)⟩
    by_cases h : β = 0 ∧ γ = 0
    · obtain ⟨rfl, rfl⟩ := h
      norm_num
    · rw [unitE_hookCoeff_one c β γ h, unitE_hookCoeff_one c _ γ (by omega)]
  · rw [List.concat_eq_append] at hc hL ⊢
    rw [List.dropLast_concat]
    have ha : 2 ≤ a := hL a (by simp)
    have hd : 1 ≤ init.prod := by
      rw [Nat.one_le_iff_ne_zero, Ne, List.prod_eq_zero_iff]
      intro h0
      have := hL 0 (by simp [h0])
      omega
    have hN : (init ++ [a]).prod = a * init.prod := by simp [mul_comm]
    rw [hN, unitE_iterated_concat] at hc
    rw [hN]
    obtain ⟨hrefl, hzero, -⟩ :=
      hE init.prod a (iterated init) c hd ha (unitE_iterated_isWH init) hc
    exact ⟨hrefl, hzero⟩

end GR22
