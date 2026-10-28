import D0

namespace LNEDPilot
open Polynomial

lemma phi_natDegree (h : ℚ[X]) : (phi h).natDegree = h.natDegree := by
  change (h.comp (X + C (1 : ℚ))).natDegree = _
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

lemma phi_leadingCoeff (h : ℚ[X]) : (phi h).leadingCoeff = h.leadingCoeff := by
  change (h.comp (X + C (1 : ℚ))).leadingCoeff = _
  have hq : (X + C (1 : ℚ)).natDegree ≠ 0 := by
    rw [natDegree_X_add_C]
    decide
  rw [leadingCoeff_comp hq, leadingCoeff_X_add_C]
  simp

lemma delta_degree_lt (h : ℚ[X]) (hh : h ≠ 0) : (delta h).degree < h.degree := by
  have hp : phi h ≠ 0 := by
    intro hz
    have hl := congrArg Polynomial.leadingCoeff hz
    rw [phi_leadingCoeff, leadingCoeff_zero] at hl
    exact hh (leadingCoeff_eq_zero.mp hl)
  have hd : h.degree = (phi h).degree := by
    rw [degree_eq_natDegree hh, degree_eq_natDegree hp, phi_natDegree]
  exact degree_sub_lt hd hh (phi_leadingCoeff h).symm

lemma delta_locally_nilpotent (h : ℚ[X]) :
    ∃ N : ℕ, 0 < N ∧ (delta^[N]) h = 0 := by
  have aux : ∀ n : ℕ, ∀ p : ℚ[X], p.natDegree = n →
      ∃ N : ℕ, 0 < N ∧ (delta^[N]) p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hz : delta p = 0
      · exact ⟨1, by omega, by simpa using hz⟩
      · have hp : p ≠ 0 := by
          intro hp0
          apply hz
          rw [hp0, delta_zero]
        have hlt : (delta p).natDegree < n := by
          rw [← hn]
          exact natDegree_lt_natDegree hz (delta_degree_lt p hp)
        obtain ⟨N, hN, he⟩ := ih (delta p).natDegree hlt (delta p) rfl
        refine ⟨N + 1, by omega, ?_⟩
        simpa only [Function.iterate_succ_apply] using he
  exact aux h.natDegree h rfl

#print axioms delta_locally_nilpotent
end LNEDPilot
