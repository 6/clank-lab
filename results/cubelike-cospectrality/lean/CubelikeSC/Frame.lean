import CubelikeSC.Cosets

/-!
# Lemma 4 (normal form), without a change of basis

If `|K(S)| ≥ 5` there are `h₀, h₁, h₂ ∈ K(S)`, independent, whose span contains
`σ`. (`K(S)` is closed under addition and contains `0` and `σ`, so this is
elementary: take `h₀ = σ` if `σ ≠ 0`, then `h₁ ∉ {0, h₀}` and
`h₂ ∉ {0, h₀, h₁, h₀ + h₁}`.)
-/

namespace CubelikeSC

lemma comb_three (h : Fin 3 → V) (c : W) : comb h c = c 0 • h 0 + c 1 • h 1 + c 2 • h 2 := by
  simp [comb, Fin.sum_univ_three]

lemma exists_frame (S : Finset V) (hK : 5 ≤ (K S).card) :
    ∃ h : Fin 3 → V, (∀ i, h i ∈ K S) ∧ (∀ c, comb h c = 0 → c = 0) ∧
      ∃ t : W, comb h t = sigma S := by
  -- `h₀`
  obtain ⟨h0, h0K, h0ne, hσ⟩ : ∃ h0 ∈ K S, h0 ≠ 0 ∧ (sigma S = 0 ∨ sigma S = h0) := by
    by_cases hs : sigma S = 0
    · obtain ⟨g, hg, hg0⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({0} : Finset V)) (t := K S) (by simp; omega)
      exact ⟨g, hg, by simpa using hg0, Or.inl hs⟩
    · exact ⟨sigma S, sigma_mem_K S, hs, Or.inr rfl⟩
  obtain ⟨h1, h1K, h1n⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, h0} : Finset V)) (t := K S) (by have := Finset.card_le_two (a := (0 : V)) (b := h0); omega)
  obtain ⟨h2, h2K, h2n⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, h0, h1, h0 + h1} : Finset V)) (t := K S)
    (by have := Finset.card_le_four (a := (0 : V)) (b := h0) (c := h1) (d := h0 + h1); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1n h2n
  obtain ⟨h10, h1h0⟩ := h1n
  obtain ⟨h20, h2h0, h2h1, h2h01⟩ := h2n
  refine ⟨![h0, h1, h2], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simpa
  · intro c hc
    rw [comb_three] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hc
    have e01 : h0 + h1 ≠ 0 := fun e => h1h0 ((add_eq_zero_iff_eq' _ _).1 e).symm
    have e02 : h0 + h2 ≠ 0 := fun e => h2h0 ((add_eq_zero_iff_eq' _ _).1 e).symm
    have e12 : h1 + h2 ≠ 0 := fun e => h2h1 ((add_eq_zero_iff_eq' _ _).1 e).symm
    have e012 : h0 + h1 + h2 ≠ 0 := fun e => h2h01 ((add_eq_zero_iff_eq' _ _).1 e).symm
    rcases zmod2_cases (c 0) with c0 | c0 <;> rcases zmod2_cases (c 1) with c1 | c1 <;>
      rcases zmod2_cases (c 2) with c2 | c2 <;>
      simp only [c0, c1, c2, zero_smul, one_smul, zero_add, add_zero] at hc <;>
      first
      | exact absurd hc h0ne | exact absurd hc h10 | exact absurd hc h20
      | exact absurd hc e01 | exact absurd hc e02 | exact absurd hc e12 | exact absurd hc e012
      | (funext i; fin_cases i <;> simp [c0, c1, c2])
  · rcases hσ with hσ | hσ
    · exact ⟨0, by rw [comb_zero, hσ]⟩
    · refine ⟨![1, 0, 0], ?_⟩
      rw [comb_three, hσ]; simp

end CubelikeSC
