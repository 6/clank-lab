import Hopkins.Definitions

namespace Hopkins

private theorem witness {a b N x y z : ℕ} {c : ℕ → Bool}
    (hx : 1 ≤ x) (hxN : x ≤ N) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hz : 1 ≤ z) (hzN : z ≤ N) (he : a*x+b*y=z)
    (hxy : c x = c y) (hyz : c y = c z) : Mono a b N c :=
  ⟨x,y,z,hx,hxN,hy,hyN,hz,hzN,he,hxy,hyz⟩

theorem control11_upper : Forces 1 1 4 := by
  intro c hc
  have h1 := hc.1
  cases h2 : c 2 with
  | false =>
    exact witness (x := 1) (y := 1) (z := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) rfl (h1.trans h2.symm)
  | true =>
    have h3 : c 3 = false := by
      cases hh : c 3 with
      | false => rfl
      | true => exact False.elim (hc.2 2 (by norm_num) (by norm_num) ⟨h2,hh⟩)
    cases h4 : c 4 with
    | false =>
      exact witness (x := 1) (y := 3) (z := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (h1.trans h3.symm) (h3.trans h4.symm)
    | true =>
      exact witness (x := 2) (y := 2) (z := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) rfl (h2.trans h4.symm)

theorem control12_upper : Forces 1 2 4 := by
  intro c hc
  have h1 := hc.1
  cases h3 : c 3 with
  | false =>
    exact witness (x := 1) (y := 1) (z := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) rfl (h1.trans h3.symm)
  | true =>
    have h2 : c 2 = false := by
      cases hh : c 2 with
      | false => rfl
      | true => exact False.elim (hc.2 2 (by norm_num) (by norm_num) ⟨hh,h3⟩)
    have h4 : c 4 = false := by
      cases hh : c 4 with
      | false => rfl
      | true => exact False.elim (hc.2 3 (by norm_num) (by norm_num) ⟨h3,hh⟩)
    exact witness (x := 2) (y := 1) (z := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (h2.trans h1.symm) (h1.trans h4.symm)

def control11Color (t : ℕ) : Bool := decide (t = 2)
def control12Color (t : ℕ) : Bool := decide (3 ≤ t)

theorem control11_lower (M : ℕ) (hM : M < 4) :
    Valid M control11Color ∧ ¬ Mono 1 1 M control11Color := by
  constructor
  · constructor
    · decide
    · intro i hi hiN hh
      simp only [control11Color, decide_eq_true_eq] at hh
      omega
  · rintro ⟨x,y,z,hx,hxN,hy,hyN,hz,hzN,he,hxy,hyz⟩
    have hx4 : x < 4 := lt_of_le_of_lt hxN hM
    have hy4 : y < 4 := lt_of_le_of_lt hyN hM
    have hz4 : z < 4 := lt_of_le_of_lt hzN hM
    interval_cases x <;> interval_cases y <;> interval_cases z <;>
      norm_num [control11Color] at *

theorem control12_lower (M : ℕ) (hM : M < 4) :
    Valid M control12Color ∧ ¬ Mono 1 2 M control12Color := by
  constructor
  · constructor
    · decide
    · intro i hi hiN hh
      simp only [control12Color, decide_eq_true_eq] at hh
      omega
  · rintro ⟨x,y,z,hx,hxN,hy,hyN,hz,hzN,he,hxy,hyz⟩
    have hx4 : x < 4 := lt_of_le_of_lt hxN hM
    have hy4 : y < 4 := lt_of_le_of_lt hyN hM
    have hz4 : z < 4 := lt_of_le_of_lt hzN hM
    interval_cases x <;> interval_cases y <;> interval_cases z <;>
      norm_num [control12Color] at *

theorem control11_isLeast : IsLeast (ForcingSet 1 1) 4 := by
  refine ⟨⟨by norm_num, control11_upper⟩, ?_⟩
  intro M hM
  by_contra h
  have hm : M < 4 := by omega
  exact (control11_lower M hm).2 (hM.2 _ (control11_lower M hm).1)

theorem control12_isLeast : IsLeast (ForcingSet 1 2) 4 := by
  refine ⟨⟨by norm_num, control12_upper⟩, ?_⟩
  intro M hM
  by_contra h
  have hm : M < 4 := by omega
  exact (control12_lower M hm).2 (hM.2 _ (control12_lower M hm).1)

theorem control11 : R0phi 1 1 = 4 := by
  exact control11_isLeast.csInf_eq

theorem control12 : R0phi 1 2 = 4 := by
  exact control12_isLeast.csInf_eq

end Hopkins
