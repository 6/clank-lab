import Hopkins.Definitions

namespace Hopkins

theorem lower (a ell M : ℕ) (ha : 2 ≤ a) (hell : 1 ≤ ell)
    (hM : 1 ≤ M) (hMN : M < a ^ 2 * (ell + 1) ^ 2) :
    Valid M (lowerColor a ell) ∧ ¬ Mono a (a * ell) M (lowerColor a ell) := by
  have hs : 4 ≤ a*(ell+1) := by nlinarith
  constructor
  · constructor
    · simp only [lowerColor, decide_eq_false_iff_not]
      rintro ⟨_,h⟩
      omega
    · intro i hi hiM hh
      simp only [lowerColor, decide_eq_true_eq] at hh
      have hd : a ∣ 1 := by
        simpa using Nat.dvd_sub hh.2.1 hh.1.1
      have := Nat.le_of_dvd (by norm_num : 0 < (1:ℕ)) hd
      omega
  · rintro ⟨x,y,z,hx,hxM,hy,hyM,hz,hzM,he,hxy,hyz⟩
    have hdz : a ∣ z := by
      rw [← he]
      exact dvd_add (dvd_mul_right a x) (dvd_mul_of_dvd_left (dvd_mul_right a ell) y)
    have hsz : a*(ell+1) ≤ z := by
      have h1 := Nat.mul_le_mul_left a hx
      have h2 := Nat.mul_le_mul_left (a*ell) hy
      nlinarith
    have hcz : lowerColor a ell z = true := by
      simp only [lowerColor, decide_eq_true_eq]
      exact ⟨hdz,hsz⟩
    have hcx : a*(ell+1) ≤ x := by
      have h : lowerColor a ell x = true := hxy.trans (hyz.trans hcz)
      simp only [lowerColor, decide_eq_true_eq] at h
      exact h.2
    have hcy : a*(ell+1) ≤ y := by
      have h : lowerColor a ell y = true := hyz.trans hcz
      simp only [lowerColor, decide_eq_true_eq] at h
      exact h.2
    have h1 := Nat.mul_le_mul_left a hcx
    have h2 := Nat.mul_le_mul_left (a*ell) hcy
    nlinarith

end Hopkins
