import ErsConj13.Defs

/-!
# The binomial side: the P-recurrence for `b_J = Σ_ℓ C(ℓ, J+1−ℓ) C(J+ℓ−1, ℓ)`

Creative telescoping with the polynomial certificate `pc` (computed with a computer
algebra system; checked here by Lean).
-/

noncomputable section
namespace ErsConj13

/-- The summand after `ℓ = J + 1 − m`: `C(J+1−m, m) · C(2J−m, J+1−m)`. -/
def Fm (J m : ℕ) : ℕ := Nat.choose (J + 1 - m) m * Nat.choose (2 * J - m) (J + 1 - m)

lemma Fm_trinomial (J m : ℕ) (hJ : 1 ≤ J) (hm : 2 * m ≤ J + 1) :
    Fm J m * (m.factorial * (J + 1 - 2 * m).factorial * (J - 1).factorial) = (2 * J - m).factorial := by
  have c1 := Nat.choose_mul_factorial_mul_factorial (n := J + 1 - m) (k := m) (by omega)
  have c2 := Nat.choose_mul_factorial_mul_factorial (n := 2 * J - m) (k := J + 1 - m) (by omega)
  rw [show J + 1 - m - m = J + 1 - 2 * m by omega] at c1
  rw [show 2 * J - m - (J + 1 - m) = J - 1 by omega] at c2
  rw [Fm, ← c2, ← c1]; ring

lemma Fm_zero (J m : ℕ) (hm : J + 1 < 2 * m) : Fm J m = 0 := by
  rw [Fm, Nat.choose_eq_zero_of_lt (by omega), zero_mul]


/-- The common hypergeometric base `H(j,m) = (2j−m)! / (m! (j+3−2m)! (j+1)!)` (zero for `2m > j+3`). -/
def Hq (j m : ℕ) : ℚ :=
  if 2 * m ≤ j + 3 then
    ((2 * j - m).factorial : ℚ) / (m.factorial * (j + 3 - 2 * m).factorial * (j + 1).factorial)
  else 0

lemma fact2 (r : ℕ) : ((r + 2).factorial : ℚ) = (r + 2) * (r + 1) * r.factorial := by
  simp [Nat.factorial_succ]; ring

lemma fact1 (r : ℕ) : ((r + 1).factorial : ℚ) = (r + 1) * r.factorial := by
  simp [Nat.factorial_succ]

lemma R0 (j m : ℕ) (hj : 1 ≤ j) :
    (Fm j m : ℚ) = Hq j m * (((j : ℚ) + 3 - 2 * m) * (j + 2 - 2 * m) * j * (j + 1)) := by
  rcases le_or_gt (2 * m) (j + 1) with h | h
  · have T := Fm_trinomial j m hj h
    obtain ⟨r, hr⟩ : ∃ r, j + 1 = 2 * m + r := ⟨j + 1 - 2 * m, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [show k + 1 + 1 - 2 * m = r by omega, show k + 1 - 1 = k by omega] at T
    rw [Hq, if_pos (by omega), show k + 1 + 3 - 2 * m = r + 2 by omega, fact2,
      show k + 1 + 1 = k + 2 by ring, fact2]
    have hrq : ((k : ℚ) + 2) = 2 * m + r := by exact_mod_cast hr
    have T' : ((Fm (k + 1) m : ℕ) : ℚ) * (m.factorial * r.factorial * k.factorial)
        = ((2 * (k + 1) - m).factorial : ℚ) := by exact_mod_cast T
    rw [← T']
    have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
    have h2 : (r.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (k.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    rw [show (k : ℚ) = 2 * m + r - 2 by linarith]; ring
  · rw [Fm_zero j m h, Nat.cast_zero]
    rcases le_or_gt (2 * m) (j + 3) with h' | h'
    · have : ((j : ℚ) + 3 - 2 * m) * (j + 2 - 2 * m) = 0 := by
        rcases (show 2 * m = j + 2 ∨ 2 * m = j + 3 by omega) with e | e
        · have : (2 * m : ℚ) = j + 2 := by exact_mod_cast e
          rw [show (j : ℚ) + 2 - 2 * m = 0 by linarith, mul_zero]
        · have : (2 * m : ℚ) = j + 3 := by exact_mod_cast e
          rw [show (j : ℚ) + 3 - 2 * m = 0 by linarith, zero_mul]
      rw [show ((j : ℚ) + 3 - 2 * m) * (j + 2 - 2 * m) * j * (j + 1)
        = (((j : ℚ) + 3 - 2 * m) * (j + 2 - 2 * m)) * j * (j + 1) by ring, this]; ring
    · rw [Hq, if_neg (by omega), zero_mul]


lemma fact4 (r : ℕ) : ((r + 4).factorial : ℚ) = (r + 4) * (r + 3) * (r + 2) * (r + 1) * r.factorial := by
  simp [Nat.factorial_succ]; ring

lemma R1 (j m : ℕ) (hj : 1 ≤ j) :
    (Fm (j + 1) m : ℚ) =
      Hq j m * (((2 * j : ℚ) + 2 - m) * (2 * j + 1 - m) * (j + 3 - 2 * m) * (j + 1)) := by
  rcases le_or_gt (2 * m) (j + 2) with h | h
  · have T := Fm_trinomial (j + 1) m (by omega) (by omega)
    obtain ⟨r, hr⟩ : ∃ r, j + 2 = 2 * m + r := ⟨j + 2 - 2 * m, by omega⟩
    obtain ⟨n, hn⟩ : ∃ n, 2 * j = m + n := ⟨2 * j - m, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [show k + 1 + 1 + 1 - 2 * m = r by omega, show k + 1 + 1 - 1 = k + 1 by omega,
      show 2 * (k + 1 + 1) - m = n + 2 by omega] at T
    rw [Hq, if_pos (by omega), show k + 1 + 3 - 2 * m = r + 1 by omega, fact1,
      show 2 * (k + 1) - m = n by omega, show k + 1 + 1 = k + 2 by ring, fact2]
    have hrq : ((k : ℚ) + 3) = 2 * m + r := by exact_mod_cast hr
    have hnq : (2 * ((k : ℚ) + 1)) = m + n := by exact_mod_cast hn
    have T' : ((Fm (k + 1 + 1) m : ℕ) : ℚ) * (m.factorial * r.factorial * ((k + 1) * k.factorial))
        = ((n : ℚ) + 2) * (n + 1) * n.factorial := by
      rw [← fact2, ← fact1]; exact_mod_cast T
    have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
    have h2 : (r.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (k.factorial : ℚ) ≠ 0 := by positivity
    have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hFm : ((Fm (k + 1 + 1) m : ℕ) : ℚ) = ((n : ℚ) + 2) * (n + 1) * n.factorial /
        (m.factorial * r.factorial * ((k + 1) * k.factorial)) := by
      rw [← T']; field_simp
    rw [hFm]
    field_simp
    push_cast
    rw [show (k : ℚ) = 2 * m + r - 3 by linarith, show (n : ℚ) = 3 * m + 2 * r - 4 by linarith]
    ring
  · rw [Fm_zero (j + 1) m (by omega), Nat.cast_zero]
    rcases le_or_gt (2 * m) (j + 3) with h' | h'
    · have e : (2 * m : ℚ) = j + 3 := by exact_mod_cast (show 2 * m = j + 3 by omega)
      rw [show (j : ℚ) + 3 - 2 * m = 0 by linarith]; ring
    · rw [Hq, if_neg (by omega), zero_mul]

lemma R2 (j m : ℕ) (hj : 1 ≤ j) :
    (Fm (j + 2) m : ℚ) =
      Hq j m * (((2 * j : ℚ) + 4 - m) * (2 * j + 3 - m) * (2 * j + 2 - m) * (2 * j + 1 - m)) := by
  rcases le_or_gt (2 * m) (j + 3) with h | h
  · have T := Fm_trinomial (j + 2) m (by omega) (by omega)
    obtain ⟨n, hn⟩ : ∃ n, 2 * j = m + n := ⟨2 * j - m, by omega⟩
    rw [show j + 2 + 1 - 2 * m = j + 3 - 2 * m by omega, show j + 2 - 1 = j + 1 by omega,
      show 2 * (j + 2) - m = n + 4 by omega] at T
    rw [Hq, if_pos h, show 2 * j - m = n by omega]
    have hnq : (2 * (j : ℚ)) = m + n := by exact_mod_cast hn
    have T' : ((Fm (j + 2) m : ℕ) : ℚ) *
        (m.factorial * (j + 3 - 2 * m).factorial * (j + 1).factorial)
        = ((n : ℚ) + 4) * (n + 3) * (n + 2) * (n + 1) * n.factorial := by
      rw [← fact4]; exact_mod_cast T
    have hden : ((m.factorial * (j + 3 - 2 * m).factorial * (j + 1).factorial : ℕ) : ℚ) ≠ 0 := by
      positivity
    push_cast at hden
    rw [← eq_div_iff hden] at T'
    rw [T']
    rw [show (2 * (j : ℚ)) = m + n from hnq]
    field_simp
    ring
  · rw [Fm_zero (j + 2) m (by omega), Nat.cast_zero, Hq, if_neg (by omega), zero_mul]

lemma Hshift (j m : ℕ) (hj : 1 ≤ j) :
    Hq j (m + 1) * ((2 * j : ℚ) - m) * (m + 1) = Hq j m * (((j : ℚ) + 3 - 2 * m) * (j + 2 - 2 * m)) := by
  rcases le_or_gt (2 * (m + 1)) (j + 3) with h | h
  · obtain ⟨r, hr⟩ : ∃ r, j + 1 = 2 * m + r := ⟨j + 1 - 2 * m, by omega⟩
    obtain ⟨n, hn⟩ : ∃ n, 2 * j = m + 1 + n := ⟨2 * j - m - 1, by omega⟩
    rw [Hq, Hq, if_pos h, if_pos (by omega), show 2 * j - (m + 1) = n by omega,
      show 2 * j - m = n + 1 by omega, show j + 3 - 2 * (m + 1) = r by omega,
      show j + 3 - 2 * m = r + 2 by omega]
    simp only [fact2, fact1]
    have hrq : ((j : ℚ) + 1) = 2 * m + r := by exact_mod_cast hr
    have hnq : (2 * (j : ℚ)) = m + 1 + n := by exact_mod_cast hn
    have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
    have h2 : (r.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((j + 1).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h5 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have h6 : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [show (2 * (j : ℚ)) = m + 1 + n from hnq]
    field_simp
    rw [show (j : ℚ) = 2 * m + r - 1 by linarith]
    ring
  · rw [Hq, if_neg (by omega), zero_mul, zero_mul]
    rcases le_or_gt (2 * m) (j + 3) with h' | h'
    · have : ((j : ℚ) + 3 - 2 * m) * (j + 2 - 2 * m) = 0 := by
        rcases (show 2 * m = j + 2 ∨ 2 * m = j + 3 by omega) with e | e
        · have : (2 * m : ℚ) = j + 2 := by exact_mod_cast e
          rw [show (j : ℚ) + 2 - 2 * m = 0 by linarith, mul_zero]
        · have : (2 * m : ℚ) = j + 3 := by exact_mod_cast e
          rw [show (j : ℚ) + 3 - 2 * m = 0 by linarith, zero_mul]
      rw [this, mul_zero]
    · rw [Hq, if_neg (by omega), zero_mul]


/-- The creative-telescoping certificate (checked by Lean below). -/
def pc (j m : ℚ) : ℚ :=
  -j * (j + 1) * (140 * j ^ 4 - 8 * j ^ 3 * m + 533 * j ^ 3 - 4 * j ^ 2 * m ^ 2 - 10 * j ^ 2 * m
    + 696 * j ^ 2 - 15 * j * m ^ 2 + 3 * j * m + 375 * j - 9 * m ^ 2 + 3 * m + 72)

/-- `G(j,m) = H(j,m) (2j+1−m) m p(j,m)`. -/
def Gt (j m : ℕ) : ℚ := Hq j m * ((2 * j : ℚ) + 1 - m) * m * pc j m

/-- The polynomial `q₂ PF₂ − q₁ PF₁ − q₀ PF₀`. -/
def Qp (j m : ℚ) : ℚ :=
  5 * j * (j + 1) * (j + 3) * (4 * j + 3) * ((2 * j + 4 - m) * (2 * j + 3 - m) * (2 * j + 2 - m) * (2 * j + 1 - m))
  - 2 * j * (j + 2) * (44 * j ^ 2 + 99 * j + 51) * ((2 * j + 2 - m) * (2 * j + 1 - m) * (j + 3 - 2 * m) * (j + 1))
  - 3 * (j + 1) * (3 * j + 1) * (3 * j + 2) * (4 * j + 7) * ((j + 3 - 2 * m) * (j + 2 - 2 * m) * j * (j + 1))

lemma Gstep (j m : ℕ) (hj : 1 ≤ j) : Gt j (m + 1) - Gt j m = Hq j m * Qp j m := by
  have hs := Hshift j m hj
  simp only [Gt, Qp]
  push_cast
  linear_combination (norm := skip) (pc j (m + 1)) * hs
  unfold pc; ring

/-- `b_J = Σ_ℓ C(ℓ, J+1−ℓ) C(J+ℓ−1, ℓ)`, as a sum over `m = J+1−ℓ`. -/
def bsum (J : ℕ) : ℚ := ∑ m ∈ Finset.range (J + 2), (Fm J m : ℚ)

lemma ersCoeff_eq (J : ℕ) : ersCoeff J = (1 / (J : ℚ)) * bsum J := by
  rw [ersCoeff, bsum, ← Finset.sum_range_reflect]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  rw [Fm, show J + 2 - 1 - m = J + 1 - m by omega, show J + 1 - (J + 1 - m) = m by omega,
    show J + (J + 1 - m) - 1 = 2 * J - m by omega]

lemma sum_ext (j i : ℕ) (hi : i ≤ 2) (f : ℕ → ℚ) (hf : ∀ m, (Fm (j + i) m : ℚ) = Hq j m * f m) :
    bsum (j + i) = ∑ m ∈ Finset.range (j + 4), Hq j m * f m := by
  rw [bsum, Finset.sum_congr rfl (fun m _ => hf m)]
  apply Finset.sum_subset
  · intro m hm; simp only [Finset.mem_range] at *; omega
  · intro m hm hm'
    simp only [Finset.mem_range] at *
    rw [Hq, if_neg (by omega), zero_mul]

/-- The P-recurrence for `b_j` (creative telescoping). -/
lemma b_rec (j : ℕ) (hj : 1 ≤ j) :
    5 * (j : ℚ) * (j + 1) * (j + 3) * (4 * j + 3) * bsum (j + 2)
      - 2 * (j : ℚ) * (j + 2) * (44 * j ^ 2 + 99 * j + 51) * bsum (j + 1)
      - 3 * ((j : ℚ) + 1) * (3 * j + 1) * (3 * j + 2) * (4 * j + 7) * bsum j = 0 := by
  rw [sum_ext j 2 (by norm_num) _ (R2 j · hj), sum_ext j 1 (by norm_num) _ (R1 j · hj),
    show bsum j = bsum (j + 0) from rfl, sum_ext j 0 (by norm_num) _ (fun m => by simpa using R0 j m hj)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ = ∑ m ∈ Finset.range (j + 4), (Gt j (m + 1) - Gt j m) :=
        Finset.sum_congr rfl (fun m _ => by rw [Gstep j m hj, Qp]; ring)
    _ = Gt j (j + 4) - Gt j 0 := Finset.sum_range_sub _ _
    _ = 0 := by
        rw [Gt, Gt, Hq, if_neg (by omega)]; simp

end ErsConj13
