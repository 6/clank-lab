import ErsConj13.Defs

noncomputable section

namespace ErsConj13

lemma coeff_diag (F : PowerSeries ℚ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (diag F) = if e 0 = e 1 then PowerSeries.coeff (e 0) F else 0 := rfl

/-- The diagonal exponent `(i, i)`. -/
def dm (i : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 i

@[simp] lemma dm_zero_apply (i : ℕ) : dm i 0 = i := by simp [dm]
@[simp] lemma dm_one_apply (i : ℕ) : dm i 1 = i := by simp [dm]

lemma eq_dm {e : Fin 2 →₀ ℕ} (h : e 0 = e 1) : e = dm (e 0) := by
  ext k; fin_cases k <;> simp [h]

lemma fin2_ext {e e' : Fin 2 →₀ ℕ} (h0 : e 0 = e' 0) (h1 : e 1 = e' 1) : e = e' := by
  ext k; fin_cases k <;> simp [h0, h1]

lemma hdeg_add (p q : Fin 2 →₀ ℕ) : hdeg (p + q) = hdeg p + hdeg q := by
  simp only [hdeg, Finsupp.add_apply]; push_cast; ring

lemma diag_one : diag 1 = 1 := by
  ext e
  rw [coeff_diag, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
  by_cases h : e 0 = e 1
  · rw [if_pos h]
    by_cases h0 : e 0 = 0
    · rw [if_pos h0, if_pos]
      exact fin2_ext (by simp [h0]) (by simp [← h, h0])
    · rw [if_neg h0, if_neg]
      intro he; apply h0; simp [he]
  · rw [if_neg h, if_neg]
    intro he; apply h; simp [he]

lemma diag_add (f g : PowerSeries ℚ) : diag (f + g) = diag f + diag g := by
  ext e
  simp only [map_add, coeff_diag]
  split_ifs <;> simp

lemma diag_zero : diag 0 = 0 := by
  ext e
  simp only [coeff_diag, map_zero]
  split_ifs <;> rfl

lemma diag_mul (f g : PowerSeries ℚ) : diag (f * g) = diag f * diag g := by
  ext e
  rw [coeff_diag, MvPowerSeries.coeff_mul]
  by_cases h : e 0 = e 1
  · rw [if_pos h, PowerSeries.coeff_mul]
    refine Finset.sum_bij_ne_zero (fun p _ _ => (dm p.1, dm p.2)) ?_ ?_ ?_ ?_
    · intro p hp _
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      exact fin2_ext (by simp [hp]) (by simp [hp, h])
    · intro p _ _ q _ _ hpq
      simp only [Prod.mk.injEq] at hpq
      have h1 := congrArg (fun d => d 0) hpq.1
      have h2 := congrArg (fun d => d 0) hpq.2
      simp only [dm_zero_apply] at h1 h2
      exact Prod.ext h1 h2
    · intro q hq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
      rw [coeff_diag, coeff_diag] at hne
      have hq1 : q.1 0 = q.1 1 := by
        by_contra hc; rw [if_neg hc, zero_mul] at hne; exact hne rfl
      have hq2 : q.2 0 = q.2 1 := by
        by_contra hc; rw [if_neg hc, mul_zero] at hne; exact hne rfl
      rw [if_pos hq1, if_pos hq2] at hne
      refine ⟨(q.1 0, q.2 0), ?_, hne, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        rw [← hq]; simp
      · simp only
        rw [← eq_dm hq1, ← eq_dm hq2]
    · intro p _ _
      simp [coeff_diag]
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_diag, coeff_diag]
    by_cases h1 : p.1 0 = p.1 1
    · by_cases h2 : p.2 0 = p.2 1
      · exfalso; apply h; rw [← hp]; simp [h1, h2]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma diag_X : diag PowerSeries.X = u * w := by
  ext e
  rw [coeff_diag, PowerSeries.coeff_X, u, w, MvPowerSeries.X_def, MvPowerSeries.X_def,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial, one_mul]
  by_cases h : e 0 = e 1
  · rw [if_pos h]
    by_cases h0 : e 0 = 1
    · rw [if_pos h0, if_pos]
      exact fin2_ext (by simp [h0]) (by simp [← h, h0])
    · rw [if_neg h0, if_neg]
      intro he; apply h0; simp [he]
  · rw [if_neg h, if_neg]
    intro he; apply h; simp [he]

lemma diag_injective : Function.Injective diag := by
  intro f g hfg
  ext n
  have := congrArg (fun F => MvPowerSeries.coeff (dm n) F) hfg
  simpa [coeff_diag] using this

lemma OGe_add {k : ℤ} {f g : A} (hf : f ∈ OGe k) (hg : g ∈ OGe k) : f + g ∈ OGe k := by
  intro e he
  rw [map_add] at he
  by_cases h : MvPowerSeries.coeff e f = 0
  · rw [h, zero_add] at he; exact hg e he
  · exact hf e h

lemma OLe_add {k : ℤ} {f g : A} (hf : f ∈ OLe k) (hg : g ∈ OLe k) : f + g ∈ OLe k := by
  intro e he
  rw [map_add] at he
  by_cases h : MvPowerSeries.coeff e f = 0
  · rw [h, zero_add] at he; exact hg e he
  · exact hf e h

lemma exists_mul_ne_zero {f g : A} {e : Fin 2 →₀ ℕ} (he : MvPowerSeries.coeff e (f * g) ≠ 0) :
    ∃ p q, p + q = e ∧ MvPowerSeries.coeff p f ≠ 0 ∧ MvPowerSeries.coeff q g ≠ 0 := by
  rw [MvPowerSeries.coeff_mul] at he
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  exact ⟨x.1, x.2, hx, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

lemma OGe_mul {a b : ℤ} {f g : A} (hf : f ∈ OGe a) (hg : g ∈ OGe b) : f * g ∈ OGe (a + b) := by
  intro e he
  obtain ⟨p, q, rfl, hp, hq⟩ := exists_mul_ne_zero he
  rw [hdeg_add]
  exact add_le_add (hf p hp) (hg q hq)

lemma OLe_mul {a b : ℤ} {f g : A} (hf : f ∈ OLe a) (hg : g ∈ OLe b) : f * g ∈ OLe (a + b) := by
  intro e he
  obtain ⟨p, q, rfl, hp, hq⟩ := exists_mul_ne_zero he
  rw [hdeg_add]
  exact add_le_add (hf p hp) (hg q hq)

lemma OGe_mono {j k : ℤ} (hjk : j ≤ k) {f : A} (hf : f ∈ OGe k) : f ∈ OGe j :=
  fun e he => le_trans hjk (hf e he)

lemma OLe_mono {j k : ℤ} (hjk : j ≤ k) {f : A} (hf : f ∈ OLe j) : f ∈ OLe k :=
  fun e he => le_trans (hf e he) hjk

lemma oneGe_mul {x y : A} (hx : x - 1 ∈ OGe 1) (hy : y - 1 ∈ OGe 1) : x * y - 1 ∈ OGe 1 := by
  have : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  rw [this]
  exact OGe_add (OGe_add (OGe_mono (by norm_num) (OGe_mul hx hy)) hx) hy

lemma oneLe_mul {x y : A} (hx : x - 1 ∈ OLe (-1)) (hy : y - 1 ∈ OLe (-1)) :
    x * y - 1 ∈ OLe (-1) := by
  have : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  rw [this]
  exact OLe_add (OLe_add (OLe_mono (by norm_num) (OLe_mul hx hy)) hx) hy

lemma diag_mem_OGe (δ : PowerSeries ℚ) : diag δ ∈ OGe 0 := by
  intro e he
  rw [coeff_diag] at he
  split_ifs at he with h
  · simp [hdeg, h]
  · exact absurd rfl he

lemma diag_mem_OLe (δ : PowerSeries ℚ) : diag δ ∈ OLe 0 := by
  intro e he
  rw [coeff_diag] at he
  split_ifs at he with h
  · simp [hdeg, h]
  · exact absurd rfl he

lemma u_mem : u ∈ OLe (-1) := by
  intro e he
  rw [u, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma w_mem : w ∈ OGe 1 := by
  intro e he
  rw [w, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial] at he
  split_ifs at he with h
  · subst h; simp [hdeg]
  · exact absurd rfl he

lemma u_mul_diag_mem (δ : PowerSeries ℚ) : u * diag δ ∈ OLe (-1) := by
  simpa using OLe_mul u_mem (diag_mem_OLe δ)

lemma w_mul_diag_mem (δ : PowerSeries ℚ) : w * diag δ ∈ OGe 1 := by
  simpa using OGe_mul w_mem (diag_mem_OGe δ)

end ErsConj13
