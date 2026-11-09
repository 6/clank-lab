import Mathlib
import ABC.S4.FlowHoloAux1
import ABC.S4.FlowHoloAux3

/-! L0a helper: explicit Euler polygons converge to the flow uniformly on the ball of initial
points; each polygon is a composition of holomorphic steps, so the flow is holomorphic. -/

open Set Metric Filter Topology Real
open scoped NNReal

noncomputable section

namespace ABC.S4.FlowHoloAux

variable {n : ℕ} {F : (Fin n → ℂ) → (Fin n → ℂ)} {U : Set (Fin n → ℂ)} {γ : ℝ → (Fin n → ℂ)}
  {T ε L M : ℝ}

/-- One explicit Euler step of size `h`. -/
def eulerStep (F : (Fin n → ℂ) → (Fin n → ℂ)) (h : ℝ) (z : Fin n → ℂ) : Fin n → ℂ :=
  z + h • F z

/-- Local truncation error of the Euler step along a solution in the half tube. -/
theorem trunc_err (htube : Tube F U γ T ε L M) (hL : 0 ≤ L) (hM : 0 ≤ M)
    {y : ℝ → (Fin n → ℂ)} (hy : ∀ s ∈ Icc 0 T, HasDerivWithinAt y (F (y s)) (Icc 0 T) s)
    (hyγ : ∀ s ∈ Icc 0 T, dist (y s) (γ s) ≤ ε / 2)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (haT : a + h ≤ T) (hMh : M * h ≤ ε / 2) :
    ‖y (a + h) - y a - h • F (y a)‖ ≤ L * M * h ^ 2 := by
  have hsub : Icc a (a + h) ⊆ Icc 0 T := Icc_subset_Icc ha haT
  have hyd : ∀ s ∈ Icc a (a + h), HasDerivWithinAt y (F (y s)) (Icc a (a + h)) s :=
    fun s hs => (hy s (hsub hs)).mono hsub
  have hin : ∀ s ∈ Icc a (a + h), y s ∈ closedBall (γ s) ε := fun s hs => by
    have h1 := hyγ s (hsub hs)
    have h2 := dist_nonneg (x := y s) (y := γ s)
    rw [mem_closedBall]; linarith
  have hstep : ∀ s ∈ Icc a (a + h), ‖y s - y a‖ ≤ M * (s - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hyd
      (fun s hs => (htube s (hsub (Ico_subset_Icc_self hs))).2.2 _ (hin s (Ico_subset_Icc_self hs)))
  have hstep' : ∀ s ∈ Icc a (a + h), ‖y s - y a‖ ≤ M * h := fun s hs =>
    (hstep s hs).trans (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hM)
  have hgd : ∀ s ∈ Icc a (a + h), HasDerivWithinAt (fun s => y s - (s - a) • F (y a))
      (F (y s) - F (y a)) (Icc a (a + h)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => (s - a) • F (y a)) ((1 : ℝ) • F (y a)) s :=
      ((hasDerivAt_id s).sub_const a).smul_const (F (y a))
    have h2 := (hyd s hs).sub h1.hasDerivWithinAt
    rw [one_smul] at h2
    exact h2
  have hbound : ∀ s ∈ Ico a (a + h), ‖F (y s) - F (y a)‖ ≤ L * M * h := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have hya : y a ∈ closedBall (γ s) ε := by
      rw [mem_closedBall]
      calc dist (y a) (γ s) ≤ dist (y a) (y s) + dist (y s) (γ s) := dist_triangle _ _ _
        _ ≤ M * h + ε / 2 := by
          gcongr
          · rw [dist_eq_norm, norm_sub_rev]; exact hstep' s hs'
          · exact hyγ s (hsub hs')
        _ ≤ ε := by linarith
    calc ‖F (y s) - F (y a)‖ ≤ L * ‖y s - y a‖ := (htube s (hsub hs')).2.1 _ (hin s hs') _ hya
      _ ≤ L * (M * h) := by gcongr; exact hstep' s hs'
      _ = L * M * h := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' hgd hbound (a + h)
    (right_mem_Icc.mpr (by linarith))
  simp only [add_sub_cancel_left, sub_self, zero_smul, sub_zero] at this
  calc ‖y (a + h) - y a - h • F (y a)‖ = ‖y (a + h) - h • F (y a) - y a‖ := by
        congr 1; abel
    _ ≤ L * M * h * h := this
    _ = L * M * h ^ 2 := by ring

/-- Global error of the Euler polygon with `N` steps up to time `t`. -/
theorem euler_err (htube : Tube F U γ T ε L M) (hL : 0 ≤ L) (hM : 0 ≤ M)
    {y : ℝ → (Fin n → ℂ)} (hy : ∀ s ∈ Icc 0 T, HasDerivWithinAt y (F (y s)) (Icc 0 T) s)
    (hyγ : ∀ s ∈ Icc 0 T, dist (y s) (γ s) ≤ ε / 2) {x : Fin n → ℂ} (hx0 : y 0 = x)
    {t : ℝ} (ht : t ∈ Icc 0 T) {N : ℕ} (hN : 0 < N)
    (hsmall : (M + T * L * M * exp (L * T)) * (t / N) ≤ ε / 2) :
    ∀ k ≤ N, ‖(eulerStep F (t / N))^[k] x - y (k * (t / N))‖ ≤
      T * L * M * exp (L * T) * (t / N) := by
  set h := t / N with hhdef
  set C := T * L * M * exp (L * T) with hCdef
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh : 0 ≤ h := div_nonneg ht.1 hNpos.le
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hC : 0 ≤ C := by positivity
  have hCh : C * h ≤ ε / 2 := by nlinarith
  have hMh : M * h ≤ ε / 2 := by nlinarith
  have hkh : ∀ k : ℕ, k ≤ N → (k : ℝ) * h ≤ T := by
    intro k hk
    calc (k : ℝ) * h ≤ N * h := by gcongr
      _ = t := by rw [hhdef]; field_simp
      _ ≤ T := ht.2
  set B : ℕ → ℝ := fun k => k * (L * M * h ^ 2) * (1 + h * L) ^ k with hBdef
  have hBC : ∀ k : ℕ, k ≤ N → B k ≤ C * h := by
    intro k hk
    have hq : (1 + h * L) ^ k ≤ exp (L * T) := by
      calc (1 + h * L) ^ k ≤ exp (h * L) ^ k :=
            pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp (h * L)]) k
        _ = exp (k * (h * L)) := (exp_nat_mul _ _).symm
        _ ≤ exp (L * T) := by
            refine exp_le_exp.mpr ?_
            calc (k : ℝ) * (h * L) = (k * h) * L := by ring
              _ ≤ T * L := by gcongr; exact hkh k hk
              _ = L * T := by ring
    calc B k = ((k : ℝ) * h) * (L * M * h) * (1 + h * L) ^ k := by simp only [hBdef]; ring
      _ ≤ T * (L * M * h) * exp (L * T) := by
          gcongr
          exact hkh k hk
      _ = C * h := by rw [hCdef]; ring
  have hmain : ∀ k : ℕ, k ≤ N → ‖(eulerStep F h)^[k] x - y (k * h)‖ ≤ B k := by
    intro k
    induction k with
    | zero => intro _; simp [hBdef, hx0]
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      have he := ih hk'
      set Y := (eulerStep F h)^[k] x
      have hkT : (k : ℝ) * h ∈ Icc 0 T := ⟨by positivity, hkh k hk'⟩
      have hyk : y (k * h) ∈ closedBall (γ (k * h)) ε := by
        rw [mem_closedBall]; have := hyγ _ hkT
        have := dist_nonneg (x := y (k * h)) (y := γ (k * h)); linarith
      have hYk : Y ∈ closedBall (γ (k * h)) ε := by
        rw [mem_closedBall]
        calc dist Y (γ (k * h)) ≤ dist Y (y (k * h)) + dist (y (k * h)) (γ (k * h)) :=
              dist_triangle _ _ _
          _ ≤ C * h + ε / 2 := by
              gcongr
              · rw [dist_eq_norm]; exact he.trans (hBC k hk')
              · exact hyγ _ hkT
          _ ≤ ε := by linarith
      have hLip := (htube _ hkT).2.1 _ hYk _ hyk
      have htr := trunc_err htube hL hM hy hyγ hkT.1 hh
        (by have := hkh (k + 1) hk; push_cast at this; linarith) hMh
      have hsucc : (eulerStep F h)^[k + 1] x = Y + h • F Y := by
        rw [Function.iterate_succ_apply']; rfl
      have hcast : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
      rw [hsucc, hcast]
      have hsplit : Y + h • F Y - y (k * h + h) = (Y - y (k * h)) + h • (F Y - F (y (k * h)))
          - (y (k * h + h) - y (k * h) - h • F (y (k * h))) := by
        rw [smul_sub]; abel
      rw [hsplit]
      have hq1 : 1 ≤ (1 + h * L) ^ (k + 1) := one_le_pow₀ (by nlinarith)
      have hc0 : 0 ≤ L * M * h ^ 2 := by positivity
      calc ‖(Y - y (k * h)) + h • (F Y - F (y (k * h)))
            - (y (k * h + h) - y (k * h) - h • F (y (k * h)))‖
          ≤ ‖Y - y (k * h)‖ + ‖h • (F Y - F (y (k * h)))‖
            + ‖y (k * h + h) - y (k * h) - h • F (y (k * h))‖ := by
            refine (norm_sub_le _ _).trans ?_
            gcongr
            exact norm_add_le _ _
        _ ≤ ‖Y - y (k * h)‖ + h * (L * ‖Y - y (k * h)‖) + L * M * h ^ 2 := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
            gcongr
        _ = (1 + h * L) * ‖Y - y (k * h)‖ + L * M * h ^ 2 := by ring
        _ ≤ (1 + h * L) * B k + L * M * h ^ 2 := by gcongr
        _ = k * (L * M * h ^ 2) * (1 + h * L) ^ (k + 1) + L * M * h ^ 2 := by
            simp only [hBdef]; ring
        _ ≤ k * (L * M * h ^ 2) * (1 + h * L) ^ (k + 1)
            + L * M * h ^ 2 * (1 + h * L) ^ (k + 1) := by
            have := mul_le_mul_of_nonneg_left hq1 hc0
            rw [mul_one] at this
            linarith
        _ = B (k + 1) := by simp only [hBdef]; push_cast; ring
  exact fun k hk => (hmain k hk).trans (hBC k hk)

end ABC.S4.FlowHoloAux
