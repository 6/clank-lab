import Mathlib
import ABC.S4.FlowHoloAux1
import ABC.S4.FlowHoloAux3
import ABC.S4.FlowHoloAux4

/-! L0a helper: the time-`t` flow is holomorphic on the ball of initial points, as the uniform
limit of the Euler polygons. -/

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.FlowHoloAux

variable {n : ℕ} {F : (Fin n → ℂ) → (Fin n → ℂ)} {U : Set (Fin n → ℂ)} {γ : ℝ → (Fin n → ℂ)}
  {T ε L M : ℝ}

theorem differentiableOn_eulerStep (hF : DifferentiableOn ℂ F U) (h : ℝ) :
    DifferentiableOn ℂ (eulerStep F h) U :=
  differentiableOn_id.add (hF.const_smul h)

theorem natCast_mul_div_le {t : ℝ} (ht : 0 ≤ t) {k N : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    (k : ℝ) * (t / N) ≤ t := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  calc (k : ℝ) * (t / N) ≤ N * (t / N) := by gcongr
    _ = t := by field_simp

/-- Holomorphy of the time-`t` flow on the ball of initial points. -/
theorem flow_differentiableOn (hF : DifferentiableOn ℂ F U) (htube : Tube F U γ T ε L M)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hε : 0 < ε) {r : ℝ} {φ : ℝ → (Fin n → ℂ) → (Fin n → ℂ)}
    (hφ : ∀ x ∈ ball (γ 0) r, φ 0 x = x ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (φ · x) (F (φ t x)) (Icc 0 T) t ∧ dist (φ t x) (γ t) < ε / 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) : DifferentiableOn ℂ (φ t) (ball (γ 0) r) := by
  set C := T * L * M * exp (L * T) with hCdef
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hC : 0 ≤ C := by positivity
  have herr : ∀ N : ℕ, 0 < N → (M + C) * (t / N) ≤ ε / 2 → ∀ x ∈ ball (γ 0) r, ∀ k ≤ N,
      ‖(eulerStep F (t / N))^[k] x - φ (k * (t / N)) x‖ ≤ C * (t / N) :=
    fun N hN hs x hx => euler_err htube hL hM (fun s hs => ((hφ x hx).2 s hs).1)
      (fun s hs => ((hφ x hx).2 s hs).2.le) (hφ x hx).1 ht hN hs
  have hdiff : ∀ N : ℕ, 0 < N → (M + C) * (t / N) ≤ ε / 2 → ∀ k ≤ N,
      DifferentiableOn ℂ ((eulerStep F (t / N))^[k]) (ball (γ 0) r) := by
    intro N hN hs k
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hh : 0 ≤ t / N := div_nonneg ht.1 hNpos.le
    have hCh : C * (t / N) ≤ ε / 2 := by nlinarith
    induction k with
    | zero => intro _; exact differentiableOn_id
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      rw [Function.iterate_succ']
      refine (differentiableOn_eulerStep hF _).comp (ih hk') (fun x hx => ?_)
      have hkT : (k : ℝ) * (t / N) ∈ Icc 0 T :=
        ⟨by positivity, (natCast_mul_div_le ht.1 hN hk').trans ht.2⟩
      apply (htube _ hkT).1
      rw [mem_closedBall]
      calc dist ((eulerStep F (t / N))^[k] x) (γ (k * (t / N)))
          ≤ dist ((eulerStep F (t / N))^[k] x) (φ (k * (t / N)) x)
            + dist (φ (k * (t / N)) x) (γ (k * (t / N))) := dist_triangle _ _ _
        _ ≤ C * (t / N) + ε / 2 := by
            gcongr
            · rw [dist_eq_norm]; exact herr N hN hs x hx k hk'
            · exact ((hφ x hx).2 _ hkT).2.le
        _ ≤ ε := by linarith
  -- all step counts beyond `N0` are admissible
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * (M + C) * T / ε)
  have hadm : ∀ N : ℕ, N0 < N → (M + C) * (t / N) ≤ ε / 2 := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by
      have : (0 : ℝ) ≤ N0 := Nat.cast_nonneg N0
      have : (N0 : ℝ) < N := by exact_mod_cast hN
      linarith
    rw [div_lt_iff₀ hε] at hN0
    have h1 : (M + C) * t ≤ (M + C) * T := mul_le_mul_of_nonneg_left ht.2 (by positivity)
    have h2 : (N0 : ℝ) ≤ N := by exact_mod_cast hN.le
    rw [← mul_div_assoc, div_le_iff₀ hNpos]
    nlinarith
  set f : ℕ → (Fin n → ℂ) → (Fin n → ℂ) := fun k =>
    (eulerStep F (t / (k + N0 + 1 : ℕ)))^[k + N0 + 1] with hfdef
  have hfd : ∀ k, DifferentiableOn ℂ (f k) (ball (γ 0) r) := fun k =>
    hdiff _ (Nat.succ_pos _) (hadm _ (by omega)) _ le_rfl
  have hunif : TendstoUniformlyOn f (φ t) atTop (ball (γ 0) r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    obtain ⟨K, hK⟩ := exists_nat_gt (C * T / δ)
    filter_upwards [eventually_ge_atTop K] with k hk x hx
    have hNpos : (0 : ℝ) < ((k + N0 + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    have he := herr (k + N0 + 1) (Nat.succ_pos _) (hadm _ (by omega)) x hx _ le_rfl
    rw [mul_div_cancel₀ _ hNpos.ne'] at he
    rw [dist_comm, dist_eq_norm]
    refine he.trans_lt ?_
    rw [div_lt_iff₀ hδ] at hK
    have h1 : C * t ≤ C * T := mul_le_mul_of_nonneg_left ht.2 hC
    have h2 : (K : ℝ) ≤ ((k + N0 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ k + N0 + 1)
    rw [← mul_div_assoc, div_lt_iff₀ hNpos]
    nlinarith
  exact differentiableOn_of_tendstoUniformlyOn isOpen_ball hfd hunif

end ABC.S4.FlowHoloAux
