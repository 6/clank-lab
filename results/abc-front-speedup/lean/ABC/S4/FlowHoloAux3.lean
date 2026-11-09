import Mathlib
import ABC.S4.FlowHoloAux1
import ABC.S4.FlowHoloAux2

/-! L0a helper: a uniform tube around the solution segment, and existence of the flow on
`[0, T]` for initial points near `γ 0` (Picard–Lindelöf for the field clamped to the tube, then
Grönwall keeps the solutions inside the tube, where the clamp is inactive). -/

open Set Metric Filter Topology Real
open scoped NNReal

noncomputable section

namespace ABC.S4.FlowHoloAux

variable {n : ℕ}

/-- The tube condition: on each `closedBall (γ u) ε`, `F` is defined (inside `U`),
`L`-Lipschitz and bounded by `M`. -/
def Tube (F : (Fin n → ℂ) → (Fin n → ℂ)) (U : Set (Fin n → ℂ)) (γ : ℝ → (Fin n → ℂ))
    (T ε L M : ℝ) : Prop :=
  ∀ u ∈ Icc 0 T, closedBall (γ u) ε ⊆ U ∧
    (∀ a ∈ closedBall (γ u) ε, ∀ b ∈ closedBall (γ u) ε, ‖F a - F b‖ ≤ L * ‖a - b‖) ∧
    (∀ a ∈ closedBall (γ u) ε, ‖F a‖ ≤ M)

theorem exists_tube {F : (Fin n → ℂ) → (Fin n → ℂ)} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {γ : ℝ → (Fin n → ℂ)} {T : ℝ}
    (hγc : ContinuousOn γ (Icc 0 T)) (hγU : ∀ t ∈ Icc 0 T, γ t ∈ U) :
    ∃ ε > 0, ∃ L ≥ 0, ∃ M ≥ 0, Tube F U γ T ε L M := by
  have hK0 : IsCompact (γ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hγc
  obtain ⟨δ2, hδ2, hsub⟩ := hK0.exists_cthickening_subset_open hU
    (by rintro _ ⟨t, ht, rfl⟩; exact hγU t ht)
  have hK : IsCompact (cthickening δ2 (γ '' Icc 0 T)) := hK0.cthickening
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF.continuousOn.mono hsub)
  set δ := δ2 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, max C 0 / δ, by positivity, max C 0, le_max_right _ _, fun u hu => ?_⟩
  have hball2 : closedBall (γ u) δ2 ⊆ cthickening δ2 (γ '' Icc 0 T) :=
    closedBall_subset_cthickening (mem_image_of_mem γ hu) δ2
  have hball1 : closedBall (γ u) δ ⊆ closedBall (γ u) δ2 :=
    closedBall_subset_closedBall (by linarith)
  refine ⟨(hball1.trans hball2).trans hsub, fun a ha b hb => ?_,
    fun a ha => (hC a (hball2 (hball1 ha))).trans (le_max_left _ _)⟩
  have hzz : ∀ z ∈ closedBall (γ u) δ, closedBall z δ ⊆ closedBall (γ u) δ2 := by
    intro z hz
    apply closedBall_subset_closedBall'
    rw [mem_closedBall] at hz
    linarith
  have hderiv : ∀ z ∈ closedBall (γ u) δ, ‖fderiv ℂ F z‖ ≤ max C 0 / δ := fun z hz =>
    norm_fderiv_le_of_closedBall hU hF hδ (le_max_right _ _) ((hzz z hz).trans (hball2.trans hsub))
      (fun w hw => (hC w (hball2 (hzz z hz hw))).trans (le_max_left _ _))
  exact (convex_closedBall (γ u) δ).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => hF.differentiableAt (hU.mem_nhds ((hball1.trans hball2).trans hsub hz)))
    hderiv hb ha

theorem mem_nhdsGE_Icc {T t : ℝ} (ht : t ∈ Ico 0 T) : Icc 0 T ∈ 𝓝[≥] t :=
  mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)

theorem exists_flow {F : (Fin n → ℂ) → (Fin n → ℂ)} {U : Set (Fin n → ℂ)}
    (hF : DifferentiableOn ℂ F U) {γ : ℝ → (Fin n → ℂ)} {T : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t)
    {ε L M : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) (hM : 0 ≤ M) (htube : Tube F U γ T ε L M) :
    ∃ r > 0, ∃ φ : ℝ → (Fin n → ℂ) → (Fin n → ℂ), ∀ x ∈ ball (γ 0) r, φ 0 x = x ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (φ · x) (F (φ t x)) (Icc 0 T) t ∧
        dist (φ t x) (γ t) < ε / 2 := by
  have hγc : ContinuousOn γ (Icc 0 T) := fun t ht => (hγ t ht).continuousWithinAt
  set g : ℝ → (Fin n → ℂ) → (Fin n → ℂ) := fun t y => F (γ t + clampR ε (y - γ t)) with hgdef
  have hgmem : ∀ t y, γ t + clampR ε (y - γ t) ∈ closedBall (γ t) ε := by
    intro t y
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact norm_clampR_le hε.le _
  have hgid : ∀ t y, dist y (γ t) ≤ ε → g t y = F y := by
    intro t y hy
    simp only [hgdef]
    rw [clampR_of_le (by rwa [← dist_eq_norm]), add_sub_cancel]
  set K : ℝ≥0 := Real.toNNReal (2 * L) with hKdef
  have hKc : (K : ℝ) = 2 * L := Real.coe_toNNReal _ (by positivity)
  have hglip : ∀ t ∈ Icc 0 T, LipschitzWith K (g t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [hKc, dist_eq_norm]
    have h1 := (htube t ht).2.1 _ (hgmem t y) _ (hgmem t z)
    have h2 := (lipschitzWith_clampR (E := Fin n → ℂ) hε).dist_le_mul (y - γ t) (z - γ t)
    rw [dist_sub_right, dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat] at h2
    calc ‖g t y - g t z‖ ≤ L * ‖γ t + clampR ε (y - γ t) - (γ t + clampR ε (z - γ t))‖ := h1
      _ = L * ‖clampR ε (y - γ t) - clampR ε (z - γ t)‖ := by rw [add_sub_add_left_eq_sub]
      _ ≤ L * (2 * ‖y - z‖) := by gcongr
      _ = 2 * L * dist y z := by rw [dist_eq_norm]; ring
  have hgcont : ∀ x, ContinuousOn (g · x) (Icc 0 T) := by
    intro x
    refine hF.continuousOn.comp (hγc.add (((lipschitzWith_clampR hε).continuous).comp_continuousOn
      (continuousOn_const.sub hγc))) (fun t ht => (htube t ht).1 (hgmem t x))
  have hgbound : ∀ t ∈ Icc 0 T, ∀ x, ‖g t x‖ ≤ M := fun t ht x =>
    (htube t ht).2.2 _ (hgmem t x)
  set r : ℝ := ε / 2 / exp (2 * L * T) with hrdef
  have hr : 0 < r := by positivity
  set t₀ : Icc (0 : ℝ) T := ⟨0, left_mem_Icc.mpr hT⟩
  set r' : ℝ≥0 := Real.toNNReal r
  set M' : ℝ≥0 := Real.toNNReal M
  set a : ℝ≥0 := r' + M' * Real.toNNReal T
  have hPL : IsPicardLindelof g t₀ (γ 0) a r' M' K :=
    { lipschitzOnWith := fun t ht => (hglip t ht).lipschitzOnWith
      continuousOn := fun x _ => hgcont x
      norm_le := fun t ht x _ => by
        rw [Real.coe_toNNReal _ hM]; exact hgbound t ht x
      mul_max_le := by
        simp [t₀, a, r', M', Real.coe_toNNReal _ hM, Real.coe_toNNReal _ hT, hT] }
  obtain ⟨α, hα⟩ := hPL.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  refine ⟨r, hr, fun t x => α x t, fun x hx => ?_⟩
  have hxr : x ∈ closedBall (γ 0) r' := by
    rw [mem_closedBall, Real.coe_toNNReal _ hr.le]
    exact (mem_ball.mp hx).le
  obtain ⟨h0, hd⟩ := hα x hxr
  have hgr : ∀ t ∈ Icc 0 T, dist (α x t) (γ t) ≤ dist x (γ 0) * exp (K * (t - 0)) := by
    refine dist_le_of_trajectories_ODE_of_mem (v := g) (s := fun _ => univ) (a := 0) (b := T)
      (fun t ht => (hglip t (Ico_subset_Icc_self ht)).lipschitzOnWith)
      (fun t ht => (hd t ht).continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (mem_nhdsGE_Icc ht))
      (fun _ _ => trivial) hγc (fun t ht => ?_) (fun _ _ => trivial)
      (show dist (α x 0) (γ 0) ≤ dist x (γ 0) from
        le_of_eq (congrArg (fun z => dist z (γ 0)) h0))
    rw [hgid t (γ t) (by simp [hε.le])]
    exact (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (mem_nhdsGE_Icc ht)
  have hclose : ∀ t ∈ Icc 0 T, dist (α x t) (γ t) < ε / 2 := by
    intro t ht
    refine (hgr t ht).trans_lt ?_
    rw [hKc, sub_zero]
    calc dist x (γ 0) * exp (2 * L * t) ≤ dist x (γ 0) * exp (2 * L * T) := by
          gcongr; exact ht.2
      _ < r * exp (2 * L * T) := by gcongr; exact mem_ball.mp hx
      _ = ε / 2 := by rw [hrdef]; field_simp
  refine ⟨h0, fun t ht => ⟨?_, hclose t ht⟩⟩
  have := hd t ht
  rwa [hgid t _ ((hclose t ht).le.trans (by linarith))] at this

end ABC.S4.FlowHoloAux
