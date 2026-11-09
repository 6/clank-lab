import ABC.S4.FlowHolo

/-! Helpers for L0b (`flow_complex_time`): local Lipschitz bounds and ODE uniqueness. -/

open Set Metric Filter Topology

noncomputable section

namespace ABC.S4.FlowComplexAux

/-- A holomorphic map on an open subset of `Cn m` is locally Lipschitz (Cauchy estimate). -/
theorem locLip {m : ℕ} {H : Cn m → Cn m} {W : Set (Cn m)} (hW : IsOpen W)
    (hH : DifferentiableOn ℂ H W) {y0 : Cn m} (hy0 : y0 ∈ W) :
    ∃ K, ∃ t ∈ 𝓝 y0, LipschitzOnWith K H t := by
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW y0 hy0
  set δ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hcl : closedBall y0 (2 * δ) ⊆ W :=
    (closedBall_subset_ball (by rw [hδdef]; linarith)).trans hεW
  obtain ⟨M, hM⟩ := (isCompact_closedBall y0 (2 * δ)).exists_bound_of_continuousOn
    (hH.continuousOn.mono hcl)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y0 (mem_closedBall_self (by positivity)))
  have hyW : ∀ y ∈ ball y0 δ, y ∈ W := fun y hy =>
    hcl (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hy)
  have hD : ∀ y ∈ ball y0 δ, ‖fderiv ℂ H y‖ ≤ M / δ := by
    intro y hy
    have hyW' : W ∈ 𝓝 y := hW.mem_nhds (hyW y hy)
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro h
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    have hnh : 0 < ‖h‖ := norm_pos_iff.2 hh
    set R := δ / ‖h‖ with hRdef
    have hR : 0 < R := by positivity
    have hgcl : ∀ l ∈ closedBall (0 : ℂ) R, y + l • h ∈ closedBall y0 (2 * δ) := by
      intro l hl
      rw [mem_closedBall, dist_zero_right] at hl
      rw [mem_closedBall, dist_eq_norm]
      have h1 : ‖y - y0‖ < δ := mem_ball_iff_norm.1 hy
      have h2 : ‖l • h‖ ≤ δ := by
        rw [norm_smul]
        calc ‖l‖ * ‖h‖ ≤ R * ‖h‖ := by gcongr
          _ = δ := by rw [hRdef]; field_simp
      calc ‖y + l • h - y0‖ = ‖(y - y0) + l • h‖ := by congr 1; abel
        _ ≤ ‖y - y0‖ + ‖l • h‖ := norm_add_le _ _
        _ ≤ 2 * δ := by linarith
    have hgd : DifferentiableOn ℂ (fun l : ℂ => H (y + l • h)) (closedBall 0 R) := by
      intro l hl
      have hm := hcl (hgcl l hl)
      exact (((hH _ hm).differentiableAt (hW.mem_nhds hm)).comp l
        ((differentiableAt_const _).add (differentiableAt_id.smul_const h))).differentiableWithinAt
    have hder : HasDerivAt (fun l : ℂ => H (y + l • h)) (fderiv ℂ H y h) 0 := by
      have h1 : HasDerivAt (fun l : ℂ => y + l • h) h 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add y
      have h2 : HasFDerivAt H (fderiv ℂ H y) ((fun l : ℂ => y + l • h) 0) := by
        simpa using ((hH y (hyW y hy)).differentiableAt hyW').hasFDerivAt
      exact h2.comp_hasDerivAt 0 h1
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      (hgd.diffContOnCl_ball subset_rfl)
      (fun z hz => hM _ (hgcl z (sphere_subset_closedBall hz)))
    rw [hder.deriv] at this
    calc ‖fderiv ℂ H y h‖ ≤ M / R := this
      _ = M / δ * ‖h‖ := by rw [hRdef]; field_simp
  refine ⟨(M / δ).toNNReal, ball y0 δ, ball_mem_nhds _ hδ, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (𝕜 := ℂ) (f' := fderiv ℂ H)
    (fun y hy => ?_) (fun y hy => ?_) (convex_ball _ _)
  · exact ((hH y (hyW y hy)).differentiableAt (hW.mem_nhds (hyW y hy))).hasFDerivAt.hasFDerivWithinAt
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity), coe_nnnorm]
    exact hD y hy

/-- Uniqueness for `y' = H y` with `H` holomorphic on an open set (one-sided derivatives). -/
theorem odeUniq {m : ℕ} {H : Cn m → Cn m} {W : Set (Cn m)} (hW : IsOpen W)
    (hH : DifferentiableOn ℂ H W) {f g : ℝ → Cn m} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (H (f t)) (Icc a b) t ∧ f t ∈ W)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (H (g t)) (Icc a b) t ∧ g t ∈ W)
    (h0 : f a = g a) : EqOn f g (Icc a b) := by
  intro τ hτ
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).1.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).1.continuousWithinAt
  have hS : IsClosed ({t | f t = g t} ∩ Icc a b) := by
    rw [inter_comm]
    exact (hfc.prodMk hgc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
  refine hS.Icc_subset_of_forall_mem_nhdsWithin h0 ?_ hτ
  rintro x ⟨hx, hxI⟩
  have hxI' : x ∈ Icc a b := Ico_subset_Icc_self hxI
  obtain ⟨K, t, ht, hL⟩ := locLip hW hH (hf x hxI').2
  have hft : f ⁻¹' t ∈ 𝓝[Icc a b] x := hfc x hxI' ht
  have hgt : g ⁻¹' t ∈ 𝓝[Icc a b] x := hgc x hxI' (by rw [← show f x = g x from hx]; exact ht)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhdsWithin_iff.1 (inter_mem hft hgt)
  set c := min (x + δ / 2) b with hc
  have hxc : x < c := lt_min (by linarith) hxI.2
  have hcb : c ≤ b := min_le_right _ _
  have hcδ : c ≤ x + δ / 2 := min_le_left _ _
  have hsub : Icc x c ⊆ Icc a b := Icc_subset_Icc hxI.1 hcb
  have hmem : ∀ τ ∈ Ico x c, f τ ∈ t ∧ g τ ∈ t := by
    intro τ hτ
    refine hδ' ⟨?_, hsub (Ico_subset_Icc_self hτ)⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hτ.1, hτ.2]
  have hnhd : ∀ τ ∈ Ico x c, Icc a b ∈ 𝓝[≥] τ := fun τ hτ =>
    mem_of_superset (Icc_mem_nhdsGE (hτ.2.trans_le hcb)) (Icc_subset_Icc (hxI.1.trans hτ.1) le_rfl)
  have key : EqOn f g (Icc x c) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => H) (s := fun _ => t) (K := K)
      (fun _ _ => hL) (hfc.mono hsub)
      (fun τ hτ => (hf τ (hsub (Ico_subset_Icc_self hτ))).1.mono_of_mem_nhdsWithin (hnhd τ hτ))
      (fun τ hτ => (hmem τ hτ).1) (hgc.mono hsub)
      (fun τ hτ => (hg τ (hsub (Ico_subset_Icc_self hτ))).1.mono_of_mem_nhdsWithin (hnhd τ hτ))
      (fun τ hτ => (hmem τ hτ).2) hx
  exact mem_of_superset (Ioo_mem_nhdsGT hxc) (fun τ hτ => key ⟨hτ.1.le, hτ.2.le⟩)

/-! ### The augmented system `(c, z)' = (0, c • F z)` on `Cn (n+1)` -/

/-- `(c, x) ↦ (c, x)` as a vector of `Cn (n+1)`. -/
abbrev aug {n : ℕ} (c : ℂ) (x : Cn n) : Cn (n + 1) := Matrix.vecCons c x

/-- The augmented field: its time-1 flow from `(t, x)` is the complex-time-`t` flow of `F`. -/
def augF {n : ℕ} (F : Cn n → Cn n) (v : Cn (n + 1)) : Cn (n + 1) :=
  Matrix.vecCons 0 (v 0 • F (Matrix.vecTail v))

theorem differentiable_tail {n : ℕ} :
    Differentiable ℂ (fun v : Cn (n + 1) => Matrix.vecTail v) :=
  differentiable_pi.2 fun i => differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin (n + 1) => ℂ) i.succ

theorem differentiable_aug {n : ℕ} :
    Differentiable ℂ (fun q : ℂ × Cn n => aug q.1 q.2) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [aug, Matrix.cons_val_zero]
    exact differentiable_fst
  · simp only [aug, Matrix.cons_val_succ]
    exact (differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin n => ℂ) j).comp differentiable_snd

theorem isOpen_augW {n : ℕ} {U : Set (Cn n)} (hU : IsOpen U) :
    IsOpen (Matrix.vecTail ⁻¹' U : Set (Cn (n + 1))) :=
  hU.preimage differentiable_tail.continuous

theorem augF_diff {n : ℕ} {F : Cn n → Cn n} {U : Set (Cn n)} (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (augF F) (Matrix.vecTail ⁻¹' U) := by
  refine differentiableOn_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [augF]
  · have h1 : DifferentiableOn ℂ (fun v : Cn (n + 1) => F (Matrix.vecTail v))
        (Matrix.vecTail ⁻¹' U) :=
      hF.comp differentiable_tail.differentiableOn (fun v hv => hv)
    have h2 := (differentiableOn_pi.1 h1) j
    have h3 : DifferentiableOn ℂ (fun v : Cn (n + 1) => v 0) (Matrix.vecTail ⁻¹' U) :=
      (differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin (n + 1) => ℂ) 0).differentiableOn
    simp only [augF, Matrix.cons_val_succ, Pi.smul_apply, smul_eq_mul]
    exact h3.mul h2

theorem dist_aug_lt {n : ℕ} {c c' : ℂ} {x x' : Cn n} {r : ℝ} (hr : 0 < r) :
    dist (aug c x) (aug c' x') < r ↔ dist c c' < r ∧ dist x x' < r := by
  rw [dist_pi_lt_iff hr, Fin.forall_fin_succ, dist_pi_lt_iff hr]
  simp

theorem augF_zero_coord {n : ℕ} (F : Cn n → Cn n) (v : Cn (n + 1)) : augF F v 0 = 0 := by
  simp [augF]

theorem augF_succ {n : ℕ} (F : Cn n → Cn n) (v : Cn (n + 1)) (j : Fin n) :
    augF F v j.succ = v 0 * F (Matrix.vecTail v) j := by
  simp [augF]

/-- The base curves `τ ↦ (c₀, γ (c₀ τ))`, `τ ∈ [0, 1]`, solve the augmented system. -/
theorem base_curve {n : ℕ} {F : Cn n → Cn n} {U : Set (Cn n)} {γ : ℝ → Cn n} {T : ℝ}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t ∧ γ t ∈ U)
    {c0 : ℝ} (hc0 : c0 ∈ Icc 0 T) :
    ∀ τ ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun τ : ℝ => aug (c0 : ℂ) (γ (c0 * τ)))
        (augF F (aug (c0 : ℂ) (γ (c0 * τ)))) (Icc 0 1) τ ∧
      aug (c0 : ℂ) (γ (c0 * τ)) ∈ (Matrix.vecTail ⁻¹' U : Set (Cn (n + 1))) := by
  have hmaps : MapsTo (fun τ : ℝ => c0 * id τ) (Icc 0 1) (Icc 0 T) := fun τ hτ =>
    ⟨mul_nonneg hc0.1 hτ.1, by simp only [id]; nlinarith [hc0.1, hc0.2, hτ.1, hτ.2]⟩
  intro τ hτ
  have hm : c0 * τ ∈ Icc 0 T := hmaps hτ
  have hd := (hγ _ hm).1.scomp τ ((hasDerivWithinAt_id τ (Icc 0 1)).const_mul c0) hmaps
  refine ⟨hasDerivWithinAt_pi.2 fun i => ?_, by simpa [aug] using (hγ _ hm).2⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [aug, Matrix.cons_val_zero, augF_zero_coord]
    exact hasDerivWithinAt_const _ _ _
  · simp only [aug, Matrix.cons_val_succ, augF_succ, Matrix.cons_val_zero, Matrix.tail_cons]
    have := hasDerivWithinAt_pi.1 hd j
    simpa [Function.comp_def, Complex.real_smul] using this

/-- The data produced by `flow_holo` for every base curve. -/
def IsAugFlow {n : ℕ} (F : Cn n → Cn n) (U : Set (Cn n)) (γ : ℝ → Cn n) (T : ℝ)
    (R : ℝ → ℝ) (Φ : ℝ → ℝ → Cn (n + 1) → Cn (n + 1)) : Prop :=
  ∀ c0 ∈ Icc 0 T, 0 < R c0 ∧ DifferentiableOn ℂ (Φ c0 1) (ball (aug (c0 : ℂ) (γ 0)) (R c0)) ∧
    ∀ v ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0), Φ c0 0 v = v ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (Φ c0 · v) (augF F (Φ c0 τ v)) (Icc 0 1) τ ∧
        Φ c0 τ v ∈ (Matrix.vecTail ⁻¹' U : Set (Cn (n + 1)))

theorem exists_augFlow {n : ℕ} {F : Cn n → Cn n} {U : Set (Cn n)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {γ : ℝ → Cn n} {T : ℝ}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t ∧ γ t ∈ U) :
    ∃ R Φ, IsAugFlow F U γ T R Φ := by
  have : ∀ c0 ∈ Icc 0 T, ∃ r > 0, ∃ φ : ℝ → Cn (n + 1) → Cn (n + 1),
      (∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (φ t) (ball (aug (c0 : ℂ) (γ 0)) r)) ∧
      ∀ x ∈ ball (aug (c0 : ℂ) (γ 0)) r, φ 0 x = x ∧
        ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (φ · x) (augF F (φ t x)) (Icc 0 1) t ∧
          φ t x ∈ (Matrix.vecTail ⁻¹' U : Set (Cn (n + 1))) := by
    intro c0 hc0
    have h := flow_holo (isOpen_augW hU) (augF_diff hF) zero_le_one (base_curve hγ hc0)
    simp only [mul_zero] at h
    exact h
  choose! R hR Φ hΦ1 hΦ2 using this
  exact ⟨R, Φ, fun c0 hc0 => ⟨hR c0 hc0, hΦ1 c0 hc0 1 ⟨zero_le_one, le_rfl⟩, hΦ2 c0 hc0⟩⟩

section Glue

variable {n : ℕ} {F : Cn n → Cn n} {U : Set (Cn n)} {γ : ℝ → Cn n} {T : ℝ} {R : ℝ → ℝ}
  {Φ : ℝ → ℝ → Cn (n + 1) → Cn (n + 1)}

theorem consist (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hΦ : IsAugFlow F U γ T R Φ)
    {c0 c1 : ℝ} (hc0 : c0 ∈ Icc 0 T) (hc1 : c1 ∈ Icc 0 T) {v : Cn (n + 1)}
    (hv0 : v ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0)) (hv1 : v ∈ ball (aug (c1 : ℂ) (γ 0)) (R c1)) :
    EqOn (Φ c0 · v) (Φ c1 · v) (Icc 0 1) :=
  odeUniq (isOpen_augW hU) (augF_diff hF) (fun τ hτ => ((hΦ c0 hc0).2.2 v hv0).2 τ hτ)
    (fun τ hτ => ((hΦ c1 hc1).2.2 v hv1).2 τ hτ)
    (by rw [((hΦ c0 hc0).2.2 v hv0).1, ((hΦ c1 hc1).2.2 v hv1).1])

/-- The union of the balls on which the pieces live. -/
def augO (γ : ℝ → Cn n) (T : ℝ) (R : ℝ → ℝ) : Set (Cn (n + 1)) :=
  ⋃ c0 ∈ Icc 0 T, ball (aug (c0 : ℂ) (γ 0)) (R c0)

theorem isOpen_augO : IsOpen (augO γ T R) := isOpen_biUnion fun _ _ => isOpen_ball

open Classical in
/-- The glued augmented flow. -/
def Psi (γ : ℝ → Cn n) (T : ℝ) (R : ℝ → ℝ) (Φ : ℝ → ℝ → Cn (n + 1) → Cn (n + 1)) (τ : ℝ)
    (v : Cn (n + 1)) : Cn (n + 1) :=
  if h : ∃ c0 ∈ Icc 0 T, v ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0) then Φ h.choose τ v else 0

theorem Psi_eq (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hΦ : IsAugFlow F U γ T R Φ)
    {c0 : ℝ} (hc0 : c0 ∈ Icc 0 T) {v : Cn (n + 1)} (hv : v ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : Psi γ T R Φ τ v = Φ c0 τ v := by
  have h : ∃ c0 ∈ Icc 0 T, v ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0) := ⟨c0, hc0, hv⟩
  rw [Psi, dite_eq_left h]
  exact consist hU hF hΦ h.choose_spec.1 hc0 h.choose_spec.2 hv hτ

theorem Psi_diff (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hΦ : IsAugFlow F U γ T R Φ) :
    DifferentiableOn ℂ (Psi γ T R Φ 1) (augO γ T R) := by
  intro v hv
  simp only [augO, mem_iUnion] at hv
  obtain ⟨c0, hc0, hv⟩ := hv
  have hn : ball (aug (c0 : ℂ) (γ 0)) (R c0) ∈ 𝓝 v := isOpen_ball.mem_nhds hv
  have hd := ((hΦ c0 hc0).2.1 v hv).differentiableAt hn
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hn] with w hw
  exact Psi_eq hU hF hΦ hc0 hw ⟨zero_le_one, le_rfl⟩

theorem Psi_mem (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hΦ : IsAugFlow F U γ T R Φ)
    {v : Cn (n + 1)} (hv : v ∈ augO γ T R) : Matrix.vecTail (Psi γ T R Φ 1 v) ∈ U := by
  simp only [augO, mem_iUnion] at hv
  obtain ⟨c0, hc0, hv⟩ := hv
  rw [Psi_eq hU hF hΦ hc0 hv ⟨zero_le_one, le_rfl⟩]
  exact (((hΦ c0 hc0).2.2 v hv).2 1 ⟨zero_le_one, le_rfl⟩).2

theorem first_coord (hΦ : IsAugFlow F U γ T R Φ) {c0 : ℝ} (hc0 : c0 ∈ Icc 0 T)
    {v : Cn (n + 1)} (hv : v ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0)) :
    ∀ τ ∈ Icc (0 : ℝ) 1, Φ c0 τ v 0 = v 0 := by
  have h := (hΦ c0 hc0).2.2 v hv
  intro τ hτ
  have := constant_of_has_deriv_right_zero (f := fun τ => Φ c0 τ v 0) (a := 0) (b := 1)
    (fun τ hτ => (hasDerivWithinAt_pi.1 (h.2 τ hτ).1 0).continuousWithinAt) ?_ τ hτ
  · simpa [h.1] using this
  · intro τ hτ
    have := hasDerivWithinAt_pi.1 (h.2 τ (Ico_subset_Icc_self hτ)).1 0
    rw [augF_zero_coord] at this
    exact this.mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hτ.2) (Icc_subset_Icc hτ.1 le_rfl))

/-- Scaling: the glued flow at `(σ t, x)` is the augmented flow from `(t, x)` at time `σ`. -/
theorem scaling (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hΦ : IsAugFlow F U γ T R Φ)
    {t : ℂ} {x : Cn n} (hseg : ∀ σ ∈ Icc (0 : ℝ) 1, aug ((σ : ℂ) * t) x ∈ augO γ T R)
    {c0 : ℝ} (hc0 : c0 ∈ Icc 0 T) (hv : aug t x ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0)) :
    ∀ σ ∈ Icc (0 : ℝ) 1, Matrix.vecTail (Psi γ T R Φ 1 (aug ((σ : ℂ) * t) x)) =
      Matrix.vecTail (Φ c0 σ (aug t x)) := by
  intro σ hσ
  obtain ⟨c1, hc1, hw⟩ : ∃ c1 ∈ Icc 0 T,
      aug ((σ : ℂ) * t) x ∈ ball (aug (c1 : ℂ) (γ 0)) (R c1) := by
    simpa [augO] using hseg σ hσ
  rw [Psi_eq hU hF hΦ hc1 hw ⟨zero_le_one, le_rfl⟩]
  have hv' := (hΦ c0 hc0).2.2 _ hv
  have hfc := first_coord hΦ hc0 hv
  set A : ℝ → Cn (n + 1) := fun ρ => aug ((σ : ℂ) * t) (Matrix.vecTail (Φ c0 (σ * id ρ) (aug t x)))
    with hAdef
  have hmaps : MapsTo (fun ρ : ℝ => σ * id ρ) (Icc 0 1) (Icc 0 1) := fun ρ hρ =>
    ⟨mul_nonneg hσ.1 hρ.1, by simp only [id]; nlinarith [hσ.1, hσ.2, hρ.1, hρ.2]⟩
  have hA : ∀ ρ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt A (augF F (A ρ)) (Icc 0 1) ρ ∧
      A ρ ∈ (Matrix.vecTail ⁻¹' U : Set (Cn (n + 1))) := by
    intro ρ hρ
    have hm := hmaps hρ
    have hd := (hv'.2 _ hm).1.scomp ρ ((hasDerivWithinAt_id ρ (Icc 0 1)).const_mul σ) hmaps
    refine ⟨hasDerivWithinAt_pi.2 fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [hAdef, aug, Matrix.cons_val_zero, augF_zero_coord]
        exact hasDerivWithinAt_const _ _ _
      · have := hasDerivWithinAt_pi.1 hd j.succ
        rw [Pi.smul_apply, augF_succ, hfc _ hm] at this
        simp only [hAdef, aug, augF_succ, Matrix.cons_val_zero, Matrix.tail_cons]
        convert this using 1
        all_goals first
          | (funext ρ'; simp [Function.comp_def, Matrix.vecTail, aug])
          | (simp only [aug, Matrix.cons_val_zero, Complex.real_smul, mul_one, id]; ring)
    · simpa [hAdef, aug] using (hv'.2 _ hm).2
  have heq := odeUniq (isOpen_augW hU) (augF_diff hF)
    (fun τ hτ => ((hΦ c1 hc1).2.2 _ hw).2 τ hτ) hA
    (by rw [((hΦ c1 hc1).2.2 _ hw).1]; simp [hAdef, hv'.1])
  have h1 := heq ⟨zero_le_one, le_rfl⟩
  simp only at h1
  rw [h1]
  simp [hAdef]

end Glue

end ABC.S4.FlowComplexAux
