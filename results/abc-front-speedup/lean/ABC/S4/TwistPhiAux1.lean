import ABC.S4.R123
import ABC.S4.HoloDeriv

/-! T2 helper: a period map with an equilibrium at `0` fixes `0` (ODE uniqueness). -/

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.TwistPhiAux

/-- Uniqueness for `y' = H y`, `H` holomorphic on open `W`; only `g` need stay in `W`, and `f`
need only solve the equation while it is in `W`. -/
theorem odeUniq' {m : ℕ} {H : Cn m → Cn m} {W : Set (Cn m)} (hW : IsOpen W)
    (hH : DifferentiableOn ℂ H W) {f g : ℝ → Cn m} {a b : ℝ}
    (hfc : ContinuousOn f (Icc a b))
    (hf : ∀ t ∈ Icc a b, f t ∈ W → HasDerivWithinAt f (H (f t)) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (H (g t)) (Icc a b) t ∧ g t ∈ W)
    (h0 : f a = g a) : EqOn f g (Icc a b) := by
  intro τ hτ
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).1.continuousWithinAt
  have hS : IsClosed ({t | f t = g t} ∩ Icc a b) := by
    rw [inter_comm]
    exact (hfc.prodMk hgc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
  refine hS.Icc_subset_of_forall_mem_nhdsWithin h0 ?_ hτ
  rintro x ⟨hx, hxI⟩
  have hxI' : x ∈ Icc a b := Ico_subset_Icc_self hxI
  have hx' : f x = g x := hx
  have hfW : f x ∈ W := hx' ▸ (hg x hxI').2
  obtain ⟨K, t₀, ht₀, hL₀⟩ := FlowComplexAux.locLip hW hH hfW
  set t := t₀ ∩ W
  have ht : t ∈ 𝓝 (f x) := inter_mem ht₀ (hW.mem_nhds hfW)
  have hL : LipschitzOnWith K H t := hL₀.mono inter_subset_left
  have hft : f ⁻¹' t ∈ 𝓝[Icc a b] x := hfc x hxI' ht
  have hgt : g ⁻¹' t ∈ 𝓝[Icc a b] x := hgc x hxI' (by rw [← hx']; exact ht)
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
      (fun τ hτ => (hf τ (hsub (Ico_subset_Icc_self hτ)) (hmem τ hτ).1.2).mono_of_mem_nhdsWithin
        (hnhd τ hτ))
      (fun τ hτ => (hmem τ hτ).1) (hgc.mono hsub)
      (fun τ hτ => (hg τ (hsub (Ico_subset_Icc_self hτ))).1.mono_of_mem_nhdsWithin (hnhd τ hτ))
      (fun τ hτ => (hmem τ hτ).2) hx
  exact mem_of_superset (Ioo_mem_nhdsGT hxc) (fun τ hτ => key ⟨hτ.1.le, hτ.2.le⟩)


/-- `w ↦ (0, w)`. -/
def ι : C2 →L[ℂ] Cn 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => Matrix.vecCons 0 w
      map_add' := fun v w => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun c w => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }

theorem ι_apply (w : C2) : ι w = Matrix.vecCons 0 w := rfl

/-- `H` read on the augmented space `(t, w)`. -/
def augK (H : C2 → ℂ → ℂ) (u : Cn 3) : ℂ := H (Matrix.vecTail u) (u 0)

/-- The augmented field `(t, w)' = (1, J∇H(·, t)(w))`, with the partial derivative written
through `augK`. -/
def augG (H : C2 → ℂ → ℂ) (u : Cn 3) : Cn 3 :=
  Matrix.vecCons 1 ![fderiv ℂ (augK H) u (ι (Pi.single 1 1)),
    -fderiv ℂ (augK H) u (ι (Pi.single 0 1))]

def augW (ρ s : ℝ) : Set (Cn 3) := {u | Matrix.vecTail u ∈ polydisc ρ ∧ u 0 ∈ strip s}

theorem differentiable_tailHead :
    Differentiable ℂ (fun u : Cn 3 => (Matrix.vecTail u, u 0)) :=
  FlowComplexAux.differentiable_tail.prodMk
    (differentiable_apply (𝕜 := ℂ) (F' := fun _ : Fin 3 => ℂ) 0)

theorem isOpen_polydisc (ρ : ℝ) : IsOpen (polydisc ρ) := by
  have : polydisc ρ = ball (0 : C2) ρ := by ext w; simp [polydisc]
  rw [this]; exact isOpen_ball

theorem isOpen_strip (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem isOpen_augW (ρ s : ℝ) : IsOpen (augW ρ s) :=
  ((isOpen_polydisc ρ).prod (isOpen_strip s)).preimage differentiable_tailHead.continuous

theorem augK_diff {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) :
    DifferentiableOn ℂ (augK H) (augW ρ s) :=
  hH.holo.comp differentiable_tailHead.differentiableOn (fun _ hu => hu)

theorem augG_diff {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) :
    DifferentiableOn ℂ (augG H) (augW ρ s) := by
  have hd := HoloDeriv.differentiableOn_fderiv (isOpen_augW ρ s) (augK_diff hH)
  refine differentiableOn_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [augG]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simpa [augG] using hd.clm_apply (differentiableOn_const _)
    · have : k = 0 := Subsingleton.elim _ _
      subst this
      simpa [augG] using (hd.clm_apply (differentiableOn_const _)).neg

/-- The partial derivative in `w` is the full derivative of `augK` along `(0, ·)`. -/
theorem fderiv_partial {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) {c : ℂ} {w : C2}
    (hu : Matrix.vecCons c w ∈ augW ρ s) (v : C2) :
    fderiv ℂ (fun w' => H w' c) w v = fderiv ℂ (augK H) (Matrix.vecCons c w) (ι v) := by
  have hj : (fun w' : C2 => Matrix.vecCons c w') = fun w' => ι w' + Matrix.vecCons c 0 := by
    funext w'; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [ι_apply]
  have hjd : HasFDerivAt (fun w' : C2 => Matrix.vecCons c w') ι w := by
    rw [hj]; exact ι.hasFDerivAt.add_const _
  have hK : HasFDerivAt (augK H) (fderiv ℂ (augK H) (Matrix.vecCons c w))
      (Matrix.vecCons c w) :=
    ((augK_diff hH _ hu).differentiableAt ((isOpen_augW ρ s).mem_nhds hu)).hasFDerivAt
  have hcomp := hK.comp w hjd
  have he : (augK H ∘ fun w' : C2 => Matrix.vecCons c w') = fun w' => H w' c := by
    funext w'; simp [augK]
  rw [he] at hcomp
  rw [hcomp.fderiv]; rfl

theorem hamVF_eq_augG {H : C2 → ℂ → ℂ} {ρ s : ℝ} (hH : IsTPHam H ρ s) {c : ℂ} {w : C2}
    (hu : Matrix.vecCons c w ∈ augW ρ s) :
    Matrix.vecCons 1 (hamVF (fun w' => H w' c) w) = augG H (Matrix.vecCons c w) := by
  simp only [hamVF, augG, fderiv_partial hH hu]

/-- A period map whose Hamiltonian has an equilibrium at `0` fixes `0`. -/
theorem period_map_zero {H : C2 → ℂ → ℂ} {ρ s r : ℝ} {P : E 2 → E 2} (hρ : 0 < ρ) (hs : 0 < s)
    (hH : IsTPHam H ρ s) (h0 : ∀ t, fderiv ℂ (H · t) 0 = 0) (hP : IsPeriodMap H P r)
    (hr : 0 < r) : P 0 = 0 := by
  obtain ⟨γ, hγ, hγ0, hγT⟩ := hP 0 (by simpa using hr)
  set f : ℝ → Cn 3 := fun t => Matrix.vecCons (t : ℂ) (γ t)
  set g : ℝ → Cn 3 := fun t => Matrix.vecCons (t : ℂ) 0
  have hofR : ∀ t : ℝ, HasDerivWithinAt (fun t : ℝ => (t : ℂ)) 1 (Icc 0 (2 * π)) t :=
    fun t => Complex.ofRealCLM.hasDerivAt.hasDerivWithinAt
  have hfd : ∀ t ∈ Icc 0 (2 * π), HasDerivWithinAt f
      (Matrix.vecCons 1 (hamVF (fun w => H w t) (γ t))) (Icc 0 (2 * π)) t := by
    intro t ht
    refine hasDerivWithinAt_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [f] using hofR t
    · simpa [f] using hasDerivWithinAt_pi.1 (hγ t ht) j
  have hgW : ∀ t : ℝ, g t ∈ augW ρ s := fun t => by
    refine ⟨?_, ?_⟩
    · simpa [g, polydisc] using hρ
    · simpa [g, strip] using hs
  have hg : ∀ t ∈ Icc 0 (2 * π), HasDerivWithinAt g (augG H (g t)) (Icc 0 (2 * π)) t ∧
      g t ∈ augW ρ s := by
    intro t ht
    refine ⟨?_, hgW t⟩
    rw [← hamVF_eq_augG hH (hgW t)]
    refine hasDerivWithinAt_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [g] using hofR t
    · have : hamVF (fun w => H w (t : ℂ)) 0 = 0 := by
        ext k; refine Fin.cases ?_ (fun l => ?_) k <;> simp [hamVF, h0]
      simpa [g, this] using hasDerivWithinAt_const t (Icc 0 (2 * π)) (0 : ℂ)
  have hf : ∀ t ∈ Icc 0 (2 * π), f t ∈ augW ρ s →
      HasDerivWithinAt f (augG H (f t)) (Icc 0 (2 * π)) t := by
    intro t ht hW
    rw [← hamVF_eq_augG hH hW]
    exact hfd t ht
  have heq := odeUniq' (isOpen_augW ρ s) (augG_diff hH)
    (fun t ht => (hfd t ht).continuousWithinAt) hf hg
    (by have : ofR 0 = 0 := by ext i; simp [ofR]
        simp [f, g, hγ0, this]) (right_mem_Icc.2 (by positivity))
  have h2 : γ (2 * π) = 0 := by
    have := congrArg Matrix.vecTail heq
    simpa [f, g] using this
  rw [hγT] at h2
  ext i
  have := congrFun h2 i
  simpa [ofR] using this

end ABC.S4.TwistPhiAux
