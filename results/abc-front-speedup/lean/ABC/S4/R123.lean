import ABC.S4.R1Translate
import ABC.S4.R2
import ABC.S4.R3
import ABC.S4.NonRes
import ABC.S4.R123Aux3

/-! R1–R3 combined. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

set_option maxHeartbeats 1000000 in
theorem R123 {p : E 2} (hp : CertFacts p) : ∃ ν b R ρ s C h₀ P', BNF p ν b R ρ s C h₀ P' := by
  have h2π : (2 * π : ℝ) ∈ Icc (0 : ℝ) (2 * π) := ⟨by positivity, le_rfl⟩
  have h2πc : (((2 * π : ℝ)) : ℂ) = 0 + 2 * (π : ℂ) := by push_cast; ring
  -- R1, the trace and non-resonance
  obtain ⟨ρ₁, s₁, H₁, h₁, P₁, hρ₁, hs₁, hH₁, h0₁, hch₁, hP₁, hconj₁⟩ := R1_translate hp
  have hvf₁ : ∀ t : ℝ, hamVF (fun w => H₁ w t) 0 = 0 := fun t =>
    R123Aux.hamVF_zero_of_fderiv (h0₁ t).2
  have hP0 : P₁ 0 = 0 := R123Aux.periodMap_zero hH₁ hs₁ hρ₁ hvf₁ hP₁
  obtain ⟨hsm, -⟩ := period_map_smooth hρ₁ hs₁ hH₁ (fun t => R123Aux.hamVF_zero_of_fderiv (h0₁ t).2)
    hP₁ hρ₁
  obtain ⟨M, hM, htr1, htr2⟩ := hp.trace
  have hjtr : jtr P₁ 0 = LinearMap.trace ℝ (E 2) (M : E 2 →ₗ[ℝ] E 2) :=
    R123Aux.jtr_eq_of_conj hch₁ hρ₁ hP0 (hsm.differentiableAt (by simp)) hconj₁ hM
  have hell : |jtr P₁ 0| < 2 := by
    rw [hjtr, abs_lt]; constructor <;> linarith
  -- R2, R3
  obtain ⟨ρ₂, s₂, ν, C₂, Q, H₂, hρ₂, hs₂, hH₂, hB₂, hQd, hQper, hQdet, hQreal, hcos, htr₂⟩ :=
    R2_floquet hρ₁ hs₁ hH₁ h0₁ hP₁ hell
  have hnr : NonRes4 ν :=
    nonres_of_trace (tr := jtr P₁ 0) (by rw [hjtr]; linarith) (by rw [hjtr]; linarith) hcos
  obtain ⟨ρ₃, s₃, C₃, b, R, Ψ, hρ₃, hs₃, hK, hR, hΨd, hΨreal, hΨper, hΨ0, hΨid, htr₃⟩ :=
    R3_bnf hρ₂ hs₂ hH₂ hB₂ hnr
  -- `G = Q(0) ∘ Ψ(0)`: holomorphic, `G 0 = 0`, `DG(0) = Q(0)` invertible
  have hΨ0d : DifferentiableOn ℂ (Ψ 0) (polydisc ρ₃) := by
    have : DifferentiableOn ℂ (fun w => (fun q : ℂ × C2 => Ψ q.1 q.2) ((0 : ℂ), w))
        (polydisc ρ₃) :=
      hΨd.comp ((differentiable_const _).prodMk differentiable_id).differentiableOn
        (fun w hw => ⟨by simp [strip, hs₃], hw⟩)
    simpa using this
  have hp3 : IsOpen (polydisc ρ₃) := R123Aux.isOpen_polydisc ρ₃
  have h0p3 : (0 : C2) ∈ polydisc ρ₃ := by simpa [polydisc] using hρ₃
  set QL : C2 →L[ℂ] C2 := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Q 0)) with hQLdef
  have hQL : ∀ w, QL w = (Q 0).mulVec w := fun w => rfl
  set G : C2 → C2 := fun w => (Q 0).mulVec (Ψ 0 w) with hGdef
  have hGQL : G = QL ∘ Ψ 0 := rfl
  have hGd : DifferentiableOn ℂ G (polydisc ρ₃) := by
    rw [hGQL]; exact QL.differentiable.comp_differentiableOn hΨ0d
  have hG0 : G 0 = 0 := by simp [G, hΨ0]
  have hGder : HasFDerivAt G QL 0 := by
    have h1 : HasFDerivAt (Ψ 0) (ContinuousLinearMap.id ℂ C2) 0 := by
      rw [← hΨid 0]
      exact (hΨ0d.differentiableAt (hp3.mem_nhds h0p3)).hasFDerivAt
    have := QL.hasFDerivAt.comp 0 h1
    simpa [hGQL] using this
  have hQinj : Function.Injective QL := by
    intro u v huv
    have hu : IsUnit (Q 0) := by
      rw [Matrix.isUnit_iff_isUnit_det, hQdet 0]; exact isUnit_one
    exact Matrix.mulVec_injective_iff_isUnit.2 hu huv
  set QLe : C2 ≃L[ℂ] C2 :=
    (LinearEquiv.ofInjectiveEndo (QL : C2 →ₗ[ℂ] C2) hQinj).toContinuousLinearEquiv
  have hQLe : (QLe : C2 →L[ℂ] C2) = QL := by ext x; rfl
  have hGstrict : HasStrictFDerivAt G (QLe : C2 →L[ℂ] C2) 0 := by
    have h := (R123Aux.analyticAt hp3 hGd h0p3).hasStrictFDerivAt
    rwa [hGder.fderiv, ← hQLe] at h
  set Gh := hGstrict.toOpenPartialHomeomorph G
  have hGh : ⇑Gh = G := rfl
  obtain ⟨η, hη, hηG⟩ := Metric.isOpen_iff.1 Gh.open_source 0
    hGstrict.mem_toOpenPartialHomeomorph_source
  -- `L = Re ∘ G ∘ ofR`, a local real-analytic diffeomorphism
  set L : E 2 → E 2 := fun x => R123Aux.reL (G (R123Aux.ofRL x)) with hLdef
  have hLreal : ∀ x : E 2, ‖x‖ < ρ₃ → ofR (L x) = G (ofR x) := by
    intro x hx
    apply R123Aux.ofR_reL
    intro i
    have h1 := hΨreal x (lt_of_le_of_lt (R123Aux.norm_ofR_le x) hx)
    fin_cases i <;>
      simp [G, R123Aux.ofRL_apply, Complex.mul_im, hQreal, h1]
  have hL0 : L 0 = 0 := by simp [L, hG0]
  have hLa : AnalyticOnNhd ℝ L (ball 0 ρ₃) := by
    intro x hx
    have hx' : R123Aux.ofRL x ∈ polydisc ρ₃ :=
      lt_of_le_of_lt (R123Aux.norm_ofR_le x) (by simpa using hx)
    have hGa := (R123Aux.analyticAt hp3 hGd hx').restrictScalars (𝕜 := ℝ)
    exact R123Aux.reL.analyticAt _ |>.comp (hGa.comp (R123Aux.ofRL.analyticAt x))
  have hLder : HasFDerivAt L (R123Aux.reL.comp ((QL.restrictScalars ℝ).comp R123Aux.ofRL)) 0 := by
    have hG' : HasFDerivAt G (QL.restrictScalars ℝ) (R123Aux.ofRL 0) := by
      rw [map_zero]; exact hGder.restrictScalars ℝ
    exact R123Aux.reL.hasFDerivAt.comp 0 (hG'.comp 0 R123Aux.ofRL.hasFDerivAt)
  have hLinj : Function.Injective (fderiv ℝ L 0) := by
    rw [hLder.fderiv]
    intro u v huv
    have hreal : ∀ y : E 2, ∀ i, (QL (ofR y) i).im = 0 := by
      intro y i
      simp [hQL, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_im, hQreal, ofR]
    have h1 : QL (ofR u) = QL (ofR v) := by
      rw [← R123Aux.ofR_reL (hreal u), ← R123Aux.ofR_reL (hreal v)]
      simpa [R123Aux.ofRL_apply] using congrArg ofR huv
    exact R123Aux.ofR_injective (hQinj h1)
  obtain ⟨Lh, hLh, h0Lh, hLhsub, hLha, hLhs⟩ := R123Aux.exists_localHomeo hLa hρ₃ hLinj hη
  -- uniform smallness on `[0, 2π]`
  set O : Set (ℂ × C2) := strip (min s₂ s₃) ×ˢ polydisc ρ₃
  have hO : IsOpen O := (R123Aux.isOpen_strip _).prod hp3
  have hOsub : O ⊆ strip s₃ ×ˢ polydisc ρ₃ := prod_mono
    (fun t (ht : |t.im| < min s₂ s₃) => show |t.im| < s₃ from lt_of_lt_of_le ht (min_le_right _ _))
    subset_rfl
  have hΨc : ContinuousOn (fun q : ℂ × C2 => Ψ q.1 q.2) O := hΨd.continuousOn.mono hOsub
  have hKO : ∀ t ∈ Icc (0 : ℝ) (2 * π), ((t : ℂ), (0 : C2)) ∈ O :=
    fun t _ => ⟨R123Aux.real_mem_strip (lt_min hs₂ hs₃) t, h0p3⟩
  obtain ⟨δ₂, hδ₂, hδ₂O⟩ := R123Aux.small_near hO hΨc
    (fun t ht => ⟨hKO t ht, hΨ0 _⟩) hρ₂
  have hQΨc : ContinuousOn (fun q : ℂ × C2 => (Q q.1).mulVec (Ψ q.1 q.2)) O := by
    have hQ' : ContinuousOn (fun q : ℂ × C2 => Q q.1) O :=
      hQd.continuousOn.comp continuousOn_fst
        (fun q (hq : q ∈ O) => show |q.1.im| < s₂ from
          lt_of_lt_of_le (show |q.1.im| < min s₂ s₃ from hq.1) (min_le_left _ _))
    refine continuousOn_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_id.matrix_elem i j).comp_continuousOn hQ').mul
      ((continuous_apply j).comp_continuousOn hΨc)
  obtain ⟨δ₁, hδ₁, hδ₁O⟩ := R123Aux.small_near hO hQΨc
    (fun t ht => ⟨hKO t ht, by simp [hΨ0]⟩) hρ₁
  have h0tgt : (0 : E 2) ∈ Lh.target := by
    have := Lh.map_source h0Lh
    rwa [hLh, hL0] at this
  have hrGc : ContinuousAt (fun w => R123Aux.reL (G w)) 0 :=
    R123Aux.reL.continuous.continuousAt.comp
      (hGd.differentiableAt (hp3.mem_nhds h0p3)).continuousAt
  obtain ⟨δ₅, hδ₅, hδ₅T⟩ := Metric.mem_nhds_iff.1
    (hrGc.preimage_mem_nhds (by rw [hG0, map_zero]; exact Lh.open_target.mem_nhds h0tgt))
  -- K-solutions from small real data
  set ρK := min (min ρ₃ δ₁) (min (min δ₂ η) δ₅)
  have hρK : 0 < ρK := by positivity
  have hKmono : ∀ ρ' s', ρ' ≤ ρ₃ → s' ≤ s₃ → IsTPHam (Kbnf ν b R) ρ' s' := fun ρ' s' h1 h2 =>
    ⟨hK.holo.mono (prod_mono (fun w hw => lt_of_lt_of_le hw h1)
      (fun t ht => lt_of_lt_of_le ht h2)), fun x t hx => hK.real x t (lt_of_lt_of_le hx h1), hK.per⟩
  have hvfK : ∀ t : ℝ, hamVF (fun w => Kbnf ν b R w t) 0 = 0 := fun t =>
    R123Aux.hamVF_zero_of_fderiv (R123Aux.hasFDerivAt_zero_of_sq_bound (lt_min hρ₃ one_pos)
      (R123Aux.Kbnf_sq_bound hR (R123Aux.real_mem_strip hs₃ t))).fderiv
  obtain ⟨rK, hrK, hex⟩ := R123Aux.exists_solves (hKmono ρK s₃ (by simp [ρK]) le_rfl) hs₃ hρK
    hvfK (T := 2 * π) (by positivity)
  -- the final radius
  have hLc : ContinuousAt L 0 := (hLa 0 (mem_ball_self hρ₃)).continuousAt
  obtain ⟨δc, hδc, hδcL⟩ := Metric.continuousAt_iff.1 hLc ρ₁ hρ₁
  have h0src : (0 : E 2) ∈ (Lh.trans h₁).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨h0Lh, ?_⟩
    rw [mem_preimage, hLh, hL0]
    exact hch₁.2.1 (mem_ball_self hρ₁)
  obtain ⟨δd, hδd, hδdS⟩ := Metric.isOpen_iff.1 (Lh.trans h₁).open_source 0 h0src
  set ρ := min (min rK ρ₃) (min δc δd)
  have hρ : 0 < ρ := by positivity
  have hρ3 : ρ ≤ ρ₃ := (min_le_left _ _).trans (min_le_right _ _)
  set P' : E 2 → E 2 := fun x => Lh.symm (P₁ (L x))
  -- core: the K-solution from `x` ends at `P' x`
  have core : ∀ x : E 2, ‖x‖ < ρ → ∃ γ : ℝ → C2, Solves (Kbnf ν b R) γ 0 (2 * π) ∧
      γ 0 = ofR x ∧ γ (2 * π) = ofR (P' x) ∧ ‖L x‖ < ρ₁ ∧ P₁ (L x) ∈ Lh.target := by
    intro x hx
    have hxr : ‖ofR x‖ < rK :=
      lt_of_le_of_lt (R123Aux.norm_ofR_le x) (hx.trans_le ((min_le_left _ _).trans
        (min_le_left _ _)))
    have hx3 : ‖x‖ < ρ₃ := hx.trans_le hρ3
    have hLx : ‖L x‖ < ρ₁ := by
      have := hδcL (x := x) (by
        rw [dist_zero_right]
        exact hx.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      rwa [hL0, dist_zero_right] at this
    obtain ⟨γ, hγ, hγ0, hγin⟩ := hex (ofR x) hxr
    have hγb : ∀ t ∈ Icc (0 : ℝ) (2 * π), ‖γ t‖ < ρ₃ ∧ ‖γ t‖ < δ₁ ∧ ‖γ t‖ < δ₂ ∧
        ‖γ t‖ < η ∧ ‖γ t‖ < δ₅ := by
      intro t ht
      have h := hγin t ht
      simp only [polydisc, mem_ofPred_eq, ρK, lt_min_iff] at h
      exact ⟨h.1.1, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩
    have hγ3 := htr₃ γ 0 (2 * π) hγ (fun t ht => (hγb t ht).1)
    have hψin : ∀ t ∈ Icc (0 : ℝ) (2 * π), Ψ t (γ t) ∈ polydisc ρ₂ := fun t ht =>
      (hδ₂O t ht (γ t) (hγb t ht).2.2.1).2
    have hδ := htr₂ _ 0 (2 * π) hγ3 hψin
    have hδin : ∀ t ∈ Icc (0 : ℝ) (2 * π), (Q t).mulVec (Ψ t (γ t)) ∈ polydisc ρ₁ := fun t ht =>
      (hδ₁O t ht (γ t) (hγb t ht).2.1).2
    have hδ0 : (Q ((0 : ℝ) : ℂ)).mulVec (Ψ ((0 : ℝ) : ℂ) (γ 0)) = ofR (L x) := by
      rw [hLreal x hx3, hγ0]; simp [G]
    obtain ⟨δ', hδ', hδ'0, hδ'T⟩ := hP₁ (L x) hLx
    have heq := R123Aux.solves_unique hH₁ hs₁ hδ hδ' (by rw [hδ'0]; exact hδ0) hδin h2π
    have hGγ : G (γ (2 * π)) = ofR (P₁ (L x)) := by
      rw [← hδ'T, ← heq]
      simp only [G]
      rw [h2πc, hQper 0, hΨper 0]
    have hT : P₁ (L x) ∈ Lh.target := by
      have := hδ₅T (show γ (2 * π) ∈ ball 0 δ₅ by
        rw [mem_ball_zero_iff]; exact (hγb _ h2π).2.2.2.2)
      rwa [mem_preimage, hGγ, R123Aux.reL_ofR] at this
    refine ⟨γ, hγ, hγ0, ?_, hLx, hT⟩
    -- injectivity of `G` near `0`
    have hx'src := Lh.map_target hT
    have hx'b := hLhsub hx'src
    rw [mem_ball_zero_iff, lt_min_iff] at hx'b
    have hGx' : G (ofR (P' x)) = G (γ (2 * π)) := by
      rw [hGγ, ← hLreal _ hx'b.2]
      congr 1
      show L (Lh.symm (P₁ (L x))) = P₁ (L x)
      have := Lh.right_inv hT; rw [hLh] at this; exact this
    have hm1 : ofR (P' x) ∈ Gh.source :=
      hηG (mem_ball_zero_iff.2 (lt_of_le_of_lt (R123Aux.norm_ofR_le _) hx'b.1))
    have hm2 : γ (2 * π) ∈ Gh.source := hηG (mem_ball_zero_iff.2 (hγb _ h2π).2.2.2.1)
    exact (Gh.injOn hm1 hm2 (by rw [hGh]; exact hGx')).symm
  refine ⟨ν, b, R, ρ, min s₃ 1, C₃, Lh.trans h₁, P', ?_⟩
  refine ⟨⟨hρ, lt_min hs₃ one_pos, min_le_right _ _⟩, hKmono ρ _ hρ3 (min_le_left _ _),
    fun w hw t ht => hR w (lt_of_lt_of_le hw hρ3) t
      (lt_of_lt_of_le (show |t.im| < min s₃ 1 from ht) (min_le_left _ _)), hnr,
    R123Aux.isChart_trans hch₁ (by rw [hLh]; exact hL0) hLha hLhs
      ((ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans hδdS), ?_, ?_⟩
  · intro x hx
    obtain ⟨γ, hγ, hγ0, hγT, -, -⟩ := core x hx
    exact ⟨γ, hγ, hγ0, hγT⟩
  · intro x hx
    obtain ⟨-, -, -, -, hLx, hT⟩ := core x hx
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, Function.comp_apply, hLh,
      hconj₁ _ hLx]
    congr 1
    show P₁ (L x) = L (Lh.symm (P₁ (L x)))
    have := Lh.right_inv hT; rw [hLh] at this; exact this.symm

end ABC.S4
