import ABC.S4.R1Ham
import ABC.S4.PeriodMap
import ABC.TubeProof
import ABC.S4.R1TranslateAux6

/-! R1: translation to the periodic orbit. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

open R1TranslateAux in
theorem R1_translate {p : E 2} (hp : CertFacts p) :
    ∃ (ρ s : ℝ) (H₁ : C2 → ℂ → ℂ) (h₁ : OpenPartialHomeomorph (E 2) (E 2)) (P₁ : E 2 → E 2),
      0 < ρ ∧ 0 < s ∧ IsTPHam H₁ ρ s ∧ (∀ t, H₁ 0 t = 0 ∧ fderiv ℂ (H₁ · t) 0 = 0) ∧
      IsChart h₁ p ρ ∧ IsPeriodMap H₁ P₁ ρ ∧ ∀ x : E 2, ‖x‖ < ρ → retMap (h₁ x) = h₁ (P₁ x) := by
  -- the certified orbit in complex time, and the translated Hamiltonian `H1`
  obtain ⟨s, hs, M, Q, hper, hder, hbd, horb, hreal⟩ := complex_orbit hp
  have hO : OrbitData p s M Q := ⟨hs, hper, hder, hbd, horb, hreal⟩
  have hM := hO.M_nonneg
  have hp0 : p ∈ closedBall p r₀ := mem_closedBall_self r₀_pos.le
  have hpi := Real.pi_lt_d2
  have hρp : 0 < Real.sin (p 1) + Real.cos (p 0) := by
    have := crossP_p_Vz hp (c := 0) (by norm_num)
    rw [crossP_zero hp hp0] at this; linarith
  -- radii: `K₁` is the Lipschitz constant of the crossing maps
  set K₁ : ℝ := 4 * Real.exp 12 with hK₁def
  have hK₁ : 0 < K₁ := by positivity
  set δ₁ : ℝ := min (r1 M / (M + 2)) (r2 M) with hδ₁def
  have hδ₁ : 0 < δ₁ := lt_min (div_pos (r1_pos hM) (by linarith)) (r2_pos M)
  set εc : ℝ := min r₀ (δ₁ / K₁) with hεcdef
  have hεc : 0 < εc := lt_min r₀_pos (div_pos hδ₁ hK₁)
  obtain ⟨e, he, hpe, hsrc, hsymm, hfwd⟩ := real_chart hρp hεc
  obtain ⟨εs, hεs, hεs_sub⟩ := Metric.isOpen_iff.1 e.open_source p hpe
  have hep : e p = 0 := by rw [he, sub_self]
  have h0t : (0 : E 2) ∈ e.target := by rw [← hep]; exact e.map_source hpe
  obtain ⟨ρ₀, hρ₀, hρ₀_sub⟩ := Metric.isOpen_iff.1 e.open_target 0 h0t
  have hsymm0 : e.symm 0 = p := by rw [← hep, e.left_inv hpe]
  obtain ⟨ρ₁, hρ₁, hρ₁c⟩ :=
    Metric.continuousAt_iff.1 (e.continuousAt_symm h0t) (εs / K₁) (div_pos hεs hK₁)
  set ρ := min (min ρ₀ ρ₁) (r1 M) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ₀ hρ₁) (r1_pos hM)
  -- facts about `a = h₁ x`
  have hx_facts : ∀ x : E 2, ‖x‖ < ρ →
      x ∈ e.target ∧ e.symm x ∈ closedBall p r₀ ∧ phi (e.symm x) - phi p = x ∧
        dist (e.symm x) p < δ₁ / K₁ ∧ retMap (e.symm x) ∈ e.source ∧
        retMap (e.symm x) = crossP (e.symm x) (2 * π) := by
    intro x hx
    have hxt : x ∈ e.target :=
      hρ₀_sub (mem_ball_zero_iff.2 (lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_left _ _))))
    have ha : e.symm x ∈ e.source := e.map_target hxt
    have hdist : dist (e.symm x) p < εc := mem_ball.1 (hsrc ha)
    have hr0 : e.symm x ∈ closedBall p r₀ :=
      mem_closedBall.2 (hdist.le.trans (min_le_left _ _))
    have hs1 : dist (e.symm x) p < εs / K₁ := by
      have := hρ₁c (x := x) (by
        rw [dist_zero_right]; exact lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_right _ _)))
      rwa [hsymm0] at this
    have hret := retMap_eq_crossP hp hr0
    refine ⟨hxt, hr0, by rw [← he, e.right_inv hxt], hdist.trans_le (min_le_right _ _), ?_, hret⟩
    apply hεs_sub
    rw [hret, mem_ball, ← crossP_p_pos hp]
    calc _ ≤ K₁ * dist (e.symm x) p := crossP_lip hp hr0 hp0 mem_Icc_two_pi
      _ < K₁ * (εs / K₁) := mul_lt_mul_of_pos_left hs1 hK₁
      _ = εs := by field_simp
  refine ⟨ρ, s, H1 M s Q, e.symm, fun x => phi (retMap (e.symm x)) - phi p, hρ, hs,
    hO.isTPHam (min_le_right _ _), hO.H1_zero, ?_, ?_, ?_⟩
  · -- the chart
    refine ⟨hsymm0, ?_, e.symm.open_source, hsymm, ?_⟩
    · intro x hx
      exact hρ₀_sub (mem_ball_zero_iff.2
        (lt_of_lt_of_le (mem_ball_zero_iff.1 hx) ((min_le_left _ _).trans (min_le_left _ _))))
    · simpa using hfwd
  · -- the period map: the translated real orbit
    intro x hx
    obtain ⟨hxt, hr0, hea, hdist, -, hret⟩ := hx_facts x hx
    set a := e.symm x with ha_def
    let γ : ℝ → C2 := fun t => phiC (ofR (crossP a t)) - phiC (ofR (crossP p t))
    refine ⟨γ, ?_, ?_, ?_⟩
    · intro t ht
      have ht7 : t ∈ Ioo (-7 : ℝ) 7 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hts : (t : ℂ) ∈ strip s := by simpa [strip] using hs
      set qa := crossP a t
      set qp := crossP p t
      have hQt : Q t = ofR qp := horb t ht
      -- the derivative of `γ`
      have hda := ((hasFDerivAt_phiC (ofR qa)).restrictScalars ℝ).comp_hasDerivAt t
        (hasDerivAt_crossP hp hr0 ht7)
      have hdp := ((hasFDerivAt_phiC (ofR qp)).restrictScalars ℝ).comp_hasDerivAt t
        (hasDerivAt_crossP hp hp0 ht7)
      have hdγ := (hda.sub hdp).hasDerivWithinAt (s := Icc 0 (2 * π))
      -- `γ t` is small
      have hd : dist qa qp < δ₁ := by
        have h1 := crossP_lip hp hr0 hp0 (c := t) (Ioo_subset_Icc_self ht7)
        calc dist qa qp ≤ K₁ * dist a p := h1
          _ < K₁ * (δ₁ / K₁) := mul_lt_mul_of_pos_left hdist hK₁
          _ = δ₁ := by field_simp
      have hd0 : |qa 0 - qp 0| ≤ dist qa qp := abs_sub_le_dist2 qa qp 0
      have hd1 : |qa 1 - qp 1| ≤ dist qa qp := abs_sub_le_dist2 qa qp 1
      have hqp0 : |qp 0| ≤ M := by
        have := (hO.bound _ hts).1
        rw [hQt] at this
        have h2 := norm_le_pi_norm (ofR qp) 0
        simp only [ofR, Complex.norm_real, Real.norm_eq_abs] at h2
        linarith
      have hγt : γ t = ofR (phi qa - phi qp) := by
        simp only [γ, phiC_ofR, ofR_sub]; rfl
      have hγn : ‖γ t‖ < r1 M := by
        rw [hγt]
        have hb : ‖ofR (phi qa - phi qp)‖ ≤ (M + 2) * dist qa qp := by
          refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
          simp only [ofR, Complex.norm_real, Real.norm_eq_abs]
          fin_cases i
          · simp only [phi, PiLp.sub_apply]
            simp
            have e1 : qa 0 * Real.sin (qa 1) + Real.sin (qa 0) -
                (qp 0 * Real.sin (qp 1) + Real.sin (qp 0)) =
                (qa 0 - qp 0) * Real.sin (qa 1) + qp 0 * (Real.sin (qa 1) - Real.sin (qp 1)) +
                  (Real.sin (qa 0) - Real.sin (qp 0)) := by ring
            rw [e1]
            have s1 := Real.abs_sin_sub_sin_le (qa 1) (qp 1)
            have s0 := Real.abs_sin_sub_sin_le (qa 0) (qp 0)
            have hs := Real.abs_sin_le_one (qa 1)
            calc _ ≤ |(qa 0 - qp 0) * Real.sin (qa 1)| +
                  |qp 0 * (Real.sin (qa 1) - Real.sin (qp 1))| +
                  |Real.sin (qa 0) - Real.sin (qp 0)| := abs_add_three _ _ _
              _ ≤ dist qa qp * 1 + M * dist qa qp + dist qa qp := by
                  rw [abs_mul, abs_mul]
                  gcongr <;>
                    first
                    | exact hd0
                    | exact s1.trans hd1
                    | exact s0.trans hd0
              _ = (M + 2) * dist qa qp - 0 := by ring
              _ ≤ (M + 2) * dist qa qp := by linarith
          · simp only [phi, PiLp.sub_apply]
            simp
            nlinarith [dist_nonneg (x := qa) (y := qp)]
        calc _ ≤ (M + 2) * dist qa qp := hb
          _ < (M + 2) * δ₁ := mul_lt_mul_of_pos_left hd (by linarith)
          _ ≤ (M + 2) * (r1 M / (M + 2)) := by gcongr; exact min_le_left _ _
          _ = r1 M := by field_simp
      have hD : (γ t, Q t) ∈ Dset M := hO.mem_D hγn hts
      have hpsi : psi M (γ t) (Q t) = ofR qa := by
        refine psi_unique hM hD ?_ ?_ ?_
        · rw [hQt]; simp only [γ, phiC, ofR, qa, qp]; simp
        · rw [hQt]
          simp only [ofR, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact lt_of_le_of_lt hd0 (lt_of_lt_of_le hd (min_le_right _ _))
        · rw [hQt]; simp only [γ, qa, qp]; abel
      have hF := hO.hasFDerivAt_H1 hγn hts
      rw [hpsi] at hF
      have hsub : sympL (phiCD (ofR qa) (zField (ofR qa) t)) - sympL (Vf Q t) =
          sympL (phiCD (ofR qa) (zField (ofR qa) t) - Vf Q t) := by
        refine ContinuousLinearMap.ext fun ξ => ?_
        simp [sympL]; ring
      rw [hsub] at hF
      rw [hamVF_eq hF]
      simp only [Vf, hQt]
      exact hdγ
    · simp only [γ]
      rw [crossP_zero hp hr0, crossP_zero hp hp0, phiC_ofR, phiC_ofR, ← ofR_sub, hea]
    · simp only [γ]
      rw [crossP_p_pos hp, ← hret, phiC_ofR, phiC_ofR, ← ofR_sub]
  · -- the conjugacy
    intro x hx
    obtain ⟨-, -, -, -, hsrc', -⟩ := hx_facts x hx
    show retMap (e.symm x) = e.symm (phi (retMap (e.symm x)) - phi p)
    rw [← he, e.left_inv hsrc']

end ABC.S4
