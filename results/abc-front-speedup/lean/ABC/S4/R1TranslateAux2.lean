import ABC.TubeProof
import ABC.S4.Defs

/-! R1 helpers: the real `z`-flow near the certified orbit, from the stage-3 crossing maps.
`c ↦ crossP a c` solves `dq/dz = zField q z`; the orbit of `p` is `2π`-periodic. -/

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.R1TranslateAux

section real

variable {p : E 2} (hp : CertFacts p)
include hp

lemma crossT_lip {a : E 2} (ha : a ∈ closedBall p r₀) {c c' : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7)
    (hc' : c' ∈ Icc (-7 : ℝ) 7) : |crossT a c - crossT a c'| ≤ |c - c'| / (19 / 10) := by
  obtain ⟨hu, hz⟩ := crossT_spec hp ha hc
  obtain ⟨hu', hz'⟩ := crossT_spec hp ha hc'
  rw [le_div_iff₀ (by norm_num)]
  rcases le_total (crossT a c) (crossT a c') with h | h
  · have := window_mono hp ha hu hu' h
    rw [hz, hz'] at this
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have := window_mono hp ha hu' hu h
    rw [hz, hz'] at this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

lemma crossT_mem_Ioo {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Ioo (-7 : ℝ) 7) :
    crossT a c ∈ Ioo (-4 : ℝ) 4 := by
  obtain ⟨hu, hz⟩ := crossT_spec hp ha (Ioo_subset_Icc_self hc)
  have h4 := window_mono hp ha (x := 0) (y := 4) (by norm_num) (by norm_num) (by norm_num)
  have h4' := window_mono hp ha (x := -4) (y := 0) (by norm_num) (by norm_num) (by norm_num)
  rw [zz_zero] at h4 h4'
  refine ⟨lt_of_le_of_ne hu.1 fun h => ?_, lt_of_le_of_ne hu.2 fun h => ?_⟩
  · rw [← h] at hz; linarith [hc.1]
  · rw [h] at hz; linarith [hc.2]

lemma crossT_zero {a : E 2} (ha : a ∈ closedBall p r₀) : crossT a 0 = 0 :=
  (crossT_unique hp ha (u := 0) (by norm_num) (zz_zero a)).symm

lemma crossP_zero {a : E 2} (ha : a ∈ closedBall p r₀) : crossP a 0 = a :=
  crossP_eq hp ha (u := 0) (by norm_num) (by rw [Γ_zero])

lemma hasDerivAt_crossT {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Ioo (-7 : ℝ) 7) :
    HasDerivAt (crossT a) (abcField (Γ (lift a 0) (crossT a c)) 2)⁻¹ c := by
  have hIcc : Icc (-7 : ℝ) 7 ∈ 𝓝 c := Icc_mem_nhds hc.1 hc.2
  have hcont : ContinuousAt (crossT a) c := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.1 hIcc
    refine ⟨min δ ε, lt_min hδ hε, fun y hy => ?_⟩
    have hy' : y ∈ Icc (-7 : ℝ) 7 := hδs (lt_of_lt_of_le hy (min_le_left _ _))
    have := crossT_lip hp ha hy' (Ioo_subset_Icc_self hc)
    rw [Real.dist_eq] at hy ⊢
    have h2 : |y - c| < ε := lt_of_lt_of_le hy (min_le_right _ _)
    have h3 : |y - c| / (19 / 10) ≤ |y - c| := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith [abs_nonneg (y - c)]
    linarith
  have hV := window_Vz hp ha (Ioo_subset_Icc_self (crossT_mem_Ioo hp ha hc))
  refine HasDerivAt.of_local_left_inverse hcont (hasDerivAt_z (Γ_orbit _) _)
    (by positivity) ?_
  filter_upwards [hIcc] with y hy
  exact (crossT_spec hp ha hy).2

lemma hasDerivAt_crossP {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Ioo (-7 : ℝ) 7) :
    HasDerivAt (fun c : ℝ => ofR (crossP a c)) (zField (ofR (crossP a c)) c) c := by
  set γ := Γ (lift a 0)
  have hτ := hasDerivAt_crossT hp ha hc
  have hz : γ (crossT a c) 2 = c := (crossT_spec hp ha (Ioo_subset_Icc_self hc)).2
  have hco : ∀ j : Fin 3, HasDerivAt (fun c => γ (crossT a c) j)
      (abcField (γ (crossT a c)) j * (abcField (γ (crossT a c)) 2)⁻¹) c := fun j =>
    ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt _
      (Γ_orbit (lift a 0) (crossT a c))).comp c hτ
  have hV : abcField (γ (crossT a c)) 2 =
      Real.sin (γ (crossT a c) 1) + Real.cos (γ (crossT a c) 0) := abcField_apply_two _
  have e0 : (fun c : ℝ => ofR (crossP a c) 0) = fun c => ((γ (crossT a c) 0 : ℝ) : ℂ) := by
    funext x; simp [ofR, crossP, γ]
  have e1 : (fun c : ℝ => ofR (crossP a c) 1) = fun c => ((γ (crossT a c) 1 : ℝ) : ℂ) := by
    funext x; simp [ofR, crossP, γ]
  have hq0 : ofR (crossP a c) 0 = ((γ (crossT a c) 0 : ℝ) : ℂ) := congrFun e0 c
  have hq1 : ofR (crossP a c) 1 = ((γ (crossT a c) 1 : ℝ) : ℂ) := congrFun e1 c
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun c : ℝ => ofR (crossP a c) 0) _ c
    rw [e0]
    convert (hco 0).ofReal_comp using 1
    simp only [zField, Matrix.cons_val_zero, Fin.zero_eta, hq0, hq1]
    rw [hV]
    simp only [abcField]
    simp [hz, div_eq_mul_inv]
  · show HasDerivAt (fun c : ℝ => ofR (crossP a c) 1) _ c
    rw [e1]
    convert (hco 1).ofReal_comp using 1
    simp only [zField, Matrix.cons_val_one, Fin.mk_one, hq0, hq1]
    rw [hV]
    simp only [abcField]
    simp [hz, div_eq_mul_inv]

lemma crossP_Vz {a : E 2} (ha : a ∈ closedBall p r₀) {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7) :
    19 / 10 ≤ Real.sin (crossP a c 1) + Real.cos (crossP a c 0) := by
  have := window_Vz hp ha (crossT_spec hp ha hc).1
  rw [abcField_apply_two] at this
  simpa [crossP] using this

lemma crossP_p_Vz {c : ℝ} (hc : c ∈ Icc (-7 : ℝ) 7) :
    192 / 100 ≤ Real.sin (crossP p c 1) + Real.cos (crossP p c 0) := by
  obtain ⟨T, -, -, -, -, hV⟩ := fixed_orbit hp
  have := hV (crossT p c)
  rw [abcField_apply_two] at this
  simpa [crossP] using this

/-- The certified orbit is `2π`-periodic in `z`. -/
lemma crossP_p_periodic {t : ℝ} (ht : |t| ≤ 7 / 10) : crossP p (t + 2 * π) = crossP p t := by
  have hp0 : p ∈ closedBall p r₀ := mem_closedBall_self r₀_pos.le
  obtain ⟨T, hT1, hT2, hT, -, -⟩ := fixed_orbit hp
  set γ := Γ (lift p 0)
  have hpi := Real.pi_lt_d2
  have hpi' := Real.pi_gt_three
  have htI : t ∈ Icc (-7 : ℝ) 7 := ⟨by linarith [(abs_le.1 ht).1], by linarith [(abs_le.1 ht).2]⟩
  have hper : ∀ s, γ (s + T) = γ s + latt 0 0 1 := by
    intro s
    have h1 : Γ (γ T) = fun s => γ (s + T) := Γ_Γ _ T
    have h2 : γ T = lift p 0 + latt 0 0 1 := by
      rw [hT]; exact ext3 (by simp) (by simp) (by simp)
    rw [h2, Γ_add_Lat _ (latt_mem_Lat 0 0 1)] at h1
    exact (congrFun h1 s).symm
  have hu := crossT_lip hp hp0 htI (by norm_num : (0 : ℝ) ∈ Icc (-7 : ℝ) 7)
  rw [crossT_zero hp hp0, sub_zero, sub_zero] at hu
  have hu' : |crossT p t| ≤ 7 / 19 := by
    rw [le_div_iff₀ (by norm_num)] at hu ⊢
    linarith
  have hab := abs_le.1 hu'
  apply crossP_eq hp hp0 (u := crossT p t + T) ⟨by linarith, by linarith⟩
  show γ (crossT p t + T) = _
  rw [hper, show γ (crossT p t) = _ from Γ_crossT hp hp0 htI]
  exact ext3 (by simp) (by simp) (by simp)

end real

end ABC.S4.R1TranslateAux
