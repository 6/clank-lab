/- Adapted from proof/lean/ThomsonN9/CandidateAlignment.lean,
 aravindkarthigeyan/thomson-n9-lean @
 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.CandidateGeometry
import ThomsonN10.Local.GramAlignment
namespace ThomsonN10.Local

set_option autoImplicit false

theorem candidate_anchor_inner (h : CandidateParameter) :
    inner ℝ (candidate h 2) (candidate h 3) = (h : ℝ)^2 ∧
    inner ℝ (candidate h 2) (candidate h 6) =
      (1-(h : ℝ)^2)*Real.sqrt 2/2-(h : ℝ)^2 ∧
    inner ℝ (candidate h 3) (candidate h 6) =
      (1-(h : ℝ)^2)*Real.sqrt 2/2-(h : ℝ)^2 := by
  obtain ⟨hl,hu⟩ := height_bounds h
  have hh : |(h : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hpair (i j : Fin 10) :
      2-2*inner ℝ (candidate h i) (candidate h j) = pairSq h (pairClass i j) := by
    have hd := candidate_distance_sq h hh i j
    change ‖candidate h i-candidate h j‖^2 = _ at hd
    rw [norm_sub_sq_real, candidate_unit h i,candidate_unit h j] at hd
    linarith
  have h23 := hpair 2 3
  have h26 := hpair 2 6
  have h36 := hpair 3 6
  norm_num [pairSq,pairClass] at h23 h26 h36
  constructor
  · linarith
  constructor <;> nlinarith

theorem candidate_anchor_bounds (h : CandidateParameter) :
    |inner ℝ (candidate h 2) (candidate h 3)| ≤ (19/100 : ℝ) ∧
    |inner ℝ (candidate h 2) (candidate h 6)| ≤ (41/100 : ℝ) ∧
    |inner ℝ (candidate h 3) (candidate h 6)| ≤ (41/100 : ℝ) := by
  obtain ⟨hl,hu⟩ := height_bounds h
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsl : (7/5 : ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsu : Real.sqrt 2 ≤ (17/12 : ℝ) := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsqlo : (42/100 : ℝ)^2 ≤ (h : ℝ)^2 := by nlinarith
  have hsqhi : (h : ℝ)^2 ≤ (43/100 : ℝ)^2 := by nlinarith
  have hmlo : 0 ≤ (Real.sqrt 2-7/5)*(h : ℝ)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hmhi : 0 ≤ (17/12-Real.sqrt 2)*(h : ℝ)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  obtain ⟨h23,h26,h36⟩ := candidate_anchor_inner h
  rw [h23,h26,h36]
  constructor
  · rw [abs_of_nonneg (sq_nonneg _)]
    linarith
  have hc : |(1-(h : ℝ)^2)*Real.sqrt 2/2-(h : ℝ)^2| ≤ (41/100 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith
  exact ⟨hc,hc⟩

theorem candidate_gram_close_minimal_alignment (h : CandidateParameter)
    {x : Configuration} {δ : ℝ} (hx : ∀ i, ‖x i‖=1)
    (hδ : 0 ≤ δ) (hδu : δ ≤ (1/10000 : ℝ))
    (hg : ∀ i j, |inner ℝ (x i) (x j)-inner ℝ (candidate h i) (candidate h j)| ≤ δ) :
    ∃ Q : R3 ≃ₗᵢ[ℝ] R3, IsMinimalAlignment (fun i => Q (x i)) (candidate h) ∧
      (∑ i, ‖Q (x i)-candidate h i‖^2) ≤ (10000*δ)^2 := by
  obtain ⟨hp23,hp26,hp36⟩ := candidate_anchor_bounds h
  have hc (i j : Fin 10) : |inner ℝ (x i) (x j)| ≤
      δ+|inner ℝ (candidate h i) (candidate h j)| := by
    have ht := abs_add_le
      (inner ℝ (x i) (x j)-inner ℝ (candidate h i) (candidate h j))
      (inner ℝ (candidate h i) (candidate h j))
    have heq : (inner ℝ (x i) (x j)-inner ℝ (candidate h i) (candidate h j))+
        inner ℝ (candidate h i) (candidate h j) = inner ℝ (x i) (x j) := by ring
    rw [heq] at ht
    linarith [hg i j]
  exact gram_close_exists_minimal_alignment 2 3 6 hx (candidate_unit h) hδ hg
    (by linarith [hc 2 3]) (by linarith [hc 2 6]) (by linarith [hc 3 6])
    (by linarith) (by linarith) (by linarith)

end ThomsonN10.Local
