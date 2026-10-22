/- Adapted from proof/lean/ThomsonN9/Alignment.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.LocalGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Orthogonal least-squares alignment and its rotational gauge. -/

namespace ThomsonN10.Local

set_option autoImplicit false

abbrev OrthonormalFrame := Fin 3 → R3

def orthonormalFrameSet : Set OrthonormalFrame := {b | Orthonormal ℝ b}

noncomputable def frameAction (b : OrthonormalFrame) (x : R3) : R3 :=
  ∑ j, x j • b j

noncomputable def alignmentObjective (x p : Configuration) (b : OrthonormalFrame) : ℝ :=
  ∑ i, ‖frameAction b (x i)-p i‖^2

theorem orthonormalFrameSet_nonempty : orthonormalFrameSet.Nonempty := by
  exact ⟨EuclideanSpace.basisFun (Fin 3) ℝ, (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal⟩

theorem orthonormalFrameSet_closed : IsClosed orthonormalFrameSet := by
  have hc : IsClosed (⋂ i : Fin 3, ⋂ j : Fin 3,
      {b : OrthonormalFrame | inner ℝ (b i) (b j) = if i = j then 1 else 0}) := by
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
  convert hc using 1
  ext b
  simp only [orthonormalFrameSet, Set.mem_ofPred_eq, Set.mem_iInter, orthonormal_iff_ite]

theorem orthonormalFrame_norm_le_one (b : OrthonormalFrame) (hb : Orthonormal ℝ b) :
    ‖b‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  exact fun i => (hb.norm_eq_one i).le

theorem orthonormalFrameSet_compact : IsCompact orthonormalFrameSet := by
  apply (isCompact_closedBall (0 : OrthonormalFrame) 1).of_isClosed_subset
    orthonormalFrameSet_closed
  intro b hb
  simpa only [Metric.mem_closedBall, dist_zero_right] using orthonormalFrame_norm_le_one b hb

noncomputable def frameBasis (b : OrthonormalFrame) (hb : Orthonormal ℝ b) :
    OrthonormalBasis (Fin 3) ℝ R3 :=
  OrthonormalBasis.mk hb
    (hb.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [R3])).ge

noncomputable def frameIsometry (b : OrthonormalFrame) (hb : Orthonormal ℝ b) : R3 ≃ₗᵢ[ℝ] R3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).equiv (frameBasis b hb) (Equiv.refl (Fin 3))

theorem frameIsometry_apply (b : OrthonormalFrame) (hb : Orthonormal ℝ b) (x : R3) :
    frameIsometry b hb x = frameAction b x := by
  simp only [frameIsometry, OrthonormalBasis.equiv_apply_euclideanSpace,
    frameBasis, OrthonormalBasis.coe_mk, frameAction]

theorem frameAction_isometry (Q : R3 ≃ₗᵢ[ℝ] R3) (x : R3) :
    frameAction (fun j => Q (EuclideanSpace.basisFun (Fin 3) ℝ j)) x = Q x := by
  unfold frameAction
  calc
    _ = Q (∑ j, x j • EuclideanSpace.basisFun (Fin 3) ℝ j) := by simp
    _ = Q x := by
      congr 1
      simpa only [EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x

theorem alignmentObjective_continuous (x p : Configuration) :
    Continuous (alignmentObjective x p) := by
  unfold alignmentObjective frameAction
  fun_prop

theorem exists_minimal_alignment (x p : Configuration) :
    ∃ Q : R3 ≃ₗᵢ[ℝ] R3, ∀ T : R3 ≃ₗᵢ[ℝ] R3,
      (∑ i, ‖Q (x i)-p i‖^2) ≤ ∑ i, ‖T (x i)-p i‖^2 := by
  obtain ⟨b, hb, hmin⟩ := orthonormalFrameSet_compact.exists_isMinOn
    orthonormalFrameSet_nonempty (alignmentObjective_continuous x p).continuousOn
  refine ⟨frameIsometry b hb, ?_⟩
  intro T
  have hT : Orthonormal ℝ (fun j => T (EuclideanSpace.basisFun (Fin 3) ℝ j)) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.comp_linearIsometryEquiv T
  have h := hmin hT
  change alignmentObjective x p b ≤
    alignmentObjective x p (fun j => T (EuclideanSpace.basisFun (Fin 3) ℝ j)) at h
  have heq (i : Fin 10) : ‖frameIsometry b hb (x i)-p i‖^2 =
      ‖frameAction b (x i)-p i‖^2 :=
    congrArg (fun v : R3 => ‖v-p i‖^2) (frameIsometry_apply b hb (x i))
  simp_rw [heq]
  simpa only [alignmentObjective, frameAction_isometry] using h

theorem quadratic_linear_coefficient_zero (A B : ℝ)
    (h : ∀ t : ℝ, 0 ≤ A*t^2+B*t) : B = 0 := by
  have hA : 0 ≤ A := by nlinarith [h 1, h (-1)]
  by_cases hAz : A = 0
  · subst A
    nlinarith [h 1, h (-1)]
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hn := mul_nonneg (h (-B/(2*A))) (show 0 ≤ 4*A by positivity)
  have hid : (A*(-B/(2*A))^2+B*(-B/(2*A)))*(4*A) = -B^2 := by
    field_simp [hAz]
    ring
  rw [hid] at hn
  exact sq_eq_zero_iff.mp (le_antisymm (by linarith) (sq_nonneg B))

def IsMinimalAlignment (x p : Configuration) : Prop :=
  ∀ T : R3 ≃ₗᵢ[ℝ] R3, (∑ i, ‖x i-p i‖^2) ≤ ∑ i, ‖T (x i)-p i‖^2

theorem exists_isMinimalAlignment (x p : Configuration) :
    ∃ Q : R3 ≃ₗᵢ[ℝ] R3, IsMinimalAlignment (fun i => Q (x i)) p := by
  obtain ⟨Q, hQ⟩ := exists_minimal_alignment x p
  refine ⟨Q, fun T => ?_⟩
  simpa only [LinearIsometryEquiv.trans_apply] using hQ (Q.trans T)

noncomputable def planeFrame (a b : Fin 3) (c s : ℝ) : OrthonormalFrame := fun j =>
  if j = a then c • EuclideanSpace.basisFun (Fin 3) ℝ a +
    s • EuclideanSpace.basisFun (Fin 3) ℝ b
  else if j = b then (-s) • EuclideanSpace.basisFun (Fin 3) ℝ a +
    c • EuclideanSpace.basisFun (Fin 3) ℝ b
  else EuclideanSpace.basisFun (Fin 3) ℝ j

theorem planeFrame_orthonormal (a b : Fin 3) (hab : a ≠ b) (c s : ℝ)
    (hcs : c^2+s^2=1) : Orthonormal ℝ (planeFrame a b c s) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [PiLp.inner_apply, Real.inner_apply]
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals
    fin_cases i <;> fin_cases j <;>
      simp [planeFrame, Fin.sum_univ_three] <;>
      nlinarith

noncomputable def planeIsometry (a b : Fin 3) (hab : a ≠ b) (c s : ℝ)
    (hcs : c^2+s^2=1) : R3 ≃ₗᵢ[ℝ] R3 :=
  frameIsometry (planeFrame a b c s) (planeFrame_orthonormal a b hab c s hcs)

theorem planeIsometry_inner (a b : Fin 3) (hab : a ≠ b) (c s : ℝ)
    (hcs : c^2+s^2=1) (x p : R3) :
    inner ℝ (planeIsometry a b hab c s hcs x) p = inner ℝ x p +
      (c-1)*(x a*p a+x b*p b)+s*(x a*p b-x b*p a) := by
  rw [planeIsometry, frameIsometry_apply]
  simp only [frameAction, sum_inner, real_inner_smul_left]
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals
    simp [planeFrame, Fin.sum_univ_three, PiLp.inner_apply]
    ring

theorem planeIsometry_displacement (a b : Fin 3) (hab : a ≠ b) (c s : ℝ)
    (hcs : c^2+s^2=1) (x p : R3) :
    ‖planeIsometry a b hab c s hcs x-p‖^2-‖x-p‖^2 =
      2*(1-c)*(x a*p a+x b*p b)-2*s*(x a*p b-x b*p a) := by
  rw [norm_sub_sq_real, norm_sub_sq_real, LinearIsometryEquiv.norm_map,
    planeIsometry_inner]
  ring

theorem minimal_alignment_skew_zero {x p : Configuration} (hmin : IsMinimalAlignment x p)
    (a b : Fin 3) (hab : a ≠ b) :
    (∑ i, ((x i) a*(p i) b-(x i) b*(p i) a)) = 0 := by
  let A : ℝ := ∑ i, ((x i) a*(p i) a+(x i) b*(p i) b)
  let B : ℝ := ∑ i, ((x i) a*(p i) b-(x i) b*(p i) a)
  have hquad : ∀ t : ℝ, 0 ≤ A*t^2+(-B)*t := by
    intro t
    have hd : 0 < 1+t^2 := by positivity
    have hcs : ((1-t^2)/(1+t^2))^2+(2*t/(1+t^2))^2=1 := by
      field_simp [ne_of_gt hd]
      ring
    have hm := hmin (planeIsometry a b hab ((1-t^2)/(1+t^2)) (2*t/(1+t^2)) hcs)
    have hdiff : 0 ≤ ∑ i, (‖planeIsometry a b hab ((1-t^2)/(1+t^2))
        (2*t/(1+t^2)) hcs (x i)-p i‖^2-‖x i-p i‖^2) := by
      rw [Finset.sum_sub_distrib]
      linarith
    simp_rw [planeIsometry_displacement] at hdiff
    have hid : (∑ i, (2*(1-(1-t^2)/(1+t^2))*((x i) a*(p i) a+(x i) b*(p i) b)-
        2*(2*t/(1+t^2))*((x i) a*(p i) b-(x i) b*(p i) a))) =
        4*(A*t^2+(-B)*t)/(1+t^2) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change 2*(1-(1-t^2)/(1+t^2))*A-2*(2*t/(1+t^2))*B = _
      field_simp [ne_of_gt hd]
      ring
    rw [hid] at hdiff
    have hh := (le_div_iff₀ hd).mp hdiff
    linarith
  have hB := quadratic_linear_coefficient_zero A (-B) hquad
  change B=0
  linarith

theorem minimal_alignment_displacement_skew_zero {x p : Configuration}
    (hmin : IsMinimalAlignment x p) (a b : Fin 3) :
    (∑ i, (((x i) a-(p i) a)*(p i) b-((x i) b-(p i) b)*(p i) a)) = 0 := by
  by_cases hab : a=b
  · subst b
    simp
  have h := minimal_alignment_skew_zero hmin a b hab
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem minimal_alignment_tangent_skew_zero {x p : Configuration}
    (hmin : IsMinimalAlignment x p) (a b : Fin 3) :
    (∑ i, ((tangentDisplacement (p i) (x i-p i)) a*(p i) b-
      (tangentDisplacement (p i) (x i-p i)) b*(p i) a)) = 0 := by
  convert minimal_alignment_displacement_skew_zero hmin a b using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [tangentDisplacement, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end ThomsonN10.Local
