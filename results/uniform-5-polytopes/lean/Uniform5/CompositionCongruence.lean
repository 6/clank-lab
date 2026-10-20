import Uniform5.CompositionGeometry
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Intrinsic congruence is Euclidean congruence

A distance-preserving equivalence of subsets of a finite-dimensional real
inner-product space extends to an ambient affine isometry. The construction
uses the Gram matrix of differences from one anchor point, then extends a
linear isometry of their span. No convexity or full-dimensionality assumption
is necessary.
-/

noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Equal Gram matrices imply equal norms of every finite linear combination. -/
theorem norm_linearCombination_eq_of_inner_eq (v : ι → E) (w : ι → F)
    (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) (c : ι →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ v c‖ = ‖Finsupp.linearCombination ℝ w c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [← real_inner_self_eq_norm_sq, Finsupp.linearCombination_apply,
    Finsupp.sum, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, h]

/-- The map between two families with equal Gram matrices extends linearly
and isometrically to the span of the first family. -/
noncomputable def gramRangeIsometry (v : ι → E) (w : ι → F)
    (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) :
    LinearMap.range (Finsupp.linearCombination ℝ v) →ₗᵢ[ℝ] F := by
  let A := Finsupp.linearCombination ℝ v
  let B := Finsupp.linearCombination ℝ w
  have hk : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    rw [← norm_linearCombination_eq_of_inner_eq v w h c]
    exact norm_eq_zero.mpr (LinearMap.mem_ker.mp hc)
  let L := ((LinearMap.ker A).liftQ B hk).comp A.quotKerEquivRange.symm.toLinearMap
  refine ⟨L, ?_⟩
  intro x
  obtain ⟨c, hc⟩ := x.property
  have hx : x = ⟨A c, LinearMap.mem_range_self A c⟩ := Subtype.ext hc.symm
  rw [hx]
  simpa [L, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply,
    A, B] using (norm_linearCombination_eq_of_inner_eq v w h c).symm

theorem gramRangeIsometry_apply (v : ι → E) (w : ι → F)
    (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) (c : ι →₀ ℝ) :
    gramRangeIsometry v w h
      ⟨Finsupp.linearCombination ℝ v c, LinearMap.mem_range_self _ c⟩ =
      Finsupp.linearCombination ℝ w c := by
  simp [gramRangeIsometry, LinearMap.quotKerEquivRange_symm_apply_image]

/-- Distances determine the Gram matrix after anchoring at one point. -/
theorem inner_sub_eq_of_isometry {P : Set E} {Q : Set F}
    (f : P ≃ᵢ Q) (a x y : P) :
    ⟪(x : E) - a, (y : E) - a⟫ =
      ⟪(f x : F) - f a, (f y : F) - f a⟫ := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  have hd (u v : P) : ‖(f u : F) - f v‖ = ‖(u : E) - v‖ := by
    simpa only [← dist_eq_norm, Subtype.dist_eq] using f.dist_eq u v
  simp only [sub_sub_sub_cancel_right, hd]

set_option maxHeartbeats 400000 in
/-- Every intrinsic isometry of subsets of the same finite-dimensional
Euclidean space is the restriction of an ambient affine isometry. -/
theorem isometryEquiv_extends_affineIsometryEquiv [FiniteDimensional ℝ E]
    {P Q : Set E} (f : P ≃ᵢ Q) :
    ∃ g : E ≃ᵃⁱ[ℝ] E, ∀ x : P, g x = f x := by
  classical
  by_cases hp : P.Nonempty
  · obtain ⟨a, ha⟩ := hp
    let a₀ : P := ⟨a, ha⟩
    let v : P → E := fun x => (x : E) - a
    let w : P → E := fun x => (f x : E) - f a₀
    have hgram : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫ :=
      fun i j => inner_sub_eq_of_isometry f a₀ i j
    let L : LinearMap.range (Finsupp.linearCombination ℝ v) →ₗᵢ[ℝ] E :=
      gramRangeIsometry v w hgram
    let M : E →ₗᵢ[ℝ] E := L.extend
    have hm (x : P) : M (v x) = w x := by
      have hv : Finsupp.linearCombination ℝ v (Finsupp.single x 1) = v x := by simp
      have hw : Finsupp.linearCombination ℝ w (Finsupp.single x 1) = w x := by simp
      have hv' : v x ∈ LinearMap.range (Finsupp.linearCombination ℝ v) :=
        ⟨Finsupp.single x 1, hv⟩
      calc
        M (v x) = L ⟨v x, hv'⟩ := L.extend_apply ⟨v x, hv'⟩
        _ = w x := by
          simpa only [hv, hw] using gramRangeIsometry_apply v w hgram (Finsupp.single x 1)
    let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ofSurjective M
      ((LinearMap.injective_iff_surjective (f := M.toLinearMap)).mp M.injective)
    let g : E ≃ᵃⁱ[ℝ] E :=
      (AffineIsometryEquiv.vaddConst ℝ a).symm.trans
        (e.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ (f a₀ : E)))
    refine ⟨g, ?_⟩
    intro x
    change M ((x : E) - a) + (f a₀ : E) = (f x : E)
    rw [show M ((x : E) - a) = (f x : E) - (f a₀ : E) from hm x]
    exact sub_add_cancel _ _
  · refine ⟨AffineIsometryEquiv.refl ℝ E, ?_⟩
    intro x
    exact (hp ⟨x, x.property⟩).elim

/-- Restricting an ambient Euclidean isometry gives intrinsic congruence. -/
theorem congruent_affineIsometryEquiv_image (g : E ≃ᵃⁱ[ℝ] F) (P : Set E) :
    Congruent P (g '' P) := by
  refine ⟨{ toEquiv := Equiv.image g.toEquiv P, isometry_toFun := ?_ }⟩
  intro x y
  exact g.isometry x y

/-- In finite-dimensional Euclidean space the metric definition of
`Congruent` is exactly congruence by an ambient rigid motion. -/
theorem congruent_iff_affineIsometryEquiv_image [FiniteDimensional ℝ E]
    (P Q : Set E) :
    Congruent P Q ↔ ∃ g : E ≃ᵃⁱ[ℝ] E, g '' P = Q := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨g, hg⟩ := isometryEquiv_extends_affineIsometryEquiv f
    refine ⟨g, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hg ⟨x, hx⟩]
      exact (f ⟨x, hx⟩).property
    · intro hy
      refine ⟨f.symm ⟨y, hy⟩, (f.symm ⟨y, hy⟩).property, ?_⟩
      rw [hg]
      exact congrArg Subtype.val (f.apply_symm_apply ⟨y, hy⟩)
  · rintro ⟨g, rfl⟩
    exact congruent_affineIsometryEquiv_image g P

/-- Even without assuming convexity, an intrinsic isometry preserves every
affine combination which belongs to its domain. -/
theorem isometryEquiv_map_lineMap [FiniteDimensional ℝ E]
    {P Q : Set E} (f : P ≃ᵢ Q) (x y : P) (t : ℝ)
    (h : AffineMap.lineMap (x : E) (y : E) t ∈ P) :
    (f ⟨AffineMap.lineMap (x : E) (y : E) t, h⟩ : E) =
      AffineMap.lineMap (f x : E) (f y : E) t := by
  obtain ⟨g, hg⟩ := isometryEquiv_extends_affineIsometryEquiv f
  rw [← hg ⟨_, h⟩]
  change g (AffineMap.lineMap (x : E) (y : E) t) = _
  calc
    _ = AffineMap.lineMap (g (x : E)) (g (y : E)) t :=
      g.toAffineEquiv.apply_lineMap x y t
    _ = _ := by rw [hg x, hg y]

/-- Sanity check: rigid translations satisfy intrinsic congruence. -/
theorem congruent_translation (P : Set E) (v : E) :
    Congruent P ((fun x => v + x) '' P) :=
  congruent_affineIsometryEquiv_image (AffineIsometryEquiv.constVAdd ℝ E v) P

omit [InnerProductSpace ℝ F] in
/-- Sanity check: a nondegenerate segment cannot be congruent to a point. -/
theorem not_congruent_segment_singleton {x y : E} (hxy : x ≠ y) (z : F) :
    ¬ Congruent (segment ℝ x y) ({z} : Set F) := by
  rintro ⟨f⟩
  let a : segment ℝ x y := ⟨x, left_mem_segment ℝ x y⟩
  let b : segment ℝ x y := ⟨y, right_mem_segment ℝ x y⟩
  have hab : f a = f b := Subtype.ext ((f a).property.trans (f b).property.symm)
  exact hxy (congrArg Subtype.val (f.injective hab))

end Uniform5.Composition
