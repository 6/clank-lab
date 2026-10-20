import Uniform5.CompositionFaces
import Uniform5.PolytopeFaces
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Exposedness of the geometric faces of a finite polytope

The proof separates the affine span of a face from the convex hull of
vertices outside it. No exposure premise is added to the face definition.
-/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A relative interior point of a face prevents its affine span from
meeting the parent convex set anywhere outside that face. -/
theorem face_affineSpan_inter [FiniteDimensional ℝ E] {P F : Set E}
    (hF : IsConvexFace P F) (hne : F.Nonempty) :
    P ∩ (affineSpan ℝ F : Set E) = F := by
  obtain ⟨c, hc⟩ := hne.intrinsicInterior hF.1
  obtain ⟨c, hc, rfl⟩ := hc
  have hcF : (c : E) ∈ F := (show c ∈ Subtype.val ⁻¹' F from interior_subset hc)
  apply Set.Subset.antisymm
  · rintro x ⟨hxP, hxA⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc)
    let t : ℝ := ε / (2 * (‖x - (c : E)‖ + 1))
    have ht : 0 < t := div_pos hε (by positivity)
    let z : affineSpan ℝ F := ⟨AffineMap.lineMap (c : E) x (-t),
      AffineMap.lineMap_mem _ c.property hxA⟩
    have hzdist : dist z c < ε := by
      change dist (AffineMap.lineMap (c : E) x (-t)) (c : E) < ε
      rw [AffineMap.lineMap_apply_module', dist_eq_norm, add_sub_cancel_right,
        norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
      dsimp [t]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (show 0 < 2 * (‖x - (c : E)‖ + 1) by positivity)).mpr
      nlinarith [norm_nonneg (x - (c : E))]
    have hzF : (z : E) ∈ F := hball hzdist
    have hcseg : (c : E) ∈ openSegment ℝ x (z : E) := by
      refine ⟨t / (1 + t), 1 / (1 + t), div_pos ht (by positivity),
        div_pos (by norm_num) (by positivity), ?_, ?_⟩
      · field_simp
        ring
      · dsimp [z]
        rw [AffineMap.lineMap_apply_module]
        simp only [smul_add, smul_smul, sub_neg_eq_add]
        have h1 : 1 / (1 + t) * (1 + t) = 1 := by field_simp
        have h2 : 1 / (1 + t) * -t = -(t / (1 + t)) := by ring
        rw [h1, h2, one_smul, neg_smul]
        abel
    exact (hF.2.2 hxP (hF.2.1 hzF) hcF hcseg).1
  · intro x hx
    exact ⟨hF.2.1 hx, subset_affineSpan ℝ F hx⟩

/-- A linear functional bounded above on an affine subspace is constant
there; otherwise its restriction to a line would be unbounded. -/
theorem linear_constant_on_affine_of_bounded (A : AffineSubspace ℝ E)
    (L : E →L[ℝ] ℝ) {b : ℝ} (hL : ∀ x ∈ A, L x < b)
    {c : E} (hc : c ∈ A) : ∀ x ∈ A, L x = L c := by
  intro x hx
  by_contra hne
  let t := (b - L c + 1) / (L x - L c)
  have hden : L x - L c ≠ 0 := sub_ne_zero.mpr hne
  have hh := hL (AffineMap.lineMap c x t) (AffineMap.lineMap_mem _ hc hx)
  rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at hh
  have ht : t * (L x - L c) = b - L c + 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ hden
  nlinarith

/-- Every geometric face of a finite convex polytope in Euclidean space
is exposed by a continuous linear functional. -/
theorem finitePolytope_face_isExposed [FiniteDimensional ℝ E]
    {P F : Set E} (hP : FinitePolytope P) (hF : IsConvexFace P F) :
    IsExposed ℝ P F := by
  obtain ⟨V, _, rfl⟩ := hP
  exact Uniform5.finite_convexFace_isExposed V hF

end Uniform5.Composition
