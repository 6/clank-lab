import Uniform5.CompositionExposedFaces
import Uniform5.CompositionFigurePlacement

/-! The inner side of an actual facet's affine hyperplane contains the
entire parent polytope. A chart need only identify this hyperplane and one
strict inner point; containment is then a geometric theorem. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Orienting a face hyperplane with one point fixes its inner side. -/
theorem face_support_halfspace_of_affineSpan {P F : Set E}
    (hP : Convex ℝ P) (hF : IsConvexFace P F) (hne : F.Nonempty)
    (L : E →L[ℝ] ℝ) (b : ℝ)
    (hspan : (affineSpan ℝ F : Set E) = {x | L x = b})
    {y : E} (hy : y ∈ P) (hbelow : L y < b) :
    P ⊆ {x | L x ≤ b} := by
  intro x hx
  by_contra h
  have habove : b < L x := lt_of_not_ge h
  let t : ℝ := (b - L y) / (L x - L y)
  have hden : 0 < L x - L y := by linarith
  have ht : 0 < t := div_pos (by linarith) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  let z := (1 - t) • y + t • x
  have hzP : z ∈ P := hP hy hx (by linarith) ht.le (by ring)
  have hzL : L z = b := by
    dsimp [z]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have he : t * (L x - L y) = b - L y := div_mul_cancel₀ _ (ne_of_gt hden)
    nlinarith
  have hzF : z ∈ F := by
    rw [← face_affineSpan_inter hF hne]
    exact ⟨hzP, hspan.symm ▸ hzL⟩
  have hzopen : z ∈ openSegment ℝ y x :=
    ⟨1 - t, t, by linarith, ht, by ring, rfl⟩
  have hxF := (hF.2.2 hy hx hzF hzopen).2
  have hxA := subset_affineSpan ℝ F hxF
  rw [hspan] at hxA
  have hxL : L x = b := hxA
  linarith

/-- Actual vertex-figure points therefore satisfy every fan support
inequality once the chart identifies its facet hyperplane and inner side. -/
theorem vertexFigure_subset_facet_halfspace {P F : Set E}
    (hP : FinitePolytope P) (hF : Facet P F)
    (L : E →L[ℝ] ℝ) (b : ℝ)
    (hspan : (affineSpan ℝ F : Set E) = {x | L x = b})
    {y : E} (hy : y ∈ P) (hbelow : L y < b) (v c : E) :
    vertexFigure P v c ⊆ {x | L x ≤ b} := by
  exact (show vertexFigure P v c ⊆ P from Set.inter_subset_left).trans
    (face_support_halfspace_of_affineSpan (finitePolytope_convex hP)
      hF.1 hF.2.1 L b hspan hy hbelow)

end Uniform5.Composition
