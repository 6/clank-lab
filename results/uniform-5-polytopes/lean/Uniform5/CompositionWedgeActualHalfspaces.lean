import Uniform5.CompositionWedgeNormalization
import Uniform5.CompositionRidgeSpanning
import Uniform5.CompositionFacetNormals

/-! Actual incident facets supply W's whole supporting cone hyperplanes.
Their inner-side containment is proved from the actual convex parent. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

/-- An actual facet section together with the root spans the parent facet. -/
theorem actual_facet_root_figure_span {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v : Space 5}
    (hv : v ∈ P.extremePoints ℝ) (hvK : v ∈ K) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    affineSpan ℝ (insert v (K ∩ vertexFigure P v c)) = affineSpan ℝ K := by
  dsimp only
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let Q := vertexFigure P v c
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hR := uniform_intrinsicRadius_pos hP.1
  have hfig := (unitUniform_vertexFigure_facet_correspondence (n := 2) hP hv).1 K hK hvK
  have hdQ : affineDimension Q = 4 := by
    have hd := finitePolytope_unit_vertexFigure_dimension (uniform_finitePolytope hP.1)
      hv c (intrinsicRadius P) hs hP.2 (by simpa using uniform_dimension hP.1) (by simp)
    simpa [Space] using hd
  have hvout : v ∉ affineSpan ℝ Q := by
    intro hh
    have he := unitUniform5_vertexFigure_affineSpan hP (intrinsicRadius P) hR hs hv
    change (affineSpan ℝ Q : Set (Space 5)) = _ at he
    change v ∈ (affineSpan ℝ Q : Set (Space 5)) at hh
    rw [he] at hh
    change ⟪v - c, v - c⟫ = intrinsicRadius P ^ 2 - 1 / 2 at hh
    rw [real_inner_self_eq_norm_sq, hs v hv] at hh
    linarith
  apply affineSpan_insert_eq_of_dimension_gap Set.inter_subset_left hfig.2.1
  · have hkdim := hK.2.2
    have hfdim := hfig.2.2
    rw [uniform_dimension hP.1] at hkdim
    change affineDimension (K ∩ Q) + 1 = affineDimension Q at hfdim
    rw [hdQ] at hfdim
    change affineDimension (K ∩ Q) + 1 = affineDimension K
    omega
  · exact hvK
  · intro hm
    exact hvout (affineSpan_mono ℝ Set.inter_subset_right hm)

namespace Wedge

/-- The actual facet normal gives both a legitimate finite W supporting
halfspace and containment of the entire actual polytope in that halfspace. -/
theorem actual_facet_supporting_halfspace {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v : Space 5}
    (hv : v ∈ P.extremePoints ℝ) (hvK : v ∈ K)
    (F : CaseB.WFanGeometry (Space 5)) (hvF : F.v = v)
    (hcF : F.centre = vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (hRF : F.radius = intrinsicRadius P) (hpoints : (F.vertices : Set (Space 5)) ⊆ P) :
    ∃ H, SupportingHalfspace (normalize F)
      (K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) H ∧ P ⊆ H := by
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let a := vertexCentroid (vertices K (finitePolytope_face (uniform_finitePolytope hP.1)
    hK.1 hK.2.1))
  obtain ⟨hac, hplane, hbound⟩ := uniform_facet_hyperplane_and_support hP.1 hK
    (by rw [uniform_dimension hP.1]; simp [Space])
  change a ≠ c at hac
  change (affineSpan ℝ K : Set (Space 5)) = {x | ⟪a - c, x - a⟫ = 0} at hplane
  change ∀ x ∈ P, ⟪a - c, x - a⟫ ≤ 0 at hbound
  let L := innerSL ℝ (a - c)
  have hvzero : ⟪a - c, v - a⟫ = 0 := by
    have hh := subset_affineSpan ℝ K hvK
    change v ∈ (affineSpan ℝ K : Set (Space 5)) at hh
    rwa [hplane] at hh
  have hshift (x : Space 5) : L (x - v) = ⟪a - c, x - a⟫ := by
    change ⟪a - c, x - v⟫ = _
    have he : x - a = (x - v) + (v - a) := by abel
    rw [he, inner_add_right, hvzero, add_zero]
  have hL : L ≠ 0 := by
    intro he
    have hh := congrArg (fun f : Space 5 →L[ℝ] ℝ => f (a - c)) he
    change ⟪a - c, a - c⟫ = 0 at hh
    exact hac (sub_eq_zero.mp (inner_self_eq_zero.mp hh))
  let H : Set (Space 5) := {x | L (x - v) ≤ 0}
  have hPH : P ⊆ H := by
    intro x hx
    change L (x - v) ≤ 0
    rw [hshift]
    exact hbound x hx
  refine ⟨H, ⟨L, hL, ?_, ?_, ?_, ?_⟩, hPH⟩
  · change H = {x | L (x - F.v) ≤ 0}
    rw [hvF]
  · change (affineSpan ℝ (insert F.v (K ∩ vertexFigure P v c)) : Set (Space 5)) = _
    rw [hvF, actual_facet_root_figure_span hP hK hv hvK, hplane]
    ext x
    change ⟪a - c, x - a⟫ = 0 ↔ L (x - F.v) = 0
    rw [hvF, hshift]
  · intro p hp
    change L (p - F.v) ≤ 0
    rw [hvF]
    exact hPH (hpoints hp)
  · change L ((1 / F.radius) • (F.centre - F.v)) < 0
    rw [map_smul, smul_eq_mul, hRF, hcF, hvF, hshift]
    have he : ⟪a - c, c - a⟫ = -‖a - c‖ ^ 2 := by
      rw [show c - a = -(a - c) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
    change (1 / intrinsicRadius P) * ⟪a - c, c - a⟫ < 0
    rw [he]
    exact mul_neg_of_pos_of_neg (one_div_pos.mpr (uniform_intrinsicRadius_pos hP.1))
      (neg_neg_of_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hac))))

/-- Every supporting halfspace allowed by the literal finite fan geometry
contains the actual parent once its facet hull is the actual section. -/
theorem actual_supporting_halfspace_contains {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v : Space 5}
    (hv : v ∈ P.extremePoints ℝ) (hvK : v ∈ K)
    (F : CaseB.WFanGeometry (Space 5)) (hvF : F.v = v)
    (hcF : F.centre = vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (hRF : F.radius = intrinsicRadius P) {H : Set (Space 5)}
    (hH : SupportingHalfspace (normalize F)
      (K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) H) :
    P ⊆ H := by
  obtain ⟨L, _, hH, hspan, _, hstrict⟩ := hH
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  have hR : 0 < F.radius := hRF.symm ▸ uniform_intrinsicRadius_pos hP.1
  have hl : L c < L v := by
    change L ((1 / F.radius) • (F.centre - F.v)) < 0 at hstrict
    rw [map_smul, smul_eq_mul, hcF, hvF] at hstrict
    have hh : L (c - v) < 0 := by
      nlinarith [one_div_pos.mpr hR]
    rw [map_sub] at hh
    linarith
  have hsp : (affineSpan ℝ K : Set (Space 5)) = {p | L p = L v} := by
    change (affineSpan ℝ (insert F.v (K ∩ vertexFigure P v c)) : Set (Space 5)) = _ at hspan
    rw [hvF, actual_facet_root_figure_span hP hK hv hvK] at hspan
    simpa only [normalize, hvF, map_sub, sub_eq_zero] using hspan
  have hcP : c ∈ P := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior
    (uniform_finitePolytope hP.1))
  have hbound := face_support_halfspace_of_affineSpan (finitePolytope_convex
    (uniform_finitePolytope hP.1)) hK.1 hK.2.1 L (L v) hsp hcP hl
  intro p hp
  rw [hH]
  change L (p - F.v) ≤ 0
  rw [hvF, map_sub]
  exact sub_nonpos.mpr (hbound hp)

end Wedge
end Uniform5.Composition
