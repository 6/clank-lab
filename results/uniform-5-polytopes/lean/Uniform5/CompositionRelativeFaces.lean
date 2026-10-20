import Uniform5.CompositionFacetContainment
import Uniform5.CompositionVertices

/-! Relative interior and strict incidence for actual geometric faces. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If an extreme subset contains a relative interior point of a set in
the parent, it contains that entire set. The proof extends a segment a
small distance past the interior point inside its own affine span. -/
theorem subset_of_intrinsicInterior_mem_extreme {P F G : Set E}
    (hFP : F ⊆ P) (hG : IsExtreme ℝ P G) {c : E}
    (hc : c ∈ intrinsicInterior ℝ F) (hcG : c ∈ G) : F ⊆ G := by
  obtain ⟨a, ha, rfl⟩ := hc
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let t : ℝ := ε / (2 * (‖x - (a : E)‖ + 1))
  have ht : 0 < t := div_pos hε (by positivity)
  let z : affineSpan ℝ F := ⟨AffineMap.lineMap (a : E) x (-t),
    AffineMap.lineMap_mem _ a.property (subset_affineSpan ℝ F hx)⟩
  have hzdist : dist z a < ε := by
    change dist (AffineMap.lineMap (a : E) x (-t)) (a : E) < ε
    rw [AffineMap.lineMap_apply_module', dist_eq_norm, add_sub_cancel_right,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (show 0 < 2 * (‖x - (a : E)‖ + 1) by positivity)).mpr
    nlinarith [norm_nonneg (x - (a : E))]
  have hzF : (z : E) ∈ F := hball hzdist
  have haseg : (a : E) ∈ openSegment ℝ x (z : E) := by
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
  exact (hG.2 (hFP hx) (hFP hzF) hcG haseg).1

/-- The relative interior of the parent is disjoint from every proper
actual face, even when the ambient Euclidean space has larger dimension. -/
theorem intrinsicInterior_not_mem_proper_face {P F : Set E}
    (hF : IsConvexFace P F) (hproper : F ≠ P) {c : E}
    (hc : c ∈ intrinsicInterior ℝ P) : c ∉ F := by
  intro hcF
  exact hproper (hF.2.1.antisymm
    (subset_of_intrinsicInterior_mem_extreme Set.Subset.rfl hF.2 hc hcF))

/-- A face containing a relative interior point of another actual face
contains that whole face. -/
theorem face_subset_of_intrinsicInterior_mem {P F G : Set E}
    (hF : IsConvexFace P F) (hG : IsConvexFace P G) {c : E}
    (hc : c ∈ intrinsicInterior ℝ F) (hcG : c ∈ G) : F ⊆ G :=
  subset_of_intrinsicInterior_mem_extreme hF.2.1 hG.2 hc hcG

/-- Relative interiors of distinct facets lie strictly off each other's
supporting hyperplanes inside the parent polytope. -/
theorem facet_intrinsicInterior_not_mem_other [FiniteDimensional ℝ E]
    {P F G : Set E} (hF : Facet P F) (hG : Facet P G) (hne : F ≠ G)
    {c : E} (hc : c ∈ intrinsicInterior ℝ F) : c ∉ G := by
  intro hcG
  have hFG := face_subset_of_intrinsicInterior_mem hF.1 hG.1 hc hcG
  have hless := face_affineDimension_lt (face_restrict hF.1 hG.1.2.1 hFG) hF.2.1 hne
  have hdF := hF.2.2
  have hdG := hG.2.2
  omega

/-- The same strictness stated for the whole affine supporting hyperplane. -/
theorem facet_intrinsicInterior_not_mem_other_span [FiniteDimensional ℝ E]
    {P F G : Set E} (hF : Facet P F) (hG : Facet P G) (hne : F ≠ G)
    {c : E} (hc : c ∈ intrinsicInterior ℝ F) : c ∉ affineSpan ℝ G := by
  intro hcG
  apply facet_intrinsicInterior_not_mem_other hF hG hne hc
  rw [← face_affineSpan_inter hG.1 hG.2.1]
  exact ⟨hF.1.2.1 (intrinsicInterior_subset hc), hcG⟩

/-- Intrinsic and ambient interior coincide for a set spanning the ambient
space. This supplies the paper's ambient-interior wording in full dimension. -/
theorem intrinsicInterior_eq_interior_of_full_span {P : Set E}
    (hfull : affineSpan ℝ P = ⊤) : intrinsicInterior ℝ P = interior P := by
  apply Set.Subset.antisymm
  · intro x hx
    have hopen : IsOpen (affineSpan ℝ P : Set E) := by rw [hfull]; exact isOpen_univ
    have hmap := hopen.isOpenMap_subtype_val.image_interior_subset
      ((Subtype.val : affineSpan ℝ P → E) ⁻¹' P)
    have hh := hmap hx
    have heq : (Subtype.val : affineSpan ℝ P → E) ''
        ((Subtype.val : affineSpan ℝ P → E) ⁻¹' P) = P := by
      apply Set.Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        exact hz
      · intro y hy
        exact ⟨⟨y, subset_affineSpan ℝ P hy⟩, hy, rfl⟩
    exact (congrArg (fun S : Set E => x ∈ interior S) heq).mp hh
  · exact interior_subset_intrinsicInterior

/-- The actual centroid in the main theorem is an ambient interior point,
with full dimension and centeredness derived from geometric uniformity. -/
theorem uniform_centroid_mem_interior {n : ℕ} {P : Set (Space (n + 3))}
    (hP : Uniform (n + 3) P) :
    vertexCentroid (vertices P (uniform_finitePolytope hP)) ∈ interior P := by
  rw [← intrinsicInterior_eq_interior_of_full_span (uniform_affineSpan_eq_top hP)]
  exact vertexCentroid_mem_intrinsicInterior (uniform_finitePolytope hP)

end Uniform5.Composition
