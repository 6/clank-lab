import Uniform5.CompositionCanonicalCoverage

/-! A complete actual-polytope composition through the first-stage filter.
No catalogue, polygon-existence, closure or support premise remains. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A proper singleton vertex lies in an actual facet. -/
theorem uniform_vertex_in_facet {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) : ∃ K, Facet P K ∧ v ∈ K := by
  have hproper : ({v} : Set E) ≠ P := by
    intro he
    have hd := uniform_dimension hP
    rw [← he, affineDimension_singleton] at hd
    omega
  obtain ⟨K, hK, hvK⟩ := finitePolytope_face_subset_facet (uniform_finitePolytope hP)
    ((singleton_face_iff_extremePoint P v).mpr hv) (singleton_nonempty v) hproper
  exact ⟨K, hK, hvK (mem_singleton v)⟩

/-- Every actual vertex of a uniform five-polytope is on an actual polygon.
The face is built through three actual facet containments. -/
theorem unitUniform5_vertex_on_polygon {P : Set E} (hP : UnitUniform 5 P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) :
    ∃ G k, PolygonFace P G k ∧ v ∈ G.extremePoints ℝ := by
  obtain ⟨K, hK, hvK⟩ := uniform_vertex_in_facet hP.1 hv
  have huK : Uniform 4 K := uniform_facets hP.1 hK
  have hvK' : v ∈ K.extremePoints ℝ := (face_extremePoints_eq hK.1).symm ▸ ⟨hvK, hv⟩
  obtain ⟨C, hC, hvC⟩ := uniform_vertex_in_facet huK hvK'
  have huC : Uniform 3 C := uniform_facets huK hC
  have hvC' : v ∈ C.extremePoints ℝ := (face_extremePoints_eq hC.1).symm ▸ ⟨hvC, hvK'⟩
  obtain ⟨G, hG, hvG⟩ := uniform_vertex_in_facet huC hvC'
  have hGP : IsConvexFace P G := ⟨hG.1.1, hK.1.2.trans (hC.1.2.trans hG.1.2)⟩
  have hd : affineDimension G = 2 := by
    have hh := hG.2.2
    rw [uniform_dimension huC] at hh
    omega
  let hpoly := finitePolytope_facet (uniform_finitePolytope huC) hG
  exact ⟨G, (vertices G hpoly).card, ⟨hGP, hd, vertices G hpoly, coe_vertices G hpoly, rfl⟩,
    (face_extremePoints_eq hGP).symm ▸ ⟨hvG, hv⟩⟩

/-- The complete first-stage composition for each actual vertex. Its only
nongeometric hypotheses are the precisely named LIB, S1 and cited facts. -/
theorem unitUniform5_smallFaces_first_stage
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    intrinsicRadius P ∈ stageOneOmega S ∧
      ∃ j : RetainedRootIndex S,
        intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j) ∧
        (retainedRootGraph S).connectedComponentMk j ∈ survivingRootClasses N S ∧
        actualListedWords N S P v ⊆
          (filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j) : Set LibraryCycleWord) := by
  obtain ⟨G, k, hG, hvG⟩ := unitUniform5_vertex_on_polygon hP hv
  exact ⟨unitUniform5_smallFaces_radius_mem_omega classification3D classification4D
    hP hs hG N S hLIB hS,
    unitUniform5_smallFaces_surviving_class classification3D classification4D
      hP hs hG hvG N S hLIB hS⟩

/-- FILTER places every actual Case A radius among exactly 563 surviving
classes. This is a first-stage theorem, not the main classification. -/
theorem unitUniform5_smallFaces_surviving_count
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS : S1 N S) (hFILTER : FILTER N S) :
    (survivingRootClasses N S).card = 563 ∧ intrinsicRadius P ∈ stageOneOmega S ∧
      ∃ j : RetainedRootIndex S,
        intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j) ∧
        (retainedRootGraph S).connectedComponentMk j ∈ survivingRootClasses N S := by
  obtain ⟨v, hv⟩ := finitePolytope_extremePoints_nonempty (uniform_finitePolytope hP.1)
  obtain ⟨hOmega, j, hj, hsurv, _⟩ := unitUniform5_smallFaces_first_stage
    classification3D classification4D hP hs N S hLIB hS hv
  exact ⟨hFILTER.surviving, hOmega, j, hj, hsurv⟩

end Uniform5.Composition
