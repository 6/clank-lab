import Uniform5.CompositionCubeProducts

/-! The cube-prism and square-duoprism entries are the B4 cube entry. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [PseudoMetricSpace E] {P : Set E}

theorem b3_cube_named : NamedPolyhedronModel 2 (WythoffHull rootsB3 cubeCorner3) := by
  change B3RingModel {⟨2, by decide⟩} (WythoffHull rootsB3 cubeCorner3)
  exact ⟨cubeCorner3, cubeCorner3_seed, congruent_refl _⟩

theorem facet_b4_cube_iff : FacetLibraryModel (.wythoff 1 0) P ↔
    Congruent P (WythoffHull rootsB4 cubeCorner4) := by
  constructor
  · intro h
    exact facetLibraryModel_unique h cubeCorner4_library_name
  · intro h
    change ∃ x, WythoffSeed rootsB4 (libraryRingSet 0) x ∧ Congruent P (WythoffHull rootsB4 x)
    refine ⟨cubeCorner4, ?_, h⟩
    have hr : libraryRingSet 0 = {⟨3, by decide⟩} := by decide
    rw [hr]
    exact cubeCorner4_seed

theorem facet_cubePrism_iff : FacetLibraryModel (.polyhedronPrism 2) P ↔
    Congruent P (polyhedralPrismModel (WythoffHull rootsB3 cubeCorner3)) := by
  constructor
  · rintro ⟨Q, hQ, hPQ⟩
    exact congruent_trans hPQ
      (congruent_product (namedPolyhedronModel_unique hQ b3_cube_named) (congruent_refl unitInterval))
  · intro h
    exact ⟨_, b3_cube_named, h⟩

/-- Literal alias-table entry pr-cube → B4:0001. -/
theorem cubePrism_b4_alias :
    FacetLibraryModel (.polyhedronPrism 2) P ↔ FacetLibraryModel (.wythoff 1 0) P := by
  rw [facet_cubePrism_iff, facet_b4_cube_iff]
  exact ⟨fun h => congruent_trans h congruent_cubePrism_b4,
    fun h => congruent_trans h (congruent_symm congruent_cubePrism_b4)⟩

/-- Literal alias-table entry duoprism(4,4) → B4:0001. -/
theorem squareDuoprism_b4_alias :
    FacetLibraryModel (.duoprism ⟨(1, 1), by decide⟩) P ↔
      FacetLibraryModel (.wythoff 1 0) P := by
  rw [facet_b4_cube_iff]
  change Congruent P (duoprismModel 4 4) ↔ Congruent P (WythoffHull rootsB4 cubeCorner4)
  exact ⟨fun h => congruent_trans h congruent_squareDuoprism_b4,
    fun h => congruent_trans h (congruent_symm congruent_squareDuoprism_b4)⟩

end Uniform5.Composition
