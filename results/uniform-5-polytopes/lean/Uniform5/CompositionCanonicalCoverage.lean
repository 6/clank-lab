import Uniform5.CompositionFacetAliasReduction
import Uniform5.CompositionFacetCatalogue
import Uniform5.CompositionFacetModelUnique
import Uniform5.CompositionActualFilterSupport

/-! The cited classifications and proved geometric aliases discharge the
canonical facet-coverage premise of the actual LIB/S1/filter chain. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Concrete 214-name coverage, all geometric aliases and same-name model
uniqueness identify an actual small-faced four-polytope with a LIB model. -/
theorem unitUniform4_canonical_library_match
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set E} (hP : UnitUniform 4 P) (hs : SmallFaces P)
    (N : LibraryNumericalData) (hLIB : LIB N) :
    ∃ n : CanonicalFacetName, Congruent P (N.model n) := by
  obtain ⟨Q, n, _, _, hn, hPQ⟩ := unitUniform4_smallFaces_intrinsic_catalogue
    classification3D classification4D hP hs
  let c := canonicalFacetIndex n
  have hc : FacetLibraryModel c.val Q := (canonicalFacetIndex_model_iff n Q).mp hn
  exact ⟨c, congruent_trans hPQ (facetLibraryModel_unique hc (hLIB.model_named c))⟩

theorem unitUniform5_smallFaces_facet_coverage
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    (N : LibraryNumericalData) (hLIB : LIB N) :
    ∀ K, Facet P K → ∃ n, Congruent K (N.model n) := by
  intro K hK
  have hUK : UnitUniform 4 K := ⟨uniform_facets hP.1 hK,
    unitEdges_face (uniform_finitePolytope hP.1) hK.1 hP.2⟩
  exact unitUniform4_canonical_library_match classification3D classification4D
    hUK (smallFaces_face hs hK.1) N hLIB

/-- The local Omega corollary now uses only named inputs and actual local
small-face facts; it has no unproved library-coverage premise. -/
theorem unitUniform5_local_smallFacets_radius_mem_omega
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) (hk : k ≤ 16)
    (hlocal : ∀ K, Facet P K → G ⊆ K → SmallFaces K)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S) :
    intrinsicRadius P ∈ stageOneOmega S := by
  apply unitUniform5_local_radius_mem_omega hP hG hk N S hLIB hS
  intro K hK hGK
  have hUK : UnitUniform 4 K := ⟨uniform_facets hP.1 hK,
    unitEdges_face (uniform_finitePolytope hP.1) hK.1 hP.2⟩
  exact unitUniform4_canonical_library_match classification3D classification4D
    hUK (hlocal K hK hGK) N hLIB

/-- Case A's actual radius belongs to Omega using only the cited facts,
LIB and S1; no model coverage or alias premise remains. -/
theorem unitUniform5_smallFaces_radius_mem_omega
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {k : ℕ} (hG : PolygonFace P G k)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S) :
    intrinsicRadius P ∈ stageOneOmega S :=
  unitUniform5_radius_mem_omega hP hG (hs G k hG) N S hLIB hS
    (unitUniform5_smallFaces_facet_coverage classification3D classification4D hP hs N hLIB)

/-- The full geometric conclusion of the closure-filter lemma: one actual
radius class survives and contains all the listed actual words at the vertex.
FILTER's counts are not needed to prove this geometric implication. -/
theorem unitUniform5_smallFaces_surviving_class
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {k : ℕ} (hG : PolygonFace P G k) {v : Space 5} (hvG : v ∈ G.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S) :
    ∃ j : RetainedRootIndex S,
      intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j) ∧
      (retainedRootGraph S).connectedComponentMk j ∈ survivingRootClasses N S ∧
      actualListedWords N S P v ⊆
        (filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j) : Set LibraryCycleWord) := by
  have hcoverage := unitUniform5_smallFaces_facet_coverage
    classification3D classification4D hP hs N hLIB
  let l : LibraryPolygonSize := ⟨k, (polygonFace_unitPolygon hP hG).1, hs G k hG⟩
  obtain ⟨_, j, hj, hsurv, _⟩ := unitUniform5_polygon_filter_witness
    hP hs (k := l) hG hvG N S hLIB hS hcoverage
  exact ⟨j, hj, hsurv, actual_listed_words_survive hP hs v N S hLIB hS hcoverage hj⟩

end Uniform5.Composition
