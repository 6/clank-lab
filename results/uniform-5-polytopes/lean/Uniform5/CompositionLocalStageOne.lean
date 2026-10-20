import Uniform5.CompositionRootRegions

/-! The local form of the Omega corollary needed when larger polygons occur
elsewhere in the polytope. Only facets around the chosen polygon are used. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- One actual cycle with genuine model matches and its proved geometry.
Retaining the labels makes later incidence arguments refer to the same word. -/
structure ActualLibraryCycle (N : LibraryNumericalData) (P G : Set (Space 5))
    (k : LibraryPolygonSize) where
  cycle : ActualPolygonCycle P G
  labels : CycleModelLabels cycle CellType CanonicalFacetName
  geometry : cycle.Stage1Geometry k.val
  cells : labels.cellModel = cellTypeModel
  facets : labels.facetModel = N.model
  closed : labels.cellLabel cycle.length = labels.cellLabel 0

namespace ActualLibraryCycle
variable {N : LibraryNumericalData} {P G : Set (Space 5)} {k : LibraryPolygonSize}
  (A : ActualLibraryCycle N P G k)

noncomputable def word : LibraryCycleWord :=
  ⟨k, ⟨A.cycle.length, A.cycle.length_ge⟩, A.labels.cyclicWord⟩

theorem admissible (hP : UnitUniform 5 P) (hG : PolygonFace P G k.val)
    (hLIB : LIB N) : A.word.Admissible N := by
  constructor
  · simpa only [word, LibraryCycleWord.Admissible, A.cells, A.facets] using
      A.labels.cyclicWord_valid A.closed hP hG
  · change (∑ i : Fin A.cycle.length,
      (N.angleBall (A.labels.cyclicWord.facet i) k.val (A.labels.cyclicWord.cell i)
        (A.labels.cyclicWord.cell (finRotate A.cycle.length i))).lower) ≤ _
    rw [A.labels.finite_lowerAngleSum_eq A.closed]
    exact (A.labels.certifiedLowerAngle_sum_lt N hLIB A.cells A.facets hP hG A.geometry).le

theorem rootFacts (hP : UnitUniform 5 P) :
    A.word.ActualRootFacts N (intrinsicRadius P) := by
  have hr := A.labels.finite_radius_domain hP
  rw [A.facets] at hr
  refine ⟨A.geometry.parent_positive, hr.1, hr.2.1, hr.2.2.2, ?_, ?_, ?_⟩
  · change A.labels.cyclicWord.angleSum k.val (intrinsicRadius ∘ N.model)
      (intrinsicRadius ∘ cellTypeModel) < _
    rw [← A.cells, ← A.facets, A.labels.finite_angleSum_eq A.closed, A.labels.angle_eq]
    exact A.geometry.perimeter
  · simpa only [word, LibraryCycleWord.Domain, CyclicWord.domain, finiteClosureDomain,
      A.cells, A.facets] using A.labels.finite_domain A.closed A.geometry
  · simpa only [word, LibraryCycleWord.closure, A.cells, A.facets] using
      A.labels.cyclicWord_actual_root A.closed A.geometry

include A in
theorem radius_mem_omega (hP : UnitUniform 5 P) (hG : PolygonFace P G k.val)
    (hLIB : LIB N) {S : StageOneNumericalData} (hS : S1 N S) :
    intrinsicRadius P ∈ stageOneOmega S :=
  hS.actual_radius_mem_omega (A.admissible hP hG hLIB) (A.rootFacts hP)

end ActualLibraryCycle

/-- No facet disjoint from the chosen polygon needs a library name. -/
theorem exists_actualLibraryCycle_local {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {k : LibraryPolygonSize} (hG : PolygonFace P G k.val) (N : LibraryNumericalData)
    (hcoverage : ∀ K, Facet P K → G ⊆ K → ∃ n, Congruent K (N.model n)) :
    Nonempty (ActualLibraryCycle N P G k) := by
  obtain ⟨D, hD⟩ := unitUniform5_stage1_geometry hP hG
  obtain ⟨L, hC, hF, hclosed⟩ := actual_cycle_exists_type_labels D hP hG N.model
    (fun i => hcoverage (D.facet i) (D.facet_incidence i).1 (D.facet_incidence i).2.1)
  exact ⟨⟨D, L, hD, hC, hF, hclosed⟩⟩

/-- Corollary Omega with the paper's local facet assumption, including
polytopes with polygons larger than sixteen elsewhere. -/
theorem unitUniform5_local_radius_mem_omega {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {k : ℕ} (hG : PolygonFace P G k) (hk : k ≤ 16)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    (hcoverage : ∀ K, Facet P K → G ⊆ K → ∃ n, Congruent K (N.model n)) :
    intrinsicRadius P ∈ stageOneOmega S := by
  have hk3 : 3 ≤ k := (polygonFace_unitPolygon hP hG).1
  obtain ⟨A⟩ := exists_actualLibraryCycle_local hP (k := ⟨k, hk3, hk⟩) hG N hcoverage
  exact A.radius_mem_omega hP hG hLIB hS

end Uniform5.Composition
