import Uniform5.CompositionActualLibrarySide
import Uniform5.CompositionFilterClasses

/-! Actual semantic cycle words at a vertex form an internally supported
set. This supplies the geometric premise of the finite closure invariant. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def actualListedWords (N : LibraryNumericalData) (S : StageOneNumericalData)
    (P : Set (Space 5)) (v : Space 5) : Set LibraryCycleWord :=
  {W | W ∈ S.listed ∧ ∃ (k : LibraryPolygonSize) (G : Set (Space 5)),
    PolygonFace P G k.val ∧ v ∈ G.extremePoints ℝ ∧
    ∃ A : ActualLibraryCycle N P G k, A.word.classCode = W.classCode}

theorem actual_listed_words_supported {P : Set (Space 5)} (hP : UnitUniform 5 P)
    (hsmall : SmallFaces P) (v : Space 5) (N : LibraryNumericalData)
    (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    (hcoverage : ∀ K, Facet P K → ∃ n, Congruent K (N.model n)) :
    (libraryFilterIncidence N).Supported (actualListedWords N S P v) := by
  rintro W ⟨hW, k, G, hG, hvG, A, hcode⟩ s hs r hr
  have hsA : s ∈ A.word.sideSet := by
    rw [LibraryCycleWord.sideSet_eq_of_class hcode]
    exact hs
  obtain ⟨_, i, hfi, _⟩ := (A.word.mem_sideSet s).mp hsA
  change A.labels.facetLabel i = s.facet at hfi
  have hKi := (A.cycle.facet_incidence i).1
  have hK := A.cycle.facet_unitUniform hP i
  have hKM := A.labels.facet_matches i
  rw [A.facets, hfi] at hKM
  have hvK : v ∈ (A.cycle.facet i).extremePoints ℝ := by
    rw [face_extremePoints_eq hKi.1]
    exact ⟨(A.cycle.facet_incidence i).2.1 (extremePoints_subset hvG),
      (face_extremePoints_eq hG.1 ▸ hvG).2⟩
  obtain ⟨H, C, D, hH, hC, hD, hHC, hHD, hCD, hCA, hDB, hvH⟩ :=
    modelPolygonWord_at_vertex hK hKM hr.2 hvK
  have hHP : PolygonFace P H r.polygon := polygonFace_trans hKi.1 hH
  let l : LibraryPolygonSize := ⟨r.polygon, (polygonFace_unitPolygon hP hHP).1,
    hsmall H r.polygon hHP⟩
  obtain ⟨B⟩ := exists_actualLibraryCycle_local hP (k := l) hHP N
    (fun K hK _ => hcoverage K hK)
  obtain ⟨j, hj⟩ := (B.cycle.facet_coverage (A.cycle.facet i)).mp ⟨hKi, hH.1.2.1⟩
  have hBM : Congruent (B.cycle.facet j) (N.model s.facet) := hj ▸ hKM
  let B' := B.relabelFacet j s.facet hBM
  have hlabel : B'.labels.facetLabel j = r.facet :=
    (B.relabelFacet_label j s.facet hBM).trans hr.1.symm
  have hside : r ∈ B'.word.sideSet := by
    apply B'.side_of_actual hP hHP j r rfl hlabel
      (C := C) (D := D)
    · exact hj ▸ hC
    · exact hj ▸ hD
    · exact hHC
    · exact hHD
    · exact hCD
    · exact hCA
    · exact hDB
  obtain ⟨V, hV, heq⟩ := hS.complete B'.word (B'.admissible hP hHP hLIB)
  refine ⟨V, ⟨hV, l, H, hHP, hvH, B', heq⟩, ?_⟩
  change r ∈ V.sideSet
  rwa [← LibraryCycleWord.sideSet_eq_of_class heq]

/-- All the actual listed words lie in any class carrying their common
actual radius. Distinct listed class representatives identify the witness. -/
theorem actual_listed_words_in_class {P : Set (Space 5)} (hP : UnitUniform 5 P)
    (v : Space 5) (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS : S1 N S) {j : RetainedRootIndex S}
    (hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    actualListedWords N S P v ⊆
      (rootClassCycles S ((retainedRootGraph S).connectedComponentMk j) : Set LibraryCycleWord) := by
  rintro W ⟨hW, k, G, hG, _, A, hcode⟩
  obtain ⟨V, hV, heq⟩ := hS.actual_word_in_class
    (A.admissible hP hG hLIB) (A.rootFacts hP) hj
  have hWV : W = V := hS.distinct_classes W hW V
    (rootClassCycles_subset_listed S _ hV) (hcode.symm.trans heq)
  exact hWV ▸ hV

/-- The semantic version of the paper's geometric closure-filter lemma.
FILTER's numerical counts play no role in proving actual survival. -/
theorem actual_listed_words_survive {P : Set (Space 5)} (hP : UnitUniform 5 P)
    (hsmall : SmallFaces P) (v : Space 5) (N : LibraryNumericalData)
    (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    (hcoverage : ∀ K, Facet P K → ∃ n, Congruent K (N.model n))
    {j : RetainedRootIndex S}
    (hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    actualListedWords N S P v ⊆
      (filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j) : Set LibraryCycleWord) :=
  supported_words_survive N S _
    (actual_listed_words_supported hP hsmall v N S hLIB hS hcoverage)
    (actual_listed_words_in_class hP v N S hLIB hS hj)


/-- Every actual polygon at the vertex supplies a retained root occurrence
and a word surviving in its radius class. All other actual polygons use
this same class by actual_listed_words_survive. -/
theorem unitUniform5_polygon_filter_witness {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) (hsmall : SmallFaces P) {k : LibraryPolygonSize}
    (hG : PolygonFace P G k.val) {v : Space 5} (hvG : v ∈ G.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    (hcoverage : ∀ K, Facet P K → ∃ n, Congruent K (N.model n)) :
    ∃ A : ActualLibraryCycle N P G k, ∃ j : RetainedRootIndex S,
      intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j) ∧
      (retainedRootGraph S).connectedComponentMk j ∈ survivingRootClasses N S ∧
      ∃ V ∈ filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j),
        A.word.classCode = V.classCode := by
  classical
  obtain ⟨A⟩ := exists_actualLibraryCycle_local hP hG N (fun K hK _ => hcoverage K hK)
  have hA := A.admissible hP hG hLIB
  have hR := A.rootFacts hP
  obtain ⟨V, hV, i, heq, hflat, hdeg, hi⟩ := hS.actual_root_witness hA hR
  let j : RetainedRootIndex S := ⟨⟨⟨V, hV⟩, i⟩, hflat, hdeg⟩
  have hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j) :=
    ⟨hR.radius_pos, hi⟩
  have hactual : V ∈ actualListedWords N S P v := ⟨hV, k, G, hG, hvG, A, heq⟩
  have hsurv := actual_listed_words_survive hP hsmall v N S hLIB hS hcoverage hj hactual
  refine ⟨A, j, hj, ?_, V, hsurv, heq⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, V, hsurv⟩
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, intrinsicRadius P, hj⟩⟩

end Uniform5.Composition
