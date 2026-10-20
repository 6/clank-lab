import Uniform5.CompositionFirstStage
import Uniform5.CompositionGlobalLabels
import Uniform5.CompositionNormalizedLabels
import Uniform5.CompositionFigureFacetCorrespondence

/-! Every actual facet at a vertex occurs in a surviving cycle. Polygon
existence, coherent labels, and transfer across word classes are proved. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- A facet label occurring in a word occurs in every representative of
its rotation/reversal class. The actual word sides witness the transfer. -/
theorem LibraryCycleWord.facet_occurs_of_class {U V : LibraryCycleWord}
    (h : U.classCode = V.classCode) (i : Fin U.length.val) :
    ∃ j, V.word.facet j = U.word.facet i := by
  let s : LibraryWordSide := ⟨U.polygon.val, U.word.facet i,
    U.word.cell i, U.word.cell (finRotate U.length.val i)⟩
  have hs : s ∈ U.sideSet := (U.mem_sideSet s).mpr
    ⟨rfl, i, rfl, Or.inl ⟨rfl, rfl⟩⟩
  rw [LibraryCycleWord.sideSet_eq_of_class h] at hs
  obtain ⟨_, j, hj, _⟩ := (V.mem_sideSet s).mp hs
  exact ⟨j, hj⟩

/-- Inside any given incident facet, two more actual facet containments
supply an actual polygon through the apex. -/
theorem unitUniform5_facet_vertex_on_polygon {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v : Space 5}
    (hv : v ∈ P.extremePoints ℝ) (hvK : v ∈ K) :
    ∃ G k, PolygonFace P G k ∧ v ∈ G.extremePoints ℝ ∧ G ⊆ K := by
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
    (face_extremePoints_eq hGP).symm ▸ ⟨hvG, hv⟩, hG.1.2.1.trans hC.1.2.1⟩

/-- The global name of each actual incident facet occurs in the filtered
cycle set of any retained class containing the actual parent radius. -/
theorem unitUniform5_globalFacetLabel_occurs
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P K : Set (Space 5)} (hP : UnitUniform 5 P) (hsmall : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hK : Facet P K) (hvK : v ∈ K)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    {j : RetainedRootIndex S}
    (hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    ∃ W ∈ filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j),
      ∃ i, W.word.facet i = globalFacetLabel N K := by
  obtain ⟨G, k, hG, hvG, hGK⟩ := unitUniform5_facet_vertex_on_polygon hP hK hv hvK
  let l : LibraryPolygonSize := ⟨k, (polygonFace_unitPolygon hP hG).1, hsmall G k hG⟩
  have hcoverage := unitUniform5_smallFaces_facet_coverage
    classification3D classification4D hP hsmall N hLIB
  obtain ⟨A⟩ := exists_actualLibraryCycle_local hP (k := l) hG N (fun K hK _ => hcoverage K hK)
  let B := A.globallyLabeled
  obtain ⟨i, hi⟩ := (B.cycle.facet_coverage K).mp ⟨hK, hGK⟩
  have hlabel : B.word.word.facet i = globalFacetLabel N K := by
    change globalFacetLabel N (A.cycle.facet i) = globalFacetLabel N K
    exact congrArg (globalFacetLabel N) hi
  obtain ⟨W, hW, heq⟩ := hS.complete B.word (B.admissible hP hG hLIB)
  have hactual : W ∈ actualListedWords N S P v := ⟨hW, l, G, hG, hvG, B, heq⟩
  have hsurv := actual_listed_words_survive hP hsmall v N S hLIB hS hcoverage hj hactual
  obtain ⟨t, ht⟩ := LibraryCycleWord.facet_occurs_of_class heq i
  exact ⟨W, hsurv, t, ht.trans hlabel⟩

/-- The facet-occurrence clause of stage two after arbitrary actual
intrinsic coordinate normalization, using the shared geometric label map. -/
theorem normalizedFigureFacetLabel_occurs
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hsmall : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q H : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hH : Facet Q H) {j : RetainedRootIndex S}
    (hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    ∃ W ∈ filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j),
      ∃ i, W.word.facet i = normalizedFigureFacetLabel N P v
        (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) f H := by
  have hH' := embedding_facet_image f hH
  rw [him] at hH'
  obtain ⟨K, hK, _, hvK, hKH, _⟩ := unitUniform5_vertexFigure_facet hP hv hH'
  obtain ⟨W, hW, i, hi⟩ := unitUniform5_globalFacetLabel_occurs
    classification3D classification4D hP hsmall hv hK hvK.1 N S hLIB hS hj
  refine ⟨W, hW, i, ?_⟩
  rw [normalizedFigureFacetLabel, ← hKH,
    parentFigureFacetLabel_section (n := 2) hP hv hK.1 hvK.1]
  exact hi

end Uniform5.Composition
