import Uniform5.CompositionCenteredEdgeCycle
import Uniform5.CompositionGlobalLabels
import Uniform5.CompositionSignatures

/-! One geometric cycle word for each actual edge of a normalized figure.
The selected data retains its parent polygon and globally shared face labels.
Closure of the resulting signature is proved before any S2 coverage input. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- A word witness refers to the actual parent polygon and actual cyclic
faces, with its side count tied to the length of this particular edge. -/
structure ActualNormalizedEdgeData (N : LibraryNumericalData)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (v : Space 5)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q e : Set (Space 4)) where
  size : LibraryPolygonSize
  polygon : Set (Space 5)
  polygon_face : PolygonFace P polygon size.val
  apex : v ∈ polygon.extremePoints ℝ
  image_edge : f '' e = polygon ∩ vertexFigure P v
    (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  cycle : ActualLibraryCycle N P polygon size
  cell_labels : ∀ i, cycle.labels.cellLabel i = globalCellLabel (cycle.cycle.cell i)
  facet_labels : ∀ i, cycle.labels.facetLabel i = globalFacetLabel N (cycle.cycle.facet i)
  chord : ∃ x y, Edge Q x y ∧ e = segment ℝ x y ∧
    dist x y = 2 * Real.cos (Real.pi / size.val)

theorem exists_actualNormalizedEdgeData
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hsmall : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (hLIB : LIB N)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q e : Set (Space 4)} (hQ : FinitePolytope Q)
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (he : IsConvexFace Q e) (hne : e.Nonempty) (hd : affineDimension e = 1) :
    Nonempty (ActualNormalizedEdgeData N hP v f Q e) := by
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  have heF : IsConvexFace (vertexFigure P v c) (f '' e) :=
    him ▸ embedding_face_image f he
  obtain ⟨G, ⟨hG, hvG, hdG, hGe⟩, _⟩ :=
    (unitUniform_vertexFigure_face_correspondence (n := 2) hP hv 1).2 (f '' e) heF
      (hne.image f) (by rwa [affineDimension_affineIsometry_image])
  let hGP := finitePolytope_face (uniform_finitePolytope hP.1) hG ⟨v, hvG⟩
  let m := (vertices G hGP).card
  have hpoly : PolygonFace P G m := ⟨hG, hdG, vertices G hGP, coe_vertices G hGP, rfl⟩
  let k : LibraryPolygonSize := ⟨m, (polygonFace_unitPolygon hP hpoly).1,
    hsmall G m hpoly⟩
  have hvG' : v ∈ G.extremePoints ℝ := by
    rw [face_extremePoints_eq hG]
    exact ⟨hvG, hv⟩
  obtain ⟨A⟩ := exists_actualLibraryCycle_local hP (k := k) hpoly N
    (fun K hK _ => unitUniform5_smallFaces_facet_coverage
      classification3D classification4D hP hsmall N hLIB K hK)
  obtain ⟨x, y, hxy, heseg⟩ := finitePolytope_oneFace_edge hQ he hne hd
  have hxyF : Edge (vertexFigure P v c) (f x) (f y) :=
    him ▸ embedding_edge_image f hxy
  have hxG : f x ∈ G := (hGe.symm ▸ mem_image_of_mem f
    (heseg.symm ▸ left_mem_segment ℝ x y)).1
  have hyG : f y ∈ G := (hGe.symm ▸ mem_image_of_mem f
    (heseg.symm ▸ right_mem_segment ℝ x y)).1
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  have hext := finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv c R hs hP.2
  have hvx : Edge P v (f x) := by have hh := hxyF.1; rwa [hext] at hh
  have hvy : Edge P v (f y) := by have hh := hxyF.2.1; rwa [hext] at hh
  have hchord := polygonFace_neighbor_chord (n := 2) hP hpoly
    ((edge_face_iff (uniform_finitePolytope hP.1) hG hvG hxG).mp hvx)
    ((edge_face_iff (uniform_finitePolytope hP.1) hG hvG hyG).mp hvy) hxyF.2.2.1
  rw [f.isometry.dist_eq] at hchord
  exact ⟨{
    size := k
    polygon := G
    polygon_face := hpoly
    apex := hvG'
    image_edge := hGe.symm
    cycle := A.globallyLabeled
    cell_labels := fun _ => rfl
    facet_labels := fun _ => rfl
    chord := ⟨x, y, hxy, heseg, hchord⟩ }⟩

/-- An arbitrary total-function value, used only outside geometric edges
for which an actual word witness exists. -/
noncomputable def unusedEdgeWord : LibraryCycleClass :=
  (LibraryCycleWord.mk ⟨3, by decide⟩ ⟨3, by decide⟩
    ⟨fun _ => canonicalFacetIndex (.wythoff 0 0), fun _ => cellType ∅⟩).classCode

/-- A single word assignment on all subsets. Every actual edge is proved
below to take the witnessed branch, which preserves its original polygon. -/
noncomputable def actualNormalizedEdgeWord (N : LibraryNumericalData)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (v : Space 5)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q : Set (Space 4)) (e : Set (Space 4)) : LibraryCycleClass :=
  if h : Nonempty (ActualNormalizedEdgeData N hP v f Q e)
  then (Classical.choice h).cycle.word.classCode else unusedEdgeWord

theorem actualNormalizedEdgeWord_witness
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hsmall : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (hLIB : LIB N)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q e : Set (Space 4)} (hQ : FinitePolytope Q)
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (he : e ∈ facesOfDimension Q hQ 1) :
    ∃ D : ActualNormalizedEdgeData N hP v f Q e,
      actualNormalizedEdgeWord N hP v f Q e = D.cycle.word.classCode := by
  obtain ⟨he, hne, hd⟩ := (mem_facesOfDimension hQ 1).mp he
  have hh := exists_actualNormalizedEdgeData classification3D classification4D
    hP hsmall hv N hLIB f hQ him he hne hd
  exact ⟨Classical.choice hh, by rw [actualNormalizedEdgeWord, dif_pos hh]⟩

namespace ActualNormalizedEdgeData
variable {N : LibraryNumericalData} {P : Set (Space 5)} {hP : UnitUniform 5 P}
  {v : Space 5} {f : Space 4 →ᵃⁱ[ℝ] Space 5} {Q e : Set (Space 4)}
  (D : ActualNormalizedEdgeData N hP v f Q e)

/-- The selected word's original incidence cycle in the supplied normalized
coordinates; no fresh choice of cyclic order or face labels is made. -/
noncomputable def incidenceCycle
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) :
    ActualEdgeIncidenceCycle Q e D.cycle.cycle.length :=
  ((D.cycle.cycle.figureEdgeCycle hP D.polygon_face D.apex).pullbackOfImage f him).castEdge
    (by rw [← D.image_edge, Set.preimage_image_eq _ f.injective])

theorem incidenceCycle_ridge_image
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) (i : ℕ) :
    f '' (D.incidenceCycle him).ridge i = D.cycle.cycle.cell i ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  unfold incidenceCycle
  rw [ActualEdgeIncidenceCycle.castEdge_ridge, ActualEdgeIncidenceCycle.pullbackOfImage_ridge]
  let A := D.cycle.cycle.figureEdgeCycle hP D.polygon_face D.apex
  have hh : IsConvexFace (f '' Q) (A.ridge i) := him.symm ▸ A.ridge_face i
  rw [embedding_face_image_preimage f hh]
  rfl

theorem incidenceCycle_facet_image
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) (i : Fin D.cycle.cycle.length) :
    f '' (D.incidenceCycle him).facet i = D.cycle.cycle.facet i ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  unfold incidenceCycle
  rw [ActualEdgeIncidenceCycle.castEdge_facet, ActualEdgeIncidenceCycle.pullbackOfImage_facet]
  let A := D.cycle.cycle.figureEdgeCycle hP D.polygon_face D.apex
  have hh : IsConvexFace (f '' Q) (A.facet i) := him.symm ▸ (A.facet_incidence i).1.1
  rw [embedding_face_image_preimage f hh]
  rfl

theorem closure : D.cycle.word.classCode.closure N (1 / intrinsicRadius P) = 0 :=
  (D.cycle.rootFacts hP).root

/-- Every selected edge word belongs to the same surviving filtered class
whenever that class contains the actual parent radius. -/
theorem filtered (hsmall : SmallFaces P)
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    {j : RetainedRootIndex S}
    (hj : intrinsicRadius P ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    ∃ W ∈ filteredClassCycles N S ((retainedRootGraph S).connectedComponentMk j),
      D.cycle.word.classCode = W.classCode := by
  obtain ⟨W, hW, heq⟩ := hS.complete D.cycle.word (D.cycle.admissible hP D.polygon_face hLIB)
  have ha : W ∈ actualListedWords N S P v :=
    ⟨hW, D.size, D.polygon, D.polygon_face, D.apex, D.cycle, heq⟩
  exact ⟨W, actual_listed_words_survive hP hsmall v N S hLIB hS
    (unitUniform5_smallFaces_facet_coverage classification3D classification4D hP hsmall N hLIB)
    hj ha, heq⟩

end ActualNormalizedEdgeData

/-- Every actual edge word in the multiset has its actual closure root;
therefore the entire actual signature is radius-compatible without S2. -/
theorem actualNormalizedFigureSignature_radiusCompatible
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hsmall : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (hLIB : LIB N)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q : Set (Space 4)} (hQ : FinitePolytope Q)
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (facetLabel : Set (Space 4) → CanonicalFacetName) :
    (geometricFigureSignature Q hQ facetLabel (actualNormalizedEdgeWord N hP v f Q)).RadiusCompatible
      N (intrinsicRadius P) := by
  intro W hW
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hW
  have he' : e ∈ facesOfDimension Q hQ 1 := he
  obtain ⟨D, hD⟩ := actualNormalizedEdgeWord_witness classification3D classification4D
    hP hsmall hv N hLIB f hQ him he'
  rw [hD]
  exact D.closure

end Uniform5.Composition
