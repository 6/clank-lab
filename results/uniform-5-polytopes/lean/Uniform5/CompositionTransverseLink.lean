import Uniform5.CompositionTransverseFace
import Uniform5.CompositionFacetSystemGeneral
import Uniform5.CompositionRidgeIncidence
import Uniform5.CompositionFigureRidgeCorrespondence

/-!
# Actual planar transverse links

A positive-height cut at the actual transverse vertex gives the link.
The two geometric face-poset correspondences compose, with their rank shifts.
-/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

noncomputable local instance (G : Set E) : DecidableEq (affineSpan ℝ G).directionᗮ := Classical.decEq _

/-- The finite-polytope version of the actual apex section face isomorphism. -/
noncomputable def finitePolytope_heightSectionFaceEquiv {Q : Set E}
    (hQ : FinitePolytope Q) (hz : (0 : E) ∈ Q.extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hh : ∀ x ∈ (vertices Q hQ).erase 0, 1 ≤ L x) :
    {F : GeometricFace Q // (0 : E) ∈ F.val} ≃o GeometricFace (heightSection Q L) :=
  ((facesAtCongr (convexHull_vertices hQ).symm rfl).trans
    (apexFaceSectionEquiv (vertices Q hQ) ((mem_vertices hQ 0).mpr hz) L hh)).trans
    (geometricFace_congr (congrArg (fun P => heightSection P L) (convexHull_vertices hQ)))

omit [FiniteDimensional ℝ E] in
@[simp] theorem finitePolytope_heightSectionFaceEquiv_apply {Q : Set E}
    (hQ : FinitePolytope Q) (hz : (0 : E) ∈ Q.extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hh : ∀ x ∈ (vertices Q hQ).erase 0, 1 ≤ L x)
    (F : {F : GeometricFace Q // (0 : E) ∈ F.val}) :
    (finitePolytope_heightSectionFaceEquiv hQ hz L hh F).val = F.val.val ∩ heightSection Q L := by
  change F.val.val ∩ heightSection (convexHull ℝ (vertices Q hQ : Set E)) L = _
  rw [convexHull_vertices]

/-- A nontrivial finite-polytope apex section has its actual finite hull
and loses exactly one intrinsic dimension. -/
theorem finitePolytope_heightSection_finite_dimension {Q : Set E}
    (hQ : FinitePolytope Q) (hz : (0 : E) ∈ Q.extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hh : ∀ x ∈ (vertices Q hQ).erase 0, 1 ≤ L x)
    (hd : 0 < affineDimension Q) :
    FinitePolytope (heightSection Q L) ∧ affineDimension (heightSection Q L) + 1 = affineDimension Q := by
  have hh' := finiteHull_heightSection_finite_dimension (vertices Q hQ)
    ((mem_vertices hQ 0).mpr hz) L hh (by simpa only [convexHull_vertices] using hd)
  simpa only [convexHull_vertices] using hh'

/-- The section rank shift applies to each actual nontrivial apex face. -/
theorem finitePolytope_heightSectionFaceEquiv_dimension {Q : Set E}
    (hQ : FinitePolytope Q) (hz : (0 : E) ∈ Q.extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hh : ∀ x ∈ (vertices Q hQ).erase 0, 1 ≤ L x)
    (F : {F : GeometricFace Q // (0 : E) ∈ F.val}) (hne : F.val.val ≠ {0}) :
    affineDimension (finitePolytope_heightSectionFaceEquiv hQ hz L hh F).val + 1 =
      affineDimension F.val.val := by
  have hF : IsConvexFace (convexHull ℝ (vertices Q hQ : Set E)) F.val.val :=
    (convexHull_vertices hQ).symm ▸ F.val.property
  have hd := apexFace_section_dimension (vertices Q hQ)
    ((mem_vertices hQ 0).mpr hz) L hh hF F.property hne
  simpa only [convexHull_vertices, finitePolytope_heightSectionFaceEquiv_apply] using hd

/-- The positive cutting functional is chosen from a proved separating
functional at the actual transverse vertex. -/
noncomputable def transverseCutHeight {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) :
    (affineSpan ℝ G).directionᗮ →L[ℝ] ℝ :=
  (finitePolytope_zero_vertex_height (finitePolytope_transverse hP G c)
    (transverse_origin_extreme hP hG hc)).choose

theorem transverseCutHeight_ge_one {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) :
    ∀ x ∈ (vertices (transverseProjection G c '' P) (finitePolytope_transverse hP G c)).erase 0,
      1 ≤ transverseCutHeight hP hG hc x :=
  (finitePolytope_zero_vertex_height (finitePolytope_transverse hP G c)
    (transverse_origin_extreme hP hG hc)).choose_spec

/-- The actual height-one planar link of a polygon face. -/
noncomputable def transverseLink {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) : Set (affineSpan ℝ G).directionᗮ :=
  heightSection (transverseProjection G c '' P) (transverseCutHeight hP hG hc)

/-- Actual faces above the collapsed face correspond to all actual link
faces, including the empty link face corresponding to the collapsed face. -/
noncomputable def transverseLinkFaceEquiv {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) :
    {F : GeometricFace P // G ⊆ F.val} ≃o GeometricFace (transverseLink hP hG hc) :=
  (transverseFaceEquiv hP hG hc).trans
    (finitePolytope_heightSectionFaceEquiv (finitePolytope_transverse hP G c)
      (transverse_origin_extreme hP hG hc) (transverseCutHeight hP hG hc)
      (transverseCutHeight_ge_one hP hG hc))

@[simp] theorem transverseLinkFaceEquiv_apply {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (F : {F : GeometricFace P // G ⊆ F.val}) :
    (transverseLinkFaceEquiv hP hG hc F).val =
      (transverseProjection G c '' F.val.val) ∩ transverseLink hP hG hc := by
  change (finitePolytope_heightSectionFaceEquiv (finitePolytope_transverse hP G c)
    (transverse_origin_extreme hP hG hc) (transverseCutHeight hP hG hc)
    (transverseCutHeight_ge_one hP hG hc) (transverseFaceEquiv hP hG hc F)).val = _
  rw [finitePolytope_heightSectionFaceEquiv_apply, transverseFaceEquiv_apply]
  rfl

/-- No larger parent face collapses to the transverse origin. -/
theorem transverse_face_image_ne_zero {P G F : Set E} (hG : IsConvexFace P G)
    (hF : IsConvexFace P F) (hGF : G ⊆ F) {c : E} (hc : c ∈ G) (hne : F ≠ G) :
    transverseProjection G c '' F ≠ {0} := by
  intro heq
  have hh := transverse_face_saturated hF hGF hc
  rw [heq, transverseProjection_zero_fiber hG hc] at hh
  exact hne hh.symm

/-- The two geometric rank shifts add: projection removes the polygon's
two directions, and taking the link removes the radial direction. -/
theorem transverseLinkFaceEquiv_dimension {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (F : {F : GeometricFace P // G ⊆ F.val}) (hne : F.val.val ≠ G) :
    affineDimension (transverseLinkFaceEquiv hP hG hc F).val + affineDimension G + 1 =
      affineDimension F.val.val := by
  have hd := finitePolytope_heightSectionFaceEquiv_dimension
    (finitePolytope_transverse hP G c) (transverse_origin_extreme hP hG hc)
    (transverseCutHeight hP hG hc) (transverseCutHeight_ge_one hP hG hc)
    (transverseFaceEquiv hP hG hc F)
    (transverse_face_image_ne_zero hG F.val.property F.property hc hne)
  have ht := transverseFaceEquiv_dimension hP hG hc F
  change affineDimension (transverseLinkFaceEquiv hP hG hc F).val + 1 = _ at hd
  omega

/-- Each strictly larger incident parent face gives a nonempty link face. -/
theorem transverseLinkFaceEquiv_nonempty {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (F : {F : GeometricFace P // G ⊆ F.val}) (hne : F.val.val ≠ G) :
    (transverseLinkFaceEquiv hP hG hc F).val.Nonempty := by
  let Q := transverseProjection G c '' P
  let hQ := finitePolytope_transverse hP G c
  let V := vertices Q hQ
  have hface : IsConvexFace (convexHull ℝ (V : Set (affineSpan ℝ G).directionᗮ))
      (transverseProjection G c '' F.val.val) := by
    rw [convexHull_vertices]
    exact transverse_face_image hP F.val.property F.property hc
  have hz : (0 : (affineSpan ℝ G).directionᗮ) ∈ transverseProjection G c '' F.val.val :=
    ⟨c, F.property hc, transverseProjection_center G c⟩
  have hh := (apexFace_section_nonempty_iff V (transverseCutHeight hP hG hc)
    (transverseCutHeight_ge_one hP hG hc) hface hz).mpr
    (transverse_face_image_ne_zero hG F.val.property F.property hc hne)
  rw [transverseLinkFaceEquiv_apply]
  simpa only [V, Q, hQ, convexHull_vertices, transverseLink] using hh

/-- The positive-height link is an actual finite polytope with the expected
intrinsic dimension whenever the parent strictly exceeds the collapsed face. -/
theorem transverseLink_finite_dimension {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (hd : affineDimension G < affineDimension P) :
    FinitePolytope (transverseLink hP hG hc) ∧
      affineDimension (transverseLink hP hG hc) + affineDimension G + 1 = affineDimension P := by
  have hdimQ := transverse_image_dimension_add hG.2.1 c
  have hpos : 0 < affineDimension (transverseProjection G c '' P) := by omega
  obtain ⟨hS, hdS⟩ := finitePolytope_heightSection_finite_dimension
    (finitePolytope_transverse hP G c) (transverse_origin_extreme hP hG hc)
    (transverseCutHeight hP hG hc) (transverseCutHeight_ge_one hP hG hc) hpos
  exact ⟨hS, by change affineDimension (transverseLink hP hG hc) + 1 = _ at hdS; omega⟩

/-- An actual polygon face of a uniform five-polytope has a genuine
finite two-dimensional transverse link. -/
theorem unitUniform5_transverseLink {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {k : ℕ} (hG : PolygonFace P G k) {c : Space 5} (hc : c ∈ G) :
    FinitePolytope (transverseLink (uniform_finitePolytope hP.1) hG.1 hc) ∧
      affineDimension (transverseLink (uniform_finitePolytope hP.1) hG.1 hc) = 2 := by
  have hdP := uniform_dimension hP.1
  obtain ⟨hS, hdS⟩ := transverseLink_finite_dimension (uniform_finitePolytope hP.1) hG.1 hc
    (by rw [hG.2.1, hdP]; norm_num)
  have hdG := hG.2.1
  exact ⟨hS, by omega⟩

/-- The collapsed polygon corresponds exactly to the empty link face. -/
theorem transverseLinkFaceEquiv_nonempty_iff {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (F : {F : GeometricFace P // G ⊆ F.val}) :
    (transverseLinkFaceEquiv hP hG hc F).val.Nonempty ↔ F.val.val ≠ G := by
  constructor
  · rintro ⟨z, hz⟩ heq
    rw [transverseLinkFaceEquiv_apply, heq, transverseProjection_face_image G hc] at hz
    have hz0 : z = 0 := hz.1
    have hheight := hz.2.2
    rw [hz0, map_zero] at hheight
    norm_num at hheight
  · exact transverseLinkFaceEquiv_nonempty hP hG hc F

/-- Every nonempty actual link face has a unique actual parent face, with
its exact original rank. -/
theorem transverseLink_face_unique_lift {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    {C : Set (affineSpan ℝ G).directionᗮ}
    (hC : IsConvexFace (transverseLink hP hG hc) C) (hne : C.Nonempty) :
    ∃! F : Set E, IsConvexFace P F ∧ G ⊆ F ∧
      affineDimension F = affineDimension C + affineDimension G + 1 ∧
      (transverseProjection G c '' F) ∩ transverseLink hP hG hc = C := by
  let e := transverseLinkFaceEquiv hP hG hc
  let F := e.symm ⟨C, hC⟩
  have hsection : (transverseProjection G c '' F.val.val) ∩ transverseLink hP hG hc = C := by
    rw [← transverseLinkFaceEquiv_apply]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨C, hC⟩)
  have hFne : F.val.val ≠ G :=
    (transverseLinkFaceEquiv_nonempty_iff hP hG hc F).mp (by
      rw [transverseLinkFaceEquiv_apply, hsection]
      exact hne)
  have hd := transverseLinkFaceEquiv_dimension hP hG hc F hFne
  rw [transverseLinkFaceEquiv_apply, hsection] at hd
  refine ⟨F.val.val, ⟨F.val.property, F.property, hd.symm, hsection⟩, ?_⟩
  rintro H ⟨hH, hGH, _, hHC⟩
  let H' : {F : GeometricFace P // G ⊆ F.val} := ⟨⟨H, hH⟩, hGH⟩
  have heq : e H' = e F := by
    apply Subtype.ext
    change (transverseLinkFaceEquiv hP hG hc H').val =
      (transverseLinkFaceEquiv hP hG hc F).val
    rw [transverseLinkFaceEquiv_apply, transverseLinkFaceEquiv_apply, hsection]
    exact hHC
  exact congrArg (fun F => F.val.val) (e.injective heq)

/-- An actual three-dimensional cell above a polygon gives an actual link
vertex; the singleton is the literal projected cell section. -/
theorem transverseLink_cell_vertex {P G F : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) (hdG : affineDimension G = 2) {c : E} (hc : c ∈ G)
    (hF : IsConvexFace P F) (hGF : G ⊆ F) (hdF : affineDimension F = 3) :
    ∃ w ∈ (transverseLink hP hG hc).extremePoints ℝ,
      (transverseProjection G c '' F) ∩ transverseLink hP hG hc = {w} := by
  let F' : {F : GeometricFace P // G ⊆ F.val} := ⟨⟨F, hF⟩, hGF⟩
  have hne : F ≠ G := by intro h; have hh := congrArg affineDimension h; omega
  have hn := transverseLinkFaceEquiv_nonempty hP hG hc F' hne
  have hd := transverseLinkFaceEquiv_dimension hP hG hc F' hne
  have hd' : affineDimension (transverseLinkFaceEquiv hP hG hc F').val = 0 := by
    change affineDimension (transverseLinkFaceEquiv hP hG hc F').val + affineDimension G + 1 =
      affineDimension F at hd
    omega
  obtain ⟨w, hw⟩ := nonempty_affineDimension_zero_singleton hn hd'
  refine ⟨w, ?_, ?_⟩
  · apply (singleton_face_iff_extremePoint _ w).mp
    exact hw ▸ (transverseLinkFaceEquiv hP hG hc F').property
  · simpa only [transverseLinkFaceEquiv_apply] using hw

/-- Conversely, every actual link vertex comes from a unique actual
three-dimensional cell containing the polygon. -/
theorem transverseLink_vertex_unique_cell {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) (hdG : affineDimension G = 2) {c : E} (hc : c ∈ G)
    {w : (affineSpan ℝ G).directionᗮ} (hw : w ∈ (transverseLink hP hG hc).extremePoints ℝ) :
    ∃! F : Set E, IsConvexFace P F ∧ G ⊆ F ∧ affineDimension F = 3 ∧
      (transverseProjection G c '' F) ∩ transverseLink hP hG hc = {w} := by
  have hh := transverseLink_face_unique_lift hP hG hc
    ((singleton_face_iff_extremePoint _ w).mpr hw) (singleton_nonempty w)
  simpa only [affineDimension_singleton, hdG, Nat.zero_add] using hh

/-- An actual parent facet above the polygon gives an actual exposed link
edge, with endpoints that are actual link vertices. -/
theorem transverseLink_facet_edge {P G F : Set E} (hP : FinitePolytope P)
    (hdP : affineDimension P = 5) (hG : IsConvexFace P G) (hdG : affineDimension G = 2)
    {c : E} (hc : c ∈ G) (hF : Facet P F) (hGF : G ⊆ F) :
    ∃ x y, Edge (transverseLink hP hG hc) x y ∧
      (transverseProjection G c '' F) ∩ transverseLink hP hG hc = segment ℝ x y := by
  let F' : {F : GeometricFace P // G ⊆ F.val} := ⟨⟨F, hF.1⟩, hGF⟩
  have hdF : affineDimension F = 4 := by have hh := hF.2.2; omega
  have hne : F ≠ G := by intro h; have hh := congrArg affineDimension h; omega
  have hn := transverseLinkFaceEquiv_nonempty hP hG hc F' hne
  have hd := transverseLinkFaceEquiv_dimension hP hG hc F' hne
  have hd' : affineDimension (transverseLinkFaceEquiv hP hG hc F').val = 1 := by
    change affineDimension (transverseLinkFaceEquiv hP hG hc F').val + affineDimension G + 1 =
      affineDimension F at hd
    omega
  have hS := (transverseLink_finite_dimension hP hG hc (by omega)).1
  obtain ⟨x, y, he, hseg⟩ := finitePolytope_oneFace_edge hS
    (transverseLinkFaceEquiv hP hG hc F').property hn hd'
  exact ⟨x, y, he, by simpa only [transverseLinkFaceEquiv_apply] using hseg⟩

/-- Every actual link edge comes from a unique actual parent facet
containing the polygon. -/
theorem transverseLink_edge_unique_facet {P G : Set E} (hP : FinitePolytope P)
    (hdP : affineDimension P = 5) (hG : IsConvexFace P G) (hdG : affineDimension G = 2)
    {c : E} (hc : c ∈ G) {x y : (affineSpan ℝ G).directionᗮ}
    (he : Edge (transverseLink hP hG hc) x y) :
    ∃! F : Set E, Facet P F ∧ G ⊆ F ∧
      (transverseProjection G c '' F) ∩ transverseLink hP hG hc = segment ℝ x y := by
  obtain ⟨F, ⟨hF, hGF, hdF, hsection⟩, hunique⟩ := transverseLink_face_unique_lift hP hG hc
    (edge_isConvexFace he) ⟨x, left_mem_segment ℝ x y⟩
  have hrank := edge_dimension he
  have hfacet : Facet P F := ⟨hF, ⟨c, hGF hc⟩, by omega⟩
  refine ⟨F, ⟨hfacet, hGF, hsection⟩, ?_⟩
  rintro H ⟨hH, hGH, hHsection⟩
  apply hunique
  exact ⟨hH.1, hGH, by have hh := hH.2.2; omega, hHsection⟩

end Uniform5.Composition
