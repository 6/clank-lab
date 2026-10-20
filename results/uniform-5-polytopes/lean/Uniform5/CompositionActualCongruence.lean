import Uniform5.CompositionInitialCongruence
import Uniform5.CompositionCenteredModel
import Uniform5.CompositionRidgeSpanning
import Uniform5.CompositionFacetGraph
import Uniform5.CompositionRidgeTangents

/-!
# Congruence from exact correspondences of actual facets

This module assembles the geometric inputs to Lemma D from finite convex
polytopes, their actual facets and ridges, and their origin-centred spheres.
-/

noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- An isometry's values on the vertices determine its values on the entire
finite polytope, and even its affine span. -/
theorem affineIsometry_eqOn_finitePolytope {P : Set E} (hP : FinitePolytope P)
    (g h : E ≃ᵃⁱ[ℝ] E) (heq : ∀ x ∈ P.extremePoints ℝ, g x = h x) :
    ∀ x ∈ affineSpan ℝ P, g x = h x := by
  intro x hx
  rw [finitePolytope_eq_convexHull_extremePoints hP, affineSpan_convexHull] at hx
  refine affineSpan_induction (p := fun x => g x = h x) hx heq ?_
  intro c u v w hu hv hw
  simp only [AffineIsometryEquiv.map_vadd, map_smul,
    AffineIsometryEquiv.map_vsub, hu, hv, hw]

/-- Pythagoras at the actual projection of the origin to a face's span. -/
theorem spanProjection_norm_sq (F : Set E) (hne : F.Nonempty) {x : E}
    (hx : x ∈ affineSpan ℝ F) :
    ‖x‖ ^ 2 = dist x (spanProjection F hne 0) ^ 2 + ‖spanProjection F hne 0‖ ^ 2 := by
  letI : Nonempty (affineSpan ℝ F) := ⟨⟨hne.choose, subset_affineSpan ℝ F hne.choose_spec⟩⟩
  have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := affineSpan ℝ F) (0 : E) hx
  simpa only [spanProjection, dist_zero_right, dist_zero_left, pow_two] using h

/-- Projection to an affine span commutes with every ambient orthogonal
transformation. -/
theorem spanProjection_linearIsometry_image (A : E ≃ₗᵢ[ℝ] E) (F : Set E)
    (hne : F.Nonempty) :
    spanProjection (A '' F) (hne.image A) 0 = A (spanProjection F hne 0) := by
  let p := spanProjection F hne (0 : E)
  have hp : p ∈ affineSpan ℝ F := spanProjection_mem F hne 0
  have ho : p ∈ (affineSpan ℝ F).directionᗮ := by
    simpa only [sub_zero] using spanProjection_sub_mem_orthogonal F hne (0 : E)
  have hspan : affineSpan ℝ (A '' F) = (affineSpan ℝ F).map A.toAffineIsometryEquiv.toAffineMap :=
    (AffineSubspace.map_span A.toAffineIsometryEquiv.toAffineMap F).symm
  have hp' : A p ∈ affineSpan ℝ (A '' F) := by
    rw [hspan]
    exact ⟨p, hp, rfl⟩
  have ho' : A p ∈ (affineSpan ℝ (A '' F)).directionᗮ := by
    rw [hspan, AffineSubspace.map_direction]
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨x, hx, rfl⟩
    change inner (A x) (A p) = (0 : ℝ)
    rw [A.inner_map_map]
    exact (Submodule.mem_orthogonal _ _).mp ho x hx
  letI : Nonempty (affineSpan ℝ (A '' F)) := ⟨⟨A p, hp'⟩⟩
  have h := EuclideanGeometry.orthogonalProjection_vadd_eq_self hp'
    ((affineSpan ℝ (A '' F)).directionᗮ.neg_mem ho')
  have hh := congrArg (fun z : affineSpan ℝ (A '' F) => (z : E)) h
  simpa only [vadd_eq_add, neg_add_cancel, Subtype.coe_mk, spanProjection] using hh

/-- The corresponding target facet is the convex hull of the images of
exactly the actual source vertices in the source facet. -/
noncomputable def matchedVertexFacet {P P' : Set E}
    (e : P.extremePoints ℝ ≃ P'.extremePoints ℝ) (F : Set E) : Set E :=
  convexHull ℝ ((fun i : P.extremePoints ℝ => (e i : E)) '' {i | (i : E) ∈ F})

omit [FiniteDimensional ℝ E] in
/-- Agreement on actual facet vertex labels identifies its entire image. -/
theorem image_facet_eq_matchedVertexFacet {P P' F : Set E}
    (hP : FinitePolytope P) (hF : Facet P F)
    (e : P.extremePoints ℝ ≃ P'.extremePoints ℝ) (g : E ≃ᵃⁱ[ℝ] E)
    (hmatch : ∀ i : P.extremePoints ℝ, (i : E) ∈ F → g i = (e i : E)) :
    g '' F = matchedVertexFacet e F := by
  have hh : g '' F = convexHull ℝ (g '' F.extremePoints ℝ) := by
    calc
      g '' F = g '' convexHull ℝ (F.extremePoints ℝ) :=
        congrArg (fun S => g '' S) (finitePolytope_eq_convexHull_extremePoints (finitePolytope_facet hP hF))
      _ = _ := g.toAffineMap.image_convexHull _
  rw [hh]
  unfold matchedVertexFacet
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let i : P.extremePoints ℝ := ⟨x, hF.1.2.extremePoints_subset_extremePoints hx⟩
    exact ⟨i, hx.1, (hmatch i hx.1).symm⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ?_, hmatch i hi⟩
    rw [face_extremePoints_eq hF.1]
    exact ⟨hi, i.property⟩

/-- Exact metric facet data indexed by an actual bijection of vertices.
The target facets are concrete hulls, and both centres are actual orthogonal
projections lying in their respective relative interiors. -/
structure ExactCenteredFacetMatching (P P' : Set E) where
  vertexEquiv : P.extremePoints ℝ ≃ P'.extremePoints ℝ
  target_isFacet : ∀ F, Facet P F → Facet P' (matchedVertexFacet vertexEquiv F)
  source_projection_interior : ∀ F (hF : Facet P F),
    spanProjection F hF.2.1 0 ∈ intrinsicInterior ℝ F
  target_projection_interior : ∀ F (hF : Facet P F),
    spanProjection (matchedVertexFacet vertexEquiv F) (target_isFacet F hF).2.1 0 ∈
      intrinsicInterior ℝ (matchedVertexFacet vertexEquiv F)
  correspondence : ∀ F (hF : Facet P F),
    ExactFacetCorrespondence (fun i : P.extremePoints ℝ => (i : E))
      (fun i => (vertexEquiv i : E)) {i | (i : E) ∈ F}
      (spanProjection F hF.2.1 0)
      (spanProjection (matchedVertexFacet vertexEquiv F) (target_isFacet F hF).2.1 0)

namespace ExactCenteredFacetMatching

variable {P P' : Set E} (M : ExactCenteredFacetMatching P P')

/-- The exact local comparison sends the entire actual source facet onto
its specified actual target facet. -/
theorem comparison_image (hP : FinitePolytope P) {F : Set E} (hF : Facet P F) :
    (M.correspondence F hF).comparison '' F = matchedVertexFacet M.vertexEquiv F :=
  image_facet_eq_matchedVertexFacet hP hF M.vertexEquiv _
    (M.correspondence F hF).comparison_points

/-- The matched hull contains no additional target vertex labels. -/
theorem vertex_mem_matchedFacet_iff {F : Set E} (hF : Facet P F)
    (i : P.extremePoints ℝ) :
    (M.vertexEquiv i : E) ∈ matchedVertexFacet M.vertexEquiv F ↔ (i : E) ∈ F := by
  constructor
  · intro hi
    have hext : (M.vertexEquiv i : E) ∈
        (matchedVertexFacet M.vertexEquiv F).extremePoints ℝ := by
      rw [face_extremePoints_eq (M.target_isFacet F hF).1]
      exact ⟨hi, (M.vertexEquiv i).property⟩
    obtain ⟨j, hj, hji⟩ := extremePoints_convexHull_subset hext
    have hji' : j = i := M.vertexEquiv.injective (Subtype.ext hji)
    exact hji' ▸ hj
  · intro hi
    exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩

/-- Distinct actual source facets have distinct actual matched facets. -/
theorem matchedFacet_injective (hP : FinitePolytope P) {F G : Set E}
    (hF : Facet P F) (hG : Facet P G)
    (heq : matchedVertexFacet M.vertexEquiv F = matchedVertexFacet M.vertexEquiv G) : F = G := by
  have hsub {A B : Set E} (hA : Facet P A) (hB : Facet P B)
      (hh : matchedVertexFacet M.vertexEquiv A = matchedVertexFacet M.vertexEquiv B) : A ⊆ B := by
    rw [finitePolytope_eq_convexHull_extremePoints (finitePolytope_facet hP hA)]
    apply convexHull_min _ hB.1.1
    intro x hx
    let i : P.extremePoints ℝ := ⟨x, hA.1.2.extremePoints_subset_extremePoints hx⟩
    have hi := (M.vertex_mem_matchedFacet_iff hA i).mpr hx.1
    rw [hh] at hi
    exact (M.vertex_mem_matchedFacet_iff hB i).mp hi
  exact Set.Subset.antisymm (hsub hF hG heq) (hsub hG hF heq.symm)

/-- Corresponding facets on a common origin sphere have equal offsets.
This uses the actual projection centres and the exact metric comparison. -/
theorem projection_norm_eq (hP : FinitePolytope P) (R : ℝ)
    (hs : ∀ x ∈ P.extremePoints ℝ, ‖x‖ = R)
    (ht : ∀ x ∈ P'.extremePoints ℝ, ‖x‖ = R)
    {F : Set E} (hF : Facet P F) :
    ‖spanProjection F hF.2.1 0‖ =
      ‖spanProjection (matchedVertexFacet M.vertexEquiv F) (M.target_isFacet F hF).2.1 0‖ := by
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty (finitePolytope_facet hP hF)
  let i : P.extremePoints ℝ := ⟨x, hF.1.2.extremePoints_subset_extremePoints hx⟩
  let D := M.correspondence F hF
  have hy : (M.vertexEquiv i : E) ∈ matchedVertexFacet M.vertexEquiv F :=
    subset_convexHull ℝ _ ⟨i, hx.1, rfl⟩
  have hd : dist x (spanProjection F hF.2.1 0) =
      dist (M.vertexEquiv i : E)
        (spanProjection (matchedVertexFacet M.vertexEquiv F) (M.target_isFacet F hF).2.1 0) := by
    have h := D.comparison.isometry.dist_eq (i : E) (spanProjection F hF.2.1 0)
    rw [D.comparison_points i hx.1, D.comparison_centre] at h
    exact h.symm
  have hx2 := spanProjection_norm_sq F hF.2.1 (subset_affineSpan ℝ F hx.1)
  have hy2 := spanProjection_norm_sq _ (M.target_isFacet F hF).2.1
    (subset_affineSpan ℝ _ hy)
  rw [hs x i.property, hd] at hx2
  rw [ht _ (M.vertexEquiv i).property] at hy2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

/-- Actual tangent geometry forces agreement of the next facet centre
once the existing facet has been aligned on its actual vertices. -/
theorem adjacent_centre_agreement
    (hP : FinitePolytope P) (hP' : FinitePolytope P')
    (hfull : affineDimension P = Module.finrank ℝ E)
    (hfull' : affineDimension P' = Module.finrank ℝ E)
    (hzero : (0 : E) ∈ intrinsicInterior ℝ P)
    (hzero' : (0 : E) ∈ intrinsicInterior ℝ P')
    (R₀ : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x‖ = R₀)
    (ht : ∀ x ∈ P'.extremePoints ℝ, ‖x‖ = R₀)
    {F G : Set E} (hFG : FacetAdjacent P F G)
    (A : E ≃ₗᵢ[ℝ] E)
    (hmatch : ∀ i : P.extremePoints ℝ, (i : E) ∈ F → A i = (M.vertexEquiv i : E)) :
    A (spanProjection G hFG.2.1.2.1 0) =
      spanProjection (matchedVertexFacet M.vertexEquiv G)
        (M.target_isFacet G hFG.2.1).2.1 0 := by
  obtain ⟨hF, hG, hFGne, R, hR, hRne, hdR, hRF, hRG⟩ := hFG
  let a := A.toAffineIsometryEquiv
  have halign : A '' F = matchedVertexFacet M.vertexEquiv F :=
    image_facet_eq_matchedVertexFacet hP hF M.vertexEquiv a hmatch
  have htargetR : A '' R ⊆ matchedVertexFacet M.vertexEquiv G := by
    rintro _ ⟨x, hx, rfl⟩
    let D := M.correspondence G hG
    have heq : A x = D.comparison x := by
      apply affineIsometry_eqOn_finitePolytope (finitePolytope_face hP hR hRne) a D.comparison
        _ x (subset_affineSpan ℝ R hx)
      intro y hy
      let i : P.extremePoints ℝ := ⟨y, hR.2.extremePoints_subset_extremePoints hy⟩
      exact (hmatch i (hRF hy.1)).trans (D.comparison_points i (hRG hy.1)).symm
    rw [heq]
    exact (M.comparison_image hP hG).le ⟨x, hRG hx, rfl⟩
  have hint {S : Set E} (hS : Facet P S) :
      spanProjection (A '' S) (hS.2.1.image A) 0 ∈ intrinsicInterior ℝ (A '' S) := by
    rw [spanProjection_linearIsometry_image]
    change A (spanProjection S hS.2.1 0) ∈ intrinsicInterior ℝ (a.toAffineIsometry '' S)
    rw [a.toAffineIsometry.image_intrinsicInterior]
    exact ⟨_, M.source_projection_interior S hS, rfl⟩
  have hz : (0 : E) ∈ intrinsicInterior ℝ (A '' P) := by
    change (0 : E) ∈ intrinsicInterior ℝ (a.toAffineIsometry '' P)
    rw [a.toAffineIsometry.image_intrinsicInterior]
    exact ⟨0, hzero, A.map_zero⟩
  have hFtarget : Facet P' (A '' F) := by
    rw [halign]
    exact M.target_isFacet F hF
  have hFGtarget : A '' F ≠ matchedVertexFacet M.vertexEquiv G := by
    rw [halign]
    exact fun h => hFGne (M.matchedFacet_injective hP hF hG h)
  have hrad : ‖spanProjection (A '' G) (hG.2.1.image A) 0‖ =
      ‖spanProjection (matchedVertexFacet M.vertexEquiv G) (M.target_isFacet G hG).2.1 0‖ := by
    rw [spanProjection_linearIsometry_image, A.norm_map]
    exact M.projection_norm_eq hP R₀ hs ht hG
  have hdata := finitePolytope_oppositeTangentData
    (finitePolytope_image a hP) hP' (facet_image a hF) hFtarget
    (facet_image a hG) (M.target_isFacet G hG)
    (fun h => hFGne (A.injective.image_injective h)) hFGtarget
    (hRne.image A) (Set.image_mono hRF) (Set.image_mono hRG) htargetR
    (by
      change affineDimension (a '' R) + 2 = affineDimension (a '' P)
      simpa only [affineDimension_image] using hdR)
    (by simpa only [affineDimension_image] using hfull) hfull' hz hzero'
    (hint hF) (hint hG) (M.target_projection_interior G hG) hrad
  exact (spanProjection_linearIsometry_image A G hG.2.1).symm.trans hdata.eq

/-- Agreement propagates across every actual adjacent-facet pair. Ridge
spanning follows from the next facet centre's actual relative interior. -/
theorem adjacent_vertex_agreement
    (hP : FinitePolytope P) (hP' : FinitePolytope P')
    (hfull : affineDimension P = Module.finrank ℝ E)
    (hfull' : affineDimension P' = Module.finrank ℝ E)
    (hzero : (0 : E) ∈ intrinsicInterior ℝ P)
    (hzero' : (0 : E) ∈ intrinsicInterior ℝ P')
    (R₀ : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x‖ = R₀)
    (ht : ∀ x ∈ P'.extremePoints ℝ, ‖x‖ = R₀)
    {F G : Set E} (hFG : FacetAdjacent P F G)
    (A : E ≃ₗᵢ[ℝ] E)
    (hmatch : ∀ i : P.extremePoints ℝ, (i : E) ∈ F → A i = (M.vertexEquiv i : E)) :
    ∀ i : P.extremePoints ℝ, (i : E) ∈ G → A i = (M.vertexEquiv i : E) := by
  have hc := M.adjacent_centre_agreement hP hP' hfull hfull' hzero hzero' R₀ hs ht hFG A hmatch
  obtain ⟨hF, hG, _, R, hR, hRne, hdR, hRF, hRG⟩ := hFG
  let c := spanProjection G hG.2.1 (0 : E)
  let D := M.correspondence G hG
  intro i hi
  have hh := affine_rigidity_of_ridge_centre A.toAffineIsometryEquiv D.comparison
    (R.extremePoints ℝ) c (i : E)
    (hc.trans D.comparison_centre.symm)
    (by
      intro x hx
      let j : P.extremePoints ℝ := ⟨x, hR.2.extremePoints_subset_extremePoints hx⟩
      exact (hmatch j (hRF hx.1)).trans (D.comparison_points j (hRG hx.1)).symm)
    (actual_ridge_centre_spans hP hG hR hRne hRG hdR
      (M.source_projection_interior G hG) hi)
  exact hh.trans (D.comparison_points i hi)

/-- Exact local correspondences imply global Euclidean congruence for
full-dimensional centred finite polytopes on the same sphere. Connectivity,
initial extension, ridge spanning, offset equality and tangent uniqueness
are all proved consequences of the concrete geometric assumptions. -/
theorem congruence
    (hP : FinitePolytope P) (hP' : FinitePolytope P')
    (hdim : 2 ≤ affineDimension P)
    (hfull : affineDimension P = Module.finrank ℝ E)
    (hfull' : affineDimension P' = Module.finrank ℝ E)
    (hzero : (0 : E) ∈ intrinsicInterior ℝ P)
    (hzero' : (0 : E) ∈ intrinsicInterior ℝ P')
    (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x‖ = R)
    (ht : ∀ x ∈ P'.extremePoints ℝ, ‖x‖ = R) :
    ∃ A : E ≃ₗᵢ[ℝ] E,
      (∀ i : P.extremePoints ℝ, A i = (M.vertexEquiv i : E)) ∧ A '' P = P' := by
  have hcover (i : P.extremePoints ℝ) : ∃ F, Facet P F ∧ (i : E) ∈ F := by
    have hproper : ({(i : E)} : Set E) ≠ P := by
      intro hh
      rw [← hh, affineDimension_singleton] at hdim
      omega
    obtain ⟨F, hF, hiF⟩ := finitePolytope_face_subset_facet hP
      ((singleton_face_iff_extremePoint P i).mpr i.property)
      (Set.singleton_nonempty _) hproper
    exact ⟨F, hF, hiF (Set.mem_singleton _)⟩
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty hP
  obtain ⟨F₀, hF₀, _⟩ := hcover ⟨x, hx⟩
  obtain ⟨A, hA⟩ := (M.correspondence F₀ hF₀).initial_facet_linear_extension_of_norm_eq
    (fun i _ => (hs i i.property).trans (ht _ (M.vertexEquiv i).property).symm)
  have hfacets (F : Set E) (hF : Facet P F) :
      ∀ i : P.extremePoints ℝ, (i : E) ∈ F → A i = (M.vertexEquiv i : E) := by
    have hpath := finitePolytope_facetGraph_connected hP hdim hF₀ hF
    clear hF
    induction hpath with
    | refl => exact hA
    | tail _ hstep ih =>
      exact M.adjacent_vertex_agreement hP hP' hfull hfull' hzero hzero' R hs ht hstep A ih
  have hall (i : P.extremePoints ℝ) : A i = (M.vertexEquiv i : E) := by
    obtain ⟨F, hF, hi⟩ := hcover i
    exact hfacets F hF i hi
  refine ⟨A, hall, ?_⟩
  have hvertices : A '' P.extremePoints ℝ = P'.extremePoints ℝ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hall ⟨z, hz⟩]
      exact (M.vertexEquiv ⟨z, hz⟩).property
    · intro hy
      let i := M.vertexEquiv.symm ⟨y, hy⟩
      refine ⟨i, i.property, ?_⟩
      rw [hall]
      exact congrArg Subtype.val (M.vertexEquiv.apply_symm_apply ⟨y, hy⟩)
  calc
    A '' P = A '' convexHull ℝ (P.extremePoints ℝ) :=
      congrArg (fun S => A '' S) (finitePolytope_eq_convexHull_extremePoints hP)
    _ = convexHull ℝ (A '' P.extremePoints ℝ) := A.toAffineIsometryEquiv.toAffineMap.image_convexHull _
    _ = P' := by rw [hvertices, ← finitePolytope_eq_convexHull_extremePoints hP']

/-- In particular the matching covers every target facet; this need not
be assumed as an additional combinatorial hypothesis. -/
theorem target_facets_surjective
    (hP : FinitePolytope P) (hP' : FinitePolytope P')
    (hdim : 2 ≤ affineDimension P)
    (hfull : affineDimension P = Module.finrank ℝ E)
    (hfull' : affineDimension P' = Module.finrank ℝ E)
    (hzero : (0 : E) ∈ intrinsicInterior ℝ P)
    (hzero' : (0 : E) ∈ intrinsicInterior ℝ P')
    (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x‖ = R)
    (ht : ∀ x ∈ P'.extremePoints ℝ, ‖x‖ = R)
    {G : Set E} (hG : Facet P' G) :
    ∃ F, Facet P F ∧ matchedVertexFacet M.vertexEquiv F = G := by
  obtain ⟨A, hA, him⟩ := M.congruence hP hP' hdim hfull hfull' hzero hzero' R hs ht
  let a := A.toAffineIsometryEquiv
  have hback : a.symm '' P' = P := by
    rw [← him]
    exact affineIsometry_symm_image_image a P
  have hF := facet_image a.symm hG
  rw [hback] at hF
  refine ⟨a.symm '' G, hF, ?_⟩
  rw [← image_facet_eq_matchedVertexFacet hP hF M.vertexEquiv a (fun i _ => hA i)]
  exact affineIsometry_image_symm_image a G

end ExactCenteredFacetMatching

/-- The four-dimensional form needed for the paper's metric vertex figures.
Only actual finite polytopes, exact facet matching, centres and sphere data
remain as premises; the geometric propagation chain is discharged. -/
theorem centered_four_dimensional_congruence {P P' : Set (Space 4)}
    (M : ExactCenteredFacetMatching P P')
    (hP : FinitePolytope P) (hP' : FinitePolytope P')
    (hdim : affineDimension P = 4) (hdim' : affineDimension P' = 4)
    (hzero : (0 : Space 4) ∈ intrinsicInterior ℝ P)
    (hzero' : (0 : Space 4) ∈ intrinsicInterior ℝ P')
    (R : ℝ) (hs : ∀ x ∈ P.extremePoints ℝ, ‖x‖ = R)
    (ht : ∀ x ∈ P'.extremePoints ℝ, ‖x‖ = R) :
    ∃ A : Space 4 ≃ₗᵢ[ℝ] Space 4,
      (∀ i : P.extremePoints ℝ, A i = (M.vertexEquiv i : Space 4)) ∧ A '' P = P' := by
  exact M.congruence hP hP' (by omega)
    (by simpa only [finrank_euclideanSpace_fin] using hdim)
    (by simpa only [finrank_euclideanSpace_fin] using hdim') hzero hzero' R hs ht

end Uniform5.Composition
