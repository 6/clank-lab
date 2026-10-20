import Uniform5.CompositionRidgeIncidence
import Uniform5.CompositionEdgeFaces
import Uniform5.CompositionGraph

/-!
# Connectivity of the actual facet adjacency graph

Adjacency means two distinct geometric facets share a nonempty actual
codimension-two face. Small sections connect the facets at each vertex;
the actual vertex-edge graph then connects these stars globally.
-/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual facets are adjacent when they share a genuine ridge. -/
noncomputable def FacetAdjacent (P F G : Set E) : Prop :=
  Facet P F ∧ Facet P G ∧ F ≠ G ∧ ∃ R,
    IsConvexFace P R ∧ R.Nonempty ∧ affineDimension R + 2 = affineDimension P ∧
      R ⊆ F ∧ R ⊆ G

theorem facetAdjacent_image (g : E ≃ᵃⁱ[ℝ] E) {P F G : Set E}
    (h : FacetAdjacent P F G) : FacetAdjacent (g '' P) (g '' F) (g '' G) := by
  obtain ⟨hF, hG, hFG, R, hR, hne, hdim, hRF, hRG⟩ := h
  refine ⟨facet_image g hF, facet_image g hG,
    fun heq => hFG (g.injective.image_injective heq), g '' R,
    isConvexFace_image g hR, hne.image g, ?_, Set.image_mono hRF, Set.image_mono hRG⟩
  simpa only [affineDimension_image] using hdim

theorem facetPath_image (g : E ≃ᵃⁱ[ℝ] E) {P F G : Set E}
    (h : Relation.ReflTransGen (FacetAdjacent P) F G) :
    Relation.ReflTransGen (FacetAdjacent (g '' P)) (g '' F) (g '' G) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (facetAdjacent_image g hstep)

/-- Lifting section faces is inclusion preserving. -/
theorem sectionFaceLift_mono {P A B : Set E} (L : E →L[ℝ] ℝ) (h : A ⊆ B) :
    sectionFaceLift P L A ⊆ sectionFaceLift P L B := by
  rintro x ⟨hx, hzero | hA⟩
  · exact ⟨hx, Or.inl hzero⟩
  · exact ⟨hx, Or.inr (h hA)⟩

/-- Adjacent facets in a genuine small vertex section lift to adjacent
facets of the parent polytope, with the shared ridge lifted geometrically. -/
theorem facetAdjacent_sectionFaceLift [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hdim : 0 < affineDimension (convexHull ℝ (V : Set E)))
    {A B : Set E}
    (h : FacetAdjacent (heightSection (convexHull ℝ (V : Set E)) L) A B) :
    FacetAdjacent (convexHull ℝ (V : Set E))
      (sectionFaceLift (convexHull ℝ (V : Set E)) L A)
      (sectionFaceLift (convexHull ℝ (V : Set E)) L B) := by
  let P := convexHull ℝ (V : Set E)
  let S := heightSection P L
  obtain ⟨hA, hB, hAB, R, hR, hRne, hRdim, hRA, hRB⟩ := h
  have hRlift := sectionFaceLift_isFace V hzero L hheight hR
  have hRzero : (0 : E) ∈ sectionFaceLift P L R :=
    ⟨subset_convexHull ℝ (V : Set E) hzero, Or.inl rfl⟩
  have hRsection : sectionFaceLift P L R ∩ S = R := sectionFaceLift_section L hR.2.1
  have hRnot : sectionFaceLift P L R ≠ {0} :=
    (apexFace_section_nonempty_iff V L hheight hRlift hRzero).mp
      (hRsection.symm ▸ hRne)
  have hdimR := apexFace_section_dimension V hzero L hheight hRlift hRzero hRnot
  rw [hRsection] at hdimR
  have hdimP := (finiteHull_heightSection_finite_dimension V hzero L hheight hdim).2
  refine ⟨sectionFacet_lift_facet V hzero L hheight hA,
    sectionFacet_lift_facet V hzero L hheight hB, ?_, sectionFaceLift P L R,
    hRlift, ⟨0, hRzero⟩, ?_, sectionFaceLift_mono L hRA, sectionFaceLift_mono L hRB⟩
  · intro heq
    have hh := congrArg (fun F => F ∩ S) heq
    change sectionFaceLift P L A ∩ heightSection P L =
      sectionFaceLift P L B ∩ heightSection P L at hh
    rw [sectionFaceLift_section L hA.1.2.1, sectionFaceLift_section L hB.1.2.1] at hh
    exact hAB hh
  · change affineDimension (sectionFaceLift P L R) + 2 = affineDimension P
    change affineDimension R + 1 = affineDimension (sectionFaceLift P L R) at hdimR
    change affineDimension S + 1 = affineDimension P at hdimP
    change affineDimension R + 2 = affineDimension S at hRdim
    omega

/-- A path through actual section facets lifts to a path through actual
parent facets. -/
theorem facetPath_sectionFaceLift [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hdim : 0 < affineDimension (convexHull ℝ (V : Set E)))
    {A B : Set E}
    (h : Relation.ReflTransGen (FacetAdjacent (heightSection (convexHull ℝ (V : Set E)) L)) A B) :
    Relation.ReflTransGen (FacetAdjacent (convexHull ℝ (V : Set E)))
      (sectionFaceLift (convexHull ℝ (V : Set E)) L A)
      (sectionFaceLift (convexHull ℝ (V : Set E)) L B) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (facetAdjacent_sectionFaceLift V hzero L hheight hdim hstep)

/-- Reconstructing an apex face from its actual section recovers the face. -/
theorem sectionFaceLift_apexFace [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hFzero : (0 : E) ∈ F) :
    sectionFaceLift (convexHull ℝ (V : Set E)) L
      (F ∩ heightSection (convexHull ℝ (V : Set E)) L) = F := by
  apply apexFace_eq_of_section_eq V L hheight
    (sectionFaceLift_isFace V hzero L hheight
      (face_heightSection (convex_convexHull ℝ (V : Set E)) hF L)) hF
    ⟨subset_convexHull ℝ (V : Set E) hzero, Or.inl rfl⟩ hFzero
  exact sectionFaceLift_section L inter_subset_right

/-- Local connectivity at all vertices gives global facet connectivity,
using the already proved actual edge graph and actual edge containment. -/
theorem facetPath_of_connected_vertex_stars [FiniteDimensional ℝ E]
    {P F G : Set E} (hP : FinitePolytope P) (hdim : 2 ≤ affineDimension P)
    (hstar : ∀ {v : E}, v ∈ P.extremePoints ℝ → ∀ {A B : Set E},
      Facet P A → Facet P B → v ∈ A → v ∈ B →
      Relation.ReflTransGen (FacetAdjacent P) A B)
    (hF : Facet P F) (hG : Facet P G) :
    Relation.ReflTransGen (FacetAdjacent P) F G := by
  obtain ⟨v, hvF⟩ := finitePolytope_extremePoints_nonempty (finitePolytope_facet hP hF)
  obtain ⟨w, hwG⟩ := finitePolytope_extremePoints_nonempty (finitePolytope_facet hP hG)
  have hvP := hF.1.2.extremePoints_subset_extremePoints hvF
  have hwP := hG.1.2.extremePoints_subset_extremePoints hwG
  have hpath := finitePolytope_edge_connected hP hvP hwP
  have hreach : ∃ H, Facet P H ∧ w ∈ H ∧
      Relation.ReflTransGen (FacetAdjacent P) F H := by
    clear hwG hwP
    induction hpath with
    | refl => exact ⟨F, hF, hvF.1, Relation.ReflTransGen.refl⟩
    | @tail x y _ hxy ih =>
      obtain ⟨H, hH, hxH, hFH⟩ := ih
      obtain ⟨K, hK, hxK, hyK⟩ := edge_mem_facet hP hxy (by omega)
      exact ⟨K, hK, hyK, hFH.trans (hstar hxy.1 hH hK hxH hxK)⟩
  obtain ⟨H, hH, hwH, hFH⟩ := hreach
  exact hFH.trans (hstar hwP hH hG hwH hwG.1)

/-- Induction on dimension connects actual facets through small sections. -/
theorem finitePolytope_facetGraph_connected_aux [FiniteDimensional ℝ E]
    (n : ℕ) {P F G : Set E} (hP : FinitePolytope P)
    (hdim : affineDimension P = n) (hn : 2 ≤ n)
    (hF : Facet P F) (hG : Facet P G) :
    Relation.ReflTransGen (FacetAdjacent P) F G := by
  induction n using Nat.strong_induction_on generalizing P F G with
  | h n ih =>
    apply facetPath_of_connected_vertex_stars hP (by omega) ?_ hF hG
    intro v hv A B hA hB hvA hvB
    by_cases hAB : A = B
    · subst B
      exact Relation.ReflTransGen.refl
    by_cases hn2 : n = 2
    · apply Relation.ReflTransGen.single
      refine ⟨hA, hB, hAB, {v}, (singleton_face_iff_extremePoint P v).mpr hv,
        singleton_nonempty v, ?_, singleton_subset_iff.mpr hvA,
        singleton_subset_iff.mpr hvB⟩
      rw [affineDimension_singleton, hdim, hn2]
    let g := (AffineIsometryEquiv.vaddConst ℝ v).symm
    have hgv : g v = 0 := by simp [g]
    let Q := g '' P
    let A' := g '' A
    let B' := g '' B
    have hQ : FinitePolytope Q := finitePolytope_image g hP
    have hA' : Facet Q A' := facet_image g hA
    have hB' : Facet Q B' := facet_image g hB
    have hAzero : (0 : E) ∈ A' := ⟨v, hvA, hgv⟩
    have hBzero : (0 : E) ∈ B' := ⟨v, hvB, hgv⟩
    have hQzero : (0 : E) ∈ Q.extremePoints ℝ := by
      rw [← affineIsometry_image_extremePoints, ← hgv]
      exact mem_image_of_mem g hv
    have hdQ : affineDimension Q = n := by rw [affineDimension_image]; exact hdim
    let V := vertices Q hQ
    have hV : convexHull ℝ (V : Set E) = Q := convexHull_vertices hQ
    have hzero : (0 : E) ∈ V := (mem_vertices hQ 0).mpr hQzero
    obtain ⟨L, hheight⟩ := finitePolytope_zero_vertex_height hQ hQzero
    have hA'' : Facet (convexHull ℝ (V : Set E)) A' := by rw [hV]; exact hA'
    have hB'' : Facet (convexHull ℝ (V : Set E)) B' := by rw [hV]; exact hB'
    have hdV : affineDimension (convexHull ℝ (V : Set E)) = n := by rw [hV]; exact hdQ
    let S := heightSection (convexHull ℝ (V : Set E)) L
    obtain ⟨hS, hdS⟩ := finiteHull_heightSection_finite_dimension V hzero L hheight (by omega)
    have hAS : Facet S (A' ∩ S) :=
      apexFacet_section_facet V hzero L hheight (by omega) hA'' hAzero
    have hBS : Facet S (B' ∩ S) :=
      apexFacet_section_facet V hzero L hheight (by omega) hB'' hBzero
    change affineDimension S + 1 = _ at hdS
    have hsection := ih (affineDimension S) (by omega) hS rfl (by omega) hAS hBS
    have hlift := facetPath_sectionFaceLift V hzero L hheight (by omega) hsection
    rw [sectionFaceLift_apexFace V hzero L hheight hA''.1 hAzero,
      sectionFaceLift_apexFace V hzero L hheight hB''.1 hBzero, hV] at hlift
    have hback := facetPath_image g.symm hlift
    change Relation.ReflTransGen (FacetAdjacent (g.symm '' (g '' P)))
      (g.symm '' (g '' A)) (g.symm '' (g '' B)) at hback
    simpa only [affineIsometry_symm_image_image] using hback

/-- The actual facet adjacency graph of every finite polytope of dimension
at least two is connected. No graph or fan hypothesis is supplied. -/
theorem finitePolytope_facetGraph_connected [FiniteDimensional ℝ E]
    {P F G : Set E} (hP : FinitePolytope P) (hdim : 2 ≤ affineDimension P)
    (hF : Facet P F) (hG : Facet P G) :
    Relation.ReflTransGen (FacetAdjacent P) F G :=
  finitePolytope_facetGraph_connected_aux (affineDimension P) hP rfl hdim hF hG

/-- The facet graph of every concrete unit uniform five-polytope is connected. -/
theorem UnitUniform5.facets_connected (P : UnitUniform5) {F G : Set (Space 5)}
    (hF : Facet P.val F) (hG : Facet P.val G) :
    Relation.ReflTransGen (FacetAdjacent P.val) F G :=
  finitePolytope_facetGraph_connected (uniform_finitePolytope P.property.1)
    (by rw [uniform_dimension P.property.1]; norm_num) hF hG

end Uniform5.Composition
