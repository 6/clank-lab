import Uniform5.CompositionSimpleGlobal

/-!
# The actual geometric facet system and its Case B laws
-/

noncomputable section
namespace Uniform5.Composition
open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonempty finite hull needs at least affine dimension plus one generators. -/
theorem finiteHull_dimension_add_one_le_card (V : Finset E) (hne : V.Nonempty) :
    affineDimension (convexHull ℝ (V : Set E)) + 1 ≤ V.card := by
  letI : Nonempty V := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hd := finrank_vectorSpan_range_add_one_le ℝ ((↑) : V → E)
  have hrange : Set.range ((↑) : V → E) = (V : Set E) := by ext x; simp
  rw [hrange, Fintype.card_coe] at hd
  rw [affineDimension, Uniform5.affineDimension, affineSpan_convexHull (𝕜 := ℝ), direction_affineSpan]
  exact hd

/-- A positive-dimensional finite hull has a nonempty height-one section
of intrinsic codimension one. -/
theorem finiteHull_heightSection_dimension [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hpos : 0 < affineDimension (convexHull ℝ (V : Set E))) :
    (heightSection (convexHull ℝ (V : Set E)) L).Nonempty ∧
      affineDimension (heightSection (convexHull ℝ (V : Set E)) L) + 1 =
        affineDimension (convexHull ℝ (V : Set E)) := by
  have hne : (V.erase 0).Nonempty := by
    by_contra hn
    have hsub : convexHull ℝ (V : Set E) ⊆ {0} := by
      apply convexHull_min _ (convex_singleton 0)
      intro x hx
      by_contra hx0
      exact hn ⟨x, Finset.mem_erase.mpr ⟨hx0, hx⟩⟩
    have heq : convexHull ℝ (V : Set E) = {0} := hsub.antisymm
      (singleton_subset_iff.mpr (subset_convexHull ℝ (V : Set E) hzero))
    rw [heq, affineDimension_singleton] at hpos
    omega
  have hs : heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ ((fun x => (L x)⁻¹ • x) '' (V.erase 0 : Set E)) :=
    finiteHull_radial_section V hzero L hheight
  have hL : ∀ x ∈ V.erase 0, L x ≠ 0 :=
    fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one (hheight x hx))
  constructor
  · rw [hs]
    exact ((show (V.erase 0 : Set E).Nonempty from hne).image _).convexHull
  · rw [hs]
    exact finiteHull_radialHull_dimension_intrinsic V hzero L.toLinearMap hL hne

/-- A unit-uniform polytope has at least its intrinsic dimension many
actual neighbors at each vertex. -/
theorem unitUniform_neighbour_card_lower [FiniteDimensional ℝ E] {n : ℕ}
    {P : Set E} (hP : UnitUniform (n + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ) :
    n + 3 ≤ (geometricNeighbours P (uniform_finitePolytope hP.1) v).card := by
  have zero_case {Q : Set E} (hQ : UnitUniform (n + 3) Q)
      (hz : (0 : E) ∈ Q.extremePoints ℝ) :
      n + 3 ≤ (geometricNeighbours Q (uniform_finitePolytope hQ.1) 0).card := by
    obtain ⟨c, R, _, hs⟩ := uniform_cospherical_pos hQ.1
    let V := vertices Q (uniform_finitePolytope hQ.1)
    have hVzero : (0 : E) ∈ V := (mem_vertices _ 0).mpr hz
    have hh := cosphericalUnit_simpleVertex_heights V hVzero c R
      (fun x hx => hs x ((mem_vertices _ x).mp hx))
      (fun x y hxy => hQ.2 x y ((edge_iff_vertices_isEdge _ x y).mpr hxy))
    have hdim : affineDimension (convexHull ℝ (V : Set E)) = n + 3 := by
      simpa only [V, convexHull_vertices] using uniform_dimension hQ.1
    have hd := finiteHull_heightSection_dimension V hVzero (sphereHeight c) hh.1 (by omega)
    have heq : heightSection (convexHull ℝ (V : Set E)) (sphereHeight c) =
        convexHull ℝ (zeroNeighbors V : Set E) := by
      rw [coe_zeroNeighbors]
      exact finiteHull_section_eq_convexHull_edges V hVzero
        (fun x hx => by simpa only [V, convexHull_vertices] using (mem_vertices _ x).mp hx)
        (sphereHeight c) hh.1 hh.2
    rw [heq, hdim] at hd
    have hNne : (zeroNeighbors V).Nonempty := (convexHull_nonempty_iff (𝕜 := ℝ)).mp hd.1
    have hcard := finiteHull_dimension_add_one_le_card (zeroNeighbors V) hNne
    rw [geometricNeighbours_zero]
    rw [hd.2] at hcard
    exact hcard
  let g := AffineIsometryEquiv.constVAdd ℝ E (-v)
  have hgv : g v = 0 := by simp [g]
  have hz : (0 : E) ∈ (g '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints, ← hgv]
    exact mem_image_of_mem g hv
  have hc := zero_case (unitUniform_image g hP) hz
  rw [← hgv, geometricNeighbours_image, Finset.card_image_of_injective _ g.injective] at hc
  exact hc

/-- The Case B incidence system on actual extreme points and actual facets. -/
noncomputable def actualFacetSystem (P : Set E) (hP : FinitePolytope P) :
    CaseB.FacetSystem (vertices P hP) {F : Set E // Facet P F} where
  edge v w := Edge P v w
  edge_symm := by
    intro v w h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, by simpa only [segment_symm] using h.2.2.2⟩
  edge_irrefl v h := h.2.2.1 rfl
  vertices F := Finset.univ.filter (fun v : vertices P hP => (v : E) ∈ F.val)

@[simp] theorem mem_actualFacetSystem_vertices (P : Set E) (hP : FinitePolytope P)
    (F : {F : Set E // Facet P F}) (v : vertices P hP) :
    v ∈ (actualFacetSystem P hP).vertices F ↔ (v : E) ∈ F.val := by
  simp [actualFacetSystem]

/-- The neighbor-label inclusion into actual polytope vertex labels. -/
noncomputable def neighbourVertexEmbedding (P : Set E) (hP : FinitePolytope P) (v : E) :
    geometricNeighbours P hP v ↪ vertices P hP where
  toFun w := ⟨w.val, (mem_vertices hP w.val).mpr
    ((mem_geometricNeighbours P hP v w.val).mp w.property).2.1⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun w : vertices P hP => (w : E)) h

/-- Graph neighbors in the incidence system are precisely geometric neighbors. -/
theorem actualFacetSystem_neighbours (P : Set E) (hP : FinitePolytope P)
    (v : vertices P hP) :
    (actualFacetSystem P hP).neighbours v =
      Finset.univ.map (neighbourVertexEmbedding P hP v) := by
  ext w
  rw [CaseB.FacetSystem.mem_neighbours, Finset.mem_map]
  constructor
  · intro he
    exact ⟨⟨w.val, (mem_geometricNeighbours P hP v w.val).mpr he⟩,
      Finset.mem_univ _, Subtype.ext rfl⟩
  · rintro ⟨x, _, hx⟩
    have he := (mem_geometricNeighbours P hP v x.val).mp x.property
    have heq : (x : E) = w.val := congrArg Subtype.val hx
    change Edge P (v : E) (w : E)
    exact heq ▸ he

theorem actualFacetSystem_neighbours_card (P : Set E) (hP : FinitePolytope P)
    (v : vertices P hP) :
    ((actualFacetSystem P hP).neighbours v).card = (geometricNeighbours P hP v).card := by
  rw [actualFacetSystem_neighbours, Finset.card_map, Finset.card_univ, Fintype.card_coe]

/-- Facet-neighbor incidence is the literal geometric face incidence. -/
theorem actualFacetSystem_facetNeighbours (P : Set E) (hP : FinitePolytope P)
    (F : {F : Set E // Facet P F}) (v : vertices P hP) (hv : (v : E) ∈ F.val) :
    (actualFacetSystem P hP).facetNeighbours F v =
      (neighboursIn P hP v ⟨⟨F.val, F.property.1⟩, hv⟩).map
        (neighbourVertexEmbedding P hP v) := by
  ext w
  rw [CaseB.FacetSystem.mem_facetNeighbours, mem_actualFacetSystem_vertices, Finset.mem_map]
  constructor
  · rintro ⟨he, hwF⟩
    refine ⟨⟨w.val, (mem_geometricNeighbours P hP v w.val).mpr he⟩, ?_, Subtype.ext rfl⟩
    exact (mem_neighboursIn P hP v _ _).mpr hwF
  · rintro ⟨x, hx, hxw⟩
    have he := (mem_geometricNeighbours P hP v x.val).mp x.property
    have hxF := (mem_neighboursIn P hP v _ x).mp hx
    have hval : (x : E) = w.val := congrArg Subtype.val hxw
    refine ⟨?_, hval ▸ hxF⟩
    change Edge P (v : E) (w : E)
    exact hval ▸ he

/-- Within a geometric facet, the induced graph is its actual edge graph. -/
theorem actualFacetSystem_facetNeighbours_image [FiniteDimensional ℝ E]
    (P : Set E) (hP : FinitePolytope P) (F : {F : Set E // Facet P F})
    (v : vertices P hP) (hv : (v : E) ∈ F.val) :
    ((actualFacetSystem P hP).facetNeighbours F v).image (fun w : vertices P hP => (w : E)) =
      geometricNeighbours F.val (finitePolytope_facet hP F.property) v := by
  ext w
  rw [Finset.mem_image, mem_geometricNeighbours]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hh := (CaseB.FacetSystem.mem_facetNeighbours (actualFacetSystem P hP)).mp hx
    have hxF := (mem_actualFacetSystem_vertices P hP F x).mp hh.2
    exact (edge_face_iff hP F.property.1 hv hxF).mp hh.1
  · intro he
    have hwP := F.property.1.2.extremePoints_subset_extremePoints he.2.1
    let x : vertices P hP := ⟨w, (mem_vertices hP w).mpr hwP⟩
    refine ⟨x, ?_, rfl⟩
    apply (CaseB.FacetSystem.mem_facetNeighbours (actualFacetSystem P hP)).mpr
    exact ⟨(edge_face_iff hP F.property.1 hv he.2.1.1).mpr he,
      (mem_actualFacetSystem_vertices P hP F x).mpr he.2.1.1⟩

/-- The three generic Case B incidence laws hold for the actual vertices
and facets of every unit-uniform four-polytope. All geometric prerequisites
are derived, including minimum facet degree and the unique-three principle. -/
theorem actualFacetSystem_laws [FiniteDimensional ℝ E]
    {P : Set E} (hP : UnitUniform 4 P) :
    (actualFacetSystem P (uniform_finitePolytope hP.1)).Laws := by
  let hpoly := uniform_finitePolytope hP.1
  constructor
  · intro F v hv
    have hvF := (mem_actualFacetSystem_vertices P hpoly F v).mp hv
    have hFu : UnitUniform 3 F.val := unitUniform_facet hP F.property
    have hvext : (v : E) ∈ F.val.extremePoints ℝ := by
      rw [face_extremePoints_eq F.property.1]
      exact ⟨hvF, (mem_vertices hpoly v).mp v.property⟩
    have hc := congrArg Finset.card (actualFacetSystem_facetNeighbours_image P hpoly F v hvF)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
    rw [hc]
    exact unitUniform_neighbour_card_lower hFu hvext
  · intro F v hv hfour
    have hvF := (mem_actualFacetSystem_vertices P hpoly F v).mp hv
    have hfour' : (geometricNeighbours P hpoly v).card = 4 := by
      rwa [actualFacetSystem_neighbours_card] at hfour
    have hf := (unitUniform4_simpleVertex_facet_iff_three hP
      ((mem_vertices hpoly v).mp v.property) hfour'
      ⟨⟨F.val, F.property.1⟩, hvF⟩).mp F.property
    rw [actualFacetSystem_facetNeighbours P hpoly F v hvF, Finset.card_map]
    exact hf
  · intro v hfour s hs hthree
    have hfour' : (geometricNeighbours P hpoly v).card = 4 := by
      rwa [actualFacetSystem_neighbours_card] at hfour
    let e := neighbourVertexEmbedding P hpoly (v : E)
    let t : Finset (geometricNeighbours P hpoly v) := Finset.univ.filter (fun w => e w ∈ s)
    have hmap : t.map e = s := by
      ext w
      rw [Finset.mem_map]
      constructor
      · rintro ⟨x, hx, hxw⟩
        have hx' : e x ∈ s := (Finset.mem_filter.mp hx).2
        exact hxw ▸ hx'
      · intro hw
        have hneigh := hs hw
        rw [actualFacetSystem_neighbours, Finset.mem_map] at hneigh
        obtain ⟨x, _, hxw⟩ := hneigh
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxw.symm ▸ hw⟩, hxw⟩
    have hcardt : t.card = 3 := by
      have hc := congrArg Finset.card hmap
      rw [Finset.card_map, hthree] at hc
      exact hc
    obtain ⟨F, ⟨hF, hinc⟩, _⟩ := unitUniform4_simpleVertex_unique_facet hP
      ((mem_vertices hpoly v).mp v.property) hfour' t hcardt
    let f : {F : Set E // Facet P F} := ⟨F.val.val, hF⟩
    refine ⟨f, (mem_actualFacetSystem_vertices P hpoly f v).mpr F.property, ?_⟩
    rw [actualFacetSystem_facetNeighbours P hpoly f v F.property]
    change (neighboursIn P hpoly v F).map e = s
    rw [hinc, hmap]

end Uniform5.Composition
