import Uniform5.ExposedSection
import Uniform5.Geometry
import Uniform5.PolytopeFaces

/-! Actual facet-section affine spans, centres and distances. -/
noncomputable section
namespace Uniform5
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- For an actual facet, the computed plane is the affine span of its
section, not merely a plane containing one neighbour. -/
theorem facet_section_affineSpan (V : Finset E) {v x c : E} {R S : ℝ}
    (hv : v ∈ V) (hsphere : ∀ y ∈ V, ‖y‖ = R)
    (hunit : ∀ y z, IsEdge V y z → dist y z = 1)
    {K : Set E} (hK : IsExposed ℝ (convexHull ℝ (V : Set E)) K)
    (hvK : v ∈ K) (hxK : x ∈ K) (hxH : x ∈ figureHyperplane v R)
    (hdim : Module.finrank ℝ (affineSpan ℝ K).direction + 1 = Module.finrank ℝ E)
    (hvS : dist v c = S) (hS : S ≠ 0) (hc : c ≠ 0)
    (hplane : ∀ y ∈ K, ⟪y - c, c⟫ = 0) :
    affineSpan ℝ (K ∩ figureHyperplane v R) = facetFigurePlane v c S := by
  classical
  have hsub : affineSpan ℝ (K ∩ figureHyperplane v R) ≤ facetFigurePlane v c S := by
    apply affineSpan_le.mpr
    intro y hy
    rw [facetFigurePlane_eq (hsphere v hv) hvS hS (hplane v hvK)]
    exact ⟨hy.2, hplane y hy.1⟩
  have hdimS := unit_edge_exposedFace_section_finrank V hv hsphere hunit hK hvK
  have hdimP := facetFigurePlane_dimension hc hvS hS (hplane v hvK)
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _
    ((show (K ∩ figureHyperplane v R).Nonempty from ⟨x, hxK, hxH⟩).affineSpan ℝ) hsub
  apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hsub)
  omega

/-- The actual facet-section affine span contains its computed circumcentre
and lies at the stated distance from the full figure centre. -/
theorem facet_section_centre_distance (V : Finset E) {v x c : E} {R S : ℝ}
    (hv : v ∈ V) (hx : x ∈ V) (hsphere : ∀ y ∈ V, ‖y‖ = R) (hR : R ≠ 0)
    (hunit : ∀ y z, IsEdge V y z → dist y z = 1)
    {K : Set E} (hK : IsExposed ℝ (convexHull ℝ (V : Set E)) K)
    (hvK : v ∈ K) (hxK : x ∈ K) (hxv : dist x v = 1)
    (hdim : Module.finrank ℝ (affineSpan ℝ K).direction + 1 = Module.finrank ℝ E)
    (hvS : dist v c = S) (hxS : dist x c = S) (hS : S ≠ 0) (hc : c ≠ 0)
    (hplane : ∀ y ∈ K, ⟪y - c, c⟫ = 0) :
    c + figureCenter (v - c) S ∈ affineSpan ℝ (K ∩ figureHyperplane v R) ∧
    Module.finrank ℝ (affineSpan ℝ (K ∩ figureHyperplane v R)).direction + 2 =
      Module.finrank ℝ E ∧
    Metric.infDist (figureCenter v R) (affineSpan ℝ (K ∩ figureHyperplane v R) : Set E) =
      Real.sqrt ((Real.sqrt (1 - 1 / (4 * R ^ 2))) ^ 2 -
        (Real.sqrt (1 - 1 / (4 * S ^ 2))) ^ 2) := by
  have hspan := facet_section_affineSpan V hv hsphere hunit hK hvK hxK
    ((unit_distance_iff_hyperplane (hsphere x hx) (hsphere v hv)).mp hxv)
    hdim hvS hS hc hplane
  rw [hspan]
  have h := facet_figure_centres_distance (hsphere x hx) (hsphere v hv) hR
    hxS hvS hS hxv (hplane x hxK) (hplane v hvK) hc
  exact ⟨h.2.2.1, h.2.1, h.2.2.2⟩

omit [FiniteDimensional ℝ E] in
/-- A nonzero-radius face through v has a neighbour of v in that face.
The face edge is constructed by nearest-point exposure and lifted to the
whole finite polytope. -/
theorem facet_neighbor_exists (V : Finset E) {v c : E} {R S : ℝ}
    (hv : v ∈ V) (hsphere : ∀ y ∈ V, ‖y‖ = R)
    (hunit : ∀ y z, IsEdge V y z → dist y z = 1)
    {K : Set E} (hK : IsExposed ℝ (convexHull ℝ (V : Set E)) K)
    (hvK : v ∈ K) (hc : c ∈ affineSpan ℝ K)
    (hvS : dist v c = S) (hS : S ≠ 0) :
    ∃ x ∈ V, x ∈ K ∧ dist x v = 1 := by
  classical
  let W := V.filter (fun y => y ∈ K)
  have hW : (W : Set E) = (V : Set E) ∩ K := by ext y; simp [W]
  have hWK : convexHull ℝ (W : Set E) = K := by
    rw [hW]
    exact (exposedFace_eq_convexHull_inter (V : Set E) hK).symm
  have hvW : v ∈ W := by simp [W, hv, hvK]
  have hne : (W.erase v).Nonempty := by
    by_contra hempty
    have hsub : (W : Set E) ⊆ {v} := by
      intro y hy
      by_contra hyv
      exact hempty ⟨y, Finset.mem_erase.mpr ⟨hyv, hy⟩⟩
    have hc' : c ∈ affineSpan ℝ ({v} : Set E) := by
      apply affineSpan_mono ℝ hsub
      rw [← affineSpan_convexHull, hWK]
      exact hc
    have hcv : c = v := by simpa using hc'
    apply hS
    simpa [hcv] using hvS.symm
  obtain ⟨x, hx, hmin⟩ := (W.erase v).exists_min_image (fun y => dist v y) hne
  have hxW := (Finset.mem_erase.mp hx).2
  have hxv := (Finset.mem_erase.mp hx).1
  have hedge : IsEdge W v x := nearest_isEdge W (c := 0) (R := R)
    (by intro y hy; simp [hsphere y (Finset.mem_filter.mp hy).1])
    hvW hxW hxv.symm (by
      intro y hy hyv
      exact hmin y (Finset.mem_erase.mpr ⟨hyv, hy⟩))
  have hedgeV : IsEdge V v x := edge_of_face
    (by rw [hWK]; exact ⟨hK.convex (convex_convexHull ℝ _), hK.isExtreme⟩)
    (by intro y hy; exact (Finset.mem_filter.mp hy).1) hedge
  exact ⟨x, (Finset.mem_filter.mp hxW).1, (Finset.mem_filter.mp hxW).2,
    (dist_comm x v).trans (hunit v x hedgeV)⟩

/-- The facet-section centre and distance from actual facet sphere data.
Projection normal, a section neighbour and nonzero facet normal are derived;
none is an additional geometric input. -/
theorem facet_section_geometry (V : Finset E) {v c : E} {R S : ℝ}
    (hv : v ∈ V) (hsphere : ∀ y ∈ V, ‖y‖ = R) (hR : R ≠ 0)
    (hunit : ∀ y z, IsEdge V y z → dist y z = 1)
    (hzero : (0 : E) ∈ interior (convexHull ℝ (V : Set E)))
    {K : Set E} (hK : IsExposed ℝ (convexHull ℝ (V : Set E)) K)
    (hvK : v ∈ K) (hproper : K ≠ convexHull ℝ (V : Set E))
    (hdim : Module.finrank ℝ (affineSpan ℝ K).direction + 1 = Module.finrank ℝ E)
    (hc : c ∈ affineSpan ℝ K) (hS : S ≠ 0)
    (hfacetSphere : ∀ y ∈ V, y ∈ K → dist y c = S) :
    c + figureCenter (v - c) S ∈ affineSpan ℝ (K ∩ figureHyperplane v R) ∧
    Module.finrank ℝ (affineSpan ℝ (K ∩ figureHyperplane v R)).direction + 2 =
      Module.finrank ℝ E ∧
    Metric.infDist (figureCenter v R) (affineSpan ℝ (K ∩ figureHyperplane v R) : Set E) =
      Real.sqrt ((Real.sqrt (1 - 1 / (4 * R ^ 2))) ^ 2 -
        (Real.sqrt (1 - 1 / (4 * S ^ 2))) ^ 2) := by
  have hspan : affineSpan ℝ ((V : Set E) ∩ K) = affineSpan ℝ K := by
    rw [← affineSpan_convexHull, ← exposedFace_eq_convexHull_inter (V : Set E) hK]
  have horth := circumsphere_centres_orthogonal (c := (0 : E))
    (s := (V : Set E) ∩ K) (hspan.symm ▸ hc)
    (fun y hy => by simpa using hsphere y hy.1)
    (fun y hy => hfacetSphere y hy.1 hy.2)
  have hplane : ∀ y ∈ K, ⟪y - c, c⟫ = 0 := by
    intro y hy
    have h := horth y (hspan.symm ▸ subset_affineSpan ℝ K hy)
    simpa using h
  obtain ⟨L, b, hL, hs, hf, _⟩ := proper_exposed_face_support hK ⟨v, hvK⟩ hproper
  have hc0 : c ≠ 0 := by
    intro heq
    have hlt := strict_support_of_interior L hL hs hzero
    have he := hf c hc
    rw [heq] at he
    exact (ne_of_lt hlt) he
  obtain ⟨x, hx, hxK, hxv⟩ := facet_neighbor_exists V hv hsphere hunit hK hvK hc
    (hfacetSphere v hv hvK) hS
  exact facet_section_centre_distance V hv hx hsphere hR hunit hK hvK hxK hxv hdim
    (hfacetSphere v hv hvK) (hfacetSphere x hx hxK) hS hc0 hplane

/-- Every extreme point of the actual facet section has the computed radius.
This is an inscribed-sphere statement about the section vertices. -/
theorem facet_section_radius (V : Finset E) {v c : E} {R S : ℝ}
    (hv : v ∈ V) (hsphere : ∀ y ∈ V, ‖y‖ = R)
    (hunit : ∀ y z, IsEdge V y z → dist y z = 1)
    {K : Set E} (hK : IsExposed ℝ (convexHull ℝ (V : Set E)) K)
    (hvK : v ∈ K) (hS : S ≠ 0)
    (hfacetSphere : ∀ y ∈ V, y ∈ K → dist y c = S)
    {x : E} (hx : x ∈ (K ∩ figureHyperplane v R).extremePoints ℝ) :
    dist x (c + figureCenter (v - c) S) = Real.sqrt (1 - 1 / (4 * S ^ 2)) := by
  classical
  have hF := exposedFace_inter_section (H := figureHyperplane v R) hK hvK
  rw [unit_edge_section_eq_neighborHull V hv hsphere hunit] at hF
  have heq := exposedFace_eq_convexHull_inter {y | IsEdge V v y} hF
  rw [heq] at hx
  have hxN := extremePoints_convexHull_subset hx
  exact translated_figure_radius (hfacetSphere x hxN.1.2.1 hxN.2.1)
    (hfacetSphere v hv hvK) hS ((dist_comm x v).trans (hunit v x hxN.1))

/-- The facet conclusions of the vertex-figure lemma, expressed for actual
codimension-one faces and their circumcentres. -/
def FacetSectionGeometry (V : Finset E) (v : E) (R : ℝ) : Prop :=
  ∀ (K : Set E) (c : E) (S : ℝ),
    IsConvexFace (convexHull ℝ (V : Set E)) K → v ∈ K →
    K ≠ convexHull ℝ (V : Set E) →
    Module.finrank ℝ (affineSpan ℝ K).direction + 1 = Module.finrank ℝ E →
    c ∈ affineSpan ℝ K → S ≠ 0 →
    (∀ y ∈ V, y ∈ K → dist y c = S) →
    c + figureCenter (v - c) S ∈ affineSpan ℝ (K ∩ figureHyperplane v R) ∧
    Module.finrank ℝ (affineSpan ℝ (K ∩ figureHyperplane v R)).direction + 2 =
      Module.finrank ℝ E ∧
    Metric.infDist (figureCenter v R) (affineSpan ℝ (K ∩ figureHyperplane v R) : Set E) =
      Real.sqrt ((Real.sqrt (1 - 1 / (4 * R ^ 2))) ^ 2 -
        (Real.sqrt (1 - 1 / (4 * S ^ 2))) ^ 2) ∧
    ∀ x ∈ (K ∩ figureHyperplane v R).extremePoints ℝ,
      dist x (c + figureCenter (v - c) S) = Real.sqrt (1 - 1 / (4 * S ^ 2))

theorem unit_edge_facetSectionGeometry (V : Finset E) {v : E} {R : ℝ}
    (hv : v ∈ V) (hsphere : ∀ y ∈ V, ‖y‖ = R) (hR : R ≠ 0)
    (hunit : ∀ y z, IsEdge V y z → dist y z = 1)
    (hzero : (0 : E) ∈ interior (convexHull ℝ (V : Set E))) :
    FacetSectionGeometry V v R := by
  intro K c S hK hvK hp hd hc hS hsp
  have hK := finite_convexFace_isExposed V hK
  obtain ⟨hcen, hdim, hdist⟩ := facet_section_geometry V hv hsphere hR hunit hzero
    hK hvK hp hd hc hS hsp
  exact ⟨hcen, hdim, hdist, fun _ hx => facet_section_radius V hv hsphere hunit hK hvK hS hsp hx⟩

end Uniform5
