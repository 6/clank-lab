import Uniform5.CompositionSection

/-!
# Actual faces through the apex and their affine sections

An actual convex section inherits the intersections with ambient faces.
For finite hulls whose nonzero generators lie on or above the section,
a face containing the apex is determined by its section.
-/

noncomputable section

namespace Uniform5.Composition

open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Intersecting a geometric face with a convex subset produces a geometric
face of that subset. -/
theorem convexFace_inter_section {P F C : Set E} (hF : IsConvexFace P F)
    (hC : Convex ℝ C) (hCP : C ⊆ P) : IsConvexFace C (F ∩ C) := by
  refine ⟨hF.1.inter hC, inter_subset_right, ?_⟩
  intro x hx y hy z hz hseg
  have hxy := hF.2.2 (hCP hx) (hCP hy) hz.1 hseg
  exact ⟨⟨hxy.1, hx⟩, ⟨hxy.2, hy⟩⟩

/-- A face through the origin contains a point on a nonzero initial piece
of a segment exactly when it contains the far endpoint. -/
theorem smul_mem_face_iff {P F : Set E} (hF : IsConvexFace P F)
    (hzero : (0 : E) ∈ F) {x : E} (hx : x ∈ P)
    {t : ℝ} (ht : 0 < t) (htone : t ≤ 1) : t • x ∈ F ↔ x ∈ F := by
  by_cases ht1 : t = 1
  · simp [ht1]
  have htlt : t < 1 := lt_of_le_of_ne htone ht1
  constructor
  · intro htx
    have hseg : t • x ∈ openSegment ℝ (0 : E) x := by
      refine ⟨1 - t, t, sub_pos.mpr htlt, ht, by ring, ?_⟩
      simp
    exact (hF.2.2 (hF.2.1 hzero) hx htx hseg).2
  · intro hxF
    have := hF.1 hzero hxF (sub_nonneg.mpr htone) ht.le (by ring : 1 - t + t = 1)
    simpa only [smul_zero, zero_add] using this

/-- Normalization to height one preserves membership in an apex face. -/
theorem radialPoint_mem_face_iff {P F : Set E} (hF : IsConvexFace P F)
    (hzero : (0 : E) ∈ F) (L : E →L[ℝ] ℝ) {x : E} (hx : x ∈ P)
    (hheight : 1 ≤ L x) : radialPoint L x ∈ F ↔ x ∈ F := by
  have hpos : 0 < L x := lt_of_lt_of_le zero_lt_one hheight
  exact smul_mem_face_iff hF hzero hx (inv_pos.mpr hpos)
    ((inv_le_one₀ hpos).mpr hheight)

/-- The geometric height-one section. -/
noncomputable def heightSection (P : Set E) (L : E →L[ℝ] ℝ) : Set E :=
  {x ∈ P | L x = 1}

theorem heightSection_convex {P : Set E} (hP : Convex ℝ P) (L : E →L[ℝ] ℝ) :
    Convex ℝ (heightSection P L) := by
  apply hP.inter
  exact (convex_singleton (1 : ℝ)).linear_preimage L.toLinearMap

/-- An ambient face cuts out a genuine face of a geometric vertex section. -/
theorem face_heightSection {P F : Set E} (hP : Convex ℝ P)
    (hF : IsConvexFace P F) (L : E →L[ℝ] ℝ) :
    IsConvexFace (heightSection P L) (F ∩ heightSection P L) :=
  convexFace_inter_section hF (heightSection_convex hP L) (fun _ hx => hx.1)

/-- Inclusion of sections reflects inclusion of the apex-containing faces. -/
theorem apexFace_subset_of_section_subset (V : Finset E) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F G : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hG : IsConvexFace (convexHull ℝ (V : Set E)) G)
    (hFzero : (0 : E) ∈ F) (hGzero : (0 : E) ∈ G)
    (hsections : F ∩ heightSection (convexHull ℝ (V : Set E)) L ⊆
      G ∩ heightSection (convexHull ℝ (V : Set E)) L) : F ⊆ G := by
  have hgen : (V : Set E) ∩ F ⊆ G := by
    intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using hGzero
    have hxV : x ∈ V.erase 0 := Finset.mem_erase.mpr ⟨hx0, hx.1⟩
    have hxP := subset_convexHull ℝ (V : Set E) hx.1
    have hradF := (radialPoint_mem_face_iff hF hFzero L hxP (hheight x hxV)).mpr hx.2
    have hradSection : radialPoint L x ∈ heightSection (convexHull ℝ (V : Set E)) L := by
      refine ⟨hF.2.1 hradF, linear_radialPoint L ?_⟩
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hheight x hxV))
    have hradG := (hsections ⟨hradF, hradSection⟩).1
    exact (radialPoint_mem_face_iff hG hGzero L hxP (hheight x hxV)).mp hradG
  rw [face_convexHull_eq hF]
  exact convexHull_min hgen hG.1

/-- Apex-containing faces of a finite hull are uniquely determined by their
height-one sections. The height hypothesis concerns the actual generators,
not an assumed combinatorial correspondence. -/
theorem apexFace_eq_of_section_eq (V : Finset E) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F G : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hG : IsConvexFace (convexHull ℝ (V : Set E)) G)
    (hFzero : (0 : E) ∈ F) (hGzero : (0 : E) ∈ G)
    (hsections : F ∩ heightSection (convexHull ℝ (V : Set E)) L =
      G ∩ heightSection (convexHull ℝ (V : Set E)) L) : F = G :=
  (apexFace_subset_of_section_subset V L hheight hF hG hFzero hGzero hsections.subset).antisymm
    (apexFace_subset_of_section_subset V L hheight hG hF hGzero hFzero hsections.symm.subset)

/-- The geometric section induces an actual order embedding on all faces
containing the apex, including the apex itself and the whole polytope. -/
noncomputable def apexFaceSectionEmbedding (V : Finset E) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x) :
    {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val} ↪o
      GeometricFace (heightSection (convexHull ℝ (V : Set E)) L) where
  toFun F := ⟨F.val.val ∩ heightSection (convexHull ℝ (V : Set E)) L,
    face_heightSection (convex_convexHull ℝ (V : Set E)) F.val.property L⟩
  inj' := by
    intro F G hFG
    apply Subtype.ext
    apply Subtype.ext
    exact apexFace_eq_of_section_eq V L hheight F.val.property G.val.property
      F.property G.property (congrArg Subtype.val hFG)
  map_rel_iff' := by
    intro F G
    constructor
    · intro hFG
      exact apexFace_subset_of_section_subset V L hheight F.val.property G.val.property
        F.property G.property hFG
    · intro hFG
      exact inter_subset_inter_left _ hFG

/-- The section of an actual apex face is the radial hull of precisely the
generators incident to that face. -/
theorem apexFace_section_eq_radialHull (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hFzero : (0 : E) ∈ F) :
    F ∩ heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ ((radialPoint L) ''
        (((V.filter (fun x => x ∈ F)).erase 0 : Finset E) : Set E)) := by
  let W := V.filter (fun x => x ∈ F)
  have hWzero : 0 ∈ W := Finset.mem_filter.mpr ⟨hzero, hFzero⟩
  have hWheight : ∀ x ∈ W.erase 0, 1 ≤ L x := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    exact hheight x (Finset.mem_erase.mpr ⟨hx'.1, (Finset.mem_filter.mp hx'.2).1⟩)
  have hFhull : F = convexHull ℝ (W : Set E) := by
    simpa only [W, Finset.coe_filter] using face_convexHull_eq hF
  have hinter : F ∩ heightSection (convexHull ℝ (V : Set E)) L =
      {x ∈ F | L x = 1} := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, hF.2.1 hx.1, hx.2⟩
  rw [hinter]
  conv_lhs => rw [hFhull]
  exact finiteHull_radial_section W hWzero L hWheight

/-- Radially projecting an actual apex face gives an actual face of the
radial vertex figure. -/
theorem face_radialHull (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hFzero : (0 : E) ∈ F) :
    IsConvexFace (convexHull ℝ ((radialPoint L) '' (V.erase 0 : Set E)))
      (convexHull ℝ ((radialPoint L) ''
        (((V.filter (fun x => x ∈ F)).erase 0 : Finset E) : Set E))) := by
  have hsection : heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ ((radialPoint L) '' (V.erase 0 : Set E)) :=
    finiteHull_radial_section V hzero L hheight
  rw [← hsection, ← apexFace_section_eq_radialHull V hzero L hheight hF hFzero]
  exact face_heightSection (convex_convexHull ℝ (V : Set E)) hF L

end Uniform5.Composition
