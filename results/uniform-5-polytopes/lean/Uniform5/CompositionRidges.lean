import Uniform5.CompositionFigureRanks
import Uniform5.CompositionExposedFaces
import Mathlib.Analysis.Convex.Between

/-!
# One-dimensional sections for the ridge incidence theorem

The extremal-ray count of a pointed planar tangent cone reduces to the
fact that its finite one-dimensional section has exactly two endpoints.
-/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonempty zero-dimensional set consists of one point. -/
theorem nonempty_affineDimension_zero_singleton [FiniteDimensional ℝ E]
    {P : Set E} (hne : P.Nonempty) (hdim : affineDimension P = 0) :
    ∃ a, P = {a} := by
  obtain ⟨a, ha⟩ := hne
  have hdir : (affineSpan ℝ P).direction = ⊥ := Submodule.finrank_eq_zero.mp hdim
  refine ⟨a, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hh := (affineSpan ℝ P).vsub_mem_direction
      (subset_affineSpan ℝ P hx) (subset_affineSpan ℝ P ha)
    rw [hdir] at hh
    exact sub_eq_zero.mp hh
  · exact Set.singleton_subset_iff.mpr ha

/-- Three different collinear points cannot all be actual extreme points. -/
theorem collinear_extreme_triple {P : Set E} {a b c : E}
    (ha : a ∈ P.extremePoints ℝ) (hb : b ∈ P.extremePoints ℝ)
    (hc : c ∈ P.extremePoints ℝ) (hcol : Collinear ℝ ({a, b, c} : Set E)) :
    a = b ∨ a = c ∨ b = c := by
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · obtain hh | hh := (mem_extremePoints_iff_forall_segment.mp hb).2
      a ha.1 c hc.1 h.mem_segment
    · exact Or.inl hh
    · exact Or.inr (Or.inr hh.symm)
  · obtain hh | hh := (mem_extremePoints_iff_forall_segment.mp hc).2
      b hb.1 a ha.1 h.mem_segment
    · exact Or.inr (Or.inr hh)
    · exact Or.inr (Or.inl hh)
  · obtain hh | hh := (mem_extremePoints_iff_forall_segment.mp ha).2
      c hc.1 b hb.1 h.mem_segment
    · exact Or.inr (Or.inl hh.symm)
    · exact Or.inl hh.symm

/-- Every one-dimensional finite polytope has precisely two actual vertices. -/
theorem finitePolytope_dim_one_vertices_card [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hdim : affineDimension P = 1) :
    (vertices P hP).card = 2 := by
  classical
  let V := vertices P hP
  have hcol : Collinear ℝ P := by
    apply collinear_iff_finrank_le_one.mpr
    unfold affineDimension Uniform5.affineDimension at hdim
    rw [direction_affineSpan] at hdim
    exact hdim.le
  have hle : V.card ≤ 2 := by
    by_contra hh
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < V.card)
    have hcol' : Collinear ℝ ({a, b, c} : Set E) := hcol.subset (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ((mem_vertices hP _).mp ha).1
      · exact ((mem_vertices hP _).mp hb).1
      · exact ((mem_vertices hP _).mp hc).1)
    rcases collinear_extreme_triple ((mem_vertices hP a).mp ha)
      ((mem_vertices hP b).mp hb) ((mem_vertices hP c).mp hc) hcol' with hh | hh | hh
    · exact hab hh
    · exact hac hh
    · exact hbc hh
  have hgt : 1 < V.card := by
    by_contra hh
    have hne : 0 < V.card := Finset.card_pos.mpr (vertices_nonempty hP)
    have heq : V.card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp heq
    have hHull := convexHull_vertices hP
    change convexHull ℝ (V : Set E) = P at hHull
    rw [ha] at hHull
    simp only [Finset.coe_singleton, convexHull_singleton] at hHull
    rw [← hHull, affineDimension_singleton] at hdim
    norm_num at hdim
  change V.card = 2
  omega

/-- A one-dimensional finite polytope is the segment joining its two
actual extreme points, rather than a merely collinear generating set. -/
theorem finitePolytope_dim_one_segment [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hdim : affineDimension P = 1) :
    ∃ a b, a ≠ b ∧ P = segment ℝ a b ∧ P.extremePoints ℝ = {a, b} := by
  classical
  obtain ⟨a, b, hab, hvertices⟩ := Finset.card_eq_two.mp
    (finitePolytope_dim_one_vertices_card hP hdim)
  refine ⟨a, b, hab, ?_, ?_⟩
  · rw [finitePolytope_eq_convexHull_extremePoints hP,
      ← coe_vertices P hP, hvertices, Finset.coe_pair, convexHull_pair]
  · rw [← coe_vertices P hP, hvertices, Finset.coe_pair]

/-- A finite one-dimensional polytope has exactly the two endpoint facets. -/
theorem finitePolytope_dim_one_facets [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hdim : affineDimension P = 1) :
    ∃ a b, a ≠ b ∧ ∀ F, Facet P F ↔ F = {a} ∨ F = {b} := by
  obtain ⟨a, b, hab, _, hext⟩ := finitePolytope_dim_one_segment hP hdim
  refine ⟨a, b, hab, ?_⟩
  intro F
  constructor
  · intro hF
    have hdF : affineDimension F = 0 := by have hh := hF.2.2; omega
    obtain ⟨x, rfl⟩ := nonempty_affineDimension_zero_singleton hF.2.1 hdF
    have hx := (singleton_face_iff_extremePoint P x).mp hF.1
    rw [hext] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (congrArg Set.singleton hx)
  · rintro (rfl | rfl)
    · exact ⟨(singleton_face_iff_extremePoint P a).mpr (by rw [hext]; simp),
        Set.singleton_nonempty a, by simp [hdim]⟩
    · exact ⟨(singleton_face_iff_extremePoint P b).mpr (by rw [hext]; simp),
        Set.singleton_nonempty b, by simp [hdim]⟩

/-- Every one-dimensional finite polytope is vertex transitive: the
nontrivial symmetry is reflection in its midpoint. -/
theorem finitePolytope_dim_one_vertexTransitive [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hdim : affineDimension P = 1) :
    VertexTransitive P := by
  classical
  obtain ⟨a, b, _, hseg, hext⟩ := finitePolytope_dim_one_segment hP hdim
  intro v hv w hw
  rw [hext] at hv hw
  have hv' : v ∈ ({a, b} : Finset E) := by simpa using hv
  have hw' : w ∈ ({a, b} : Finset E) := by simpa using hw
  obtain ⟨g, hg, hvw⟩ := vertexTransitive_pair a b v hv' w hw'
  refine ⟨g, ?_, hvw⟩
  rw [hseg, ← convexHull_pair]
  have hHull : g '' convexHull ℝ ({a, b} : Set E) =
      convexHull ℝ (g '' ({a, b} : Set E)) := g.toAffineMap.image_convexHull _
  rw [hHull]
  have hg' : g '' ({a, b} : Set E) = {a, b} := by simpa using hg
  rw [hg']

/-- Every finite polytope of affine dimension at most one is transitive
under actual ambient Euclidean isometries. -/
theorem finitePolytope_low_dimension_vertexTransitive [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hdim : affineDimension P ≤ 1) :
    VertexTransitive P := by
  by_cases hz : affineDimension P = 0
  · obtain ⟨a, rfl⟩ := nonempty_affineDimension_zero_singleton (finitePolytope_nonempty hP) hz
    intro v hv w hw
    simp only [extremePoints_singleton, Set.mem_singleton_iff] at hv hw
    subst v
    subst w
    exact ⟨AffineIsometryEquiv.refl ℝ E, by simp, rfl⟩
  · exact finitePolytope_dim_one_vertexTransitive hP (by omega)

/-- A genuine positive-height section of a nontrivial finite hull is a
finite polytope, and its intrinsic dimension drops by exactly one. -/
theorem finiteHull_heightSection_finite_dimension [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hdim : 0 < affineDimension (convexHull ℝ (V : Set E))) :
    FinitePolytope (heightSection (convexHull ℝ (V : Set E)) L) ∧
      affineDimension (heightSection (convexHull ℝ (V : Set E)) L) + 1 =
        affineDimension (convexHull ℝ (V : Set E)) := by
  classical
  have hne : (V.erase 0).Nonempty := by
    by_contra hh
    have he : V.erase 0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    have hV : V = {0} := by simpa only [he, Finset.insert_empty] using (Finset.insert_erase hzero).symm
    simp only [hV, Finset.coe_singleton, convexHull_singleton, affineDimension_singleton] at hdim
    omega
  have hsection : heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ ((radialPoint L) '' (V.erase 0 : Set E)) :=
    finiteHull_radial_section V hzero L hheight
  constructor
  · refine ⟨(V.erase 0).image (radialPoint L), hne.image _, ?_⟩
    simpa only [Finset.coe_image] using hsection
  · rw [hsection]
    exact finiteHull_radialHull_dimension_intrinsic V hzero L.toLinearMap
      (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one (hheight x hx))) hne

/-- The decisive planar-cone incidence fact: a two-dimensional finite hull
at a strict zero apex has exactly two incident facets. Its transverse
section is a segment, and its endpoint faces lift to the two facets. -/
theorem finiteHull_dim_two_apex_facets [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hdim : affineDimension (convexHull ℝ (V : Set E)) = 2) :
    ∃ F G : Set E, F ≠ G ∧ ∀ H,
      (Facet (convexHull ℝ (V : Set E)) H ∧ (0 : E) ∈ H) ↔ H = F ∨ H = G := by
  let P := convexHull ℝ (V : Set E)
  let S := heightSection P L
  have hzeroP : (0 : E) ∈ P := subset_convexHull ℝ (V : Set E) hzero
  obtain ⟨hS, hdS⟩ := finiteHull_heightSection_finite_dimension V hzero L hheight (by omega)
  have hdS' : affineDimension S = 1 := by change affineDimension S + 1 = _ at hdS; omega
  obtain ⟨a, b, hab, hfacets⟩ := finitePolytope_dim_one_facets hS hdS'
  have ha : Facet S {a} := (hfacets {a}).mpr (Or.inl rfl)
  have hb : Facet S {b} := (hfacets {b}).mpr (Or.inr rfl)
  let F := sectionFaceLift P L {a}
  let G := sectionFaceLift P L {b}
  have hF : Facet P F := sectionFacet_lift_facet V hzero L hheight ha
  have hG : Facet P G := sectionFacet_lift_facet V hzero L hheight hb
  have hFzero : (0 : E) ∈ F := ⟨hzeroP, Or.inl rfl⟩
  have hGzero : (0 : E) ∈ G := ⟨hzeroP, Or.inl rfl⟩
  have hFS : F ∩ S = {a} := sectionFaceLift_section L ha.1.2.1
  have hGS : G ∩ S = {b} := sectionFaceLift_section L hb.1.2.1
  refine ⟨F, G, ?_, ?_⟩
  · intro hFG
    have hh : ({a} : Set E) = {b} := by rw [← hFS, ← hGS, hFG]
    exact hab (Set.singleton_injective hh)
  · intro H
    constructor
    · rintro ⟨hH, hHzero⟩
      have hHS := apexFacet_section_facet V hzero L hheight (by omega) hH hHzero
      rcases (hfacets (H ∩ S)).mp hHS with hh | hh
      · exact Or.inl (apexFace_eq_of_section_eq V L hheight hH.1 hF.1 hHzero hFzero
          (hh.trans hFS.symm))
      · exact Or.inr (apexFace_eq_of_section_eq V L hheight hH.1 hG.1 hHzero hGzero
          (hh.trans hGS.symm))
    · rintro (rfl | rfl)
      · exact ⟨hF, hFzero⟩
      · exact ⟨hG, hGzero⟩

end Uniform5.Composition
