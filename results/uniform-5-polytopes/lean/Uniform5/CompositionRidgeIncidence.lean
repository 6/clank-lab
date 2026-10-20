import Uniform5.CompositionRidges
import Uniform5.CompositionSymmetry

/-!
# Exactly two facets through a geometric ridge

Strict vertex support provides genuine small sections. Repeated sections
reduce ridge incidence to the proved two-dimensional apex case.
-/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An actual vertex admits a separating functional normalized so every
other actual vertex has height at least one. -/
theorem finitePolytope_zero_vertex_height {P : Set E} (hP : FinitePolytope P)
    (hzero : (0 : E) ∈ P.extremePoints ℝ) :
    ∃ L : E →L[ℝ] ℝ, ∀ x ∈ (vertices P hP).erase 0, 1 ≤ L x := by
  let V := vertices P hP
  have hz : (0 : E) ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ := by
    simpa only [V, convexHull_vertices] using hzero
  obtain ⟨M, hM⟩ := finite_extreme_strict_support V hz
  have hpos (x : E) (hx : x ∈ V.erase 0) : 0 < (-M) x := by
    have hh := hM x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1
    simpa only [map_zero, ContinuousLinearMap.neg_apply, neg_pos] using hh
  by_cases hne : (V.erase 0).Nonempty
  · obtain ⟨a, ha, hmin⟩ := (V.erase 0).exists_min_image (fun x => (-M) x) hne
    refine ⟨((-M) a)⁻¹ • (-M), ?_⟩
    intro x hx
    change 1 ≤ ((-M) a)⁻¹ * (-M) x
    rw [mul_comm, ← div_eq_mul_inv]
    exact (one_le_div (hpos a ha)).mpr (hmin x hx)
  · exact ⟨0, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

/-- Exactly two distinct actual facets contain the specified face. -/
noncomputable def TwoContainingFacets (P R : Set E) : Prop :=
  ∃ F G : Set E, F ≠ G ∧ ∀ H, (Facet P H ∧ R ⊆ H) ↔ H = F ∨ H = G

theorem twoContainingFacets_image (g : E ≃ᵃⁱ[ℝ] E) {P R : Set E}
    (h : TwoContainingFacets P R) : TwoContainingFacets (g '' P) (g '' R) := by
  obtain ⟨F, G, hFG, hfacets⟩ := h
  refine ⟨g '' F, g '' G, fun hh => hFG (g.injective.image_injective hh), ?_⟩
  intro H
  constructor
  · rintro ⟨hH, hRH⟩
    have hpre : Facet P (g.symm '' H) := by
      simpa only [affineIsometry_symm_image_image] using facet_image g.symm hH
    have hRpre : R ⊆ g.symm '' H := by
      intro x hx
      exact ⟨g x, hRH (mem_image_of_mem g hx), g.symm_apply_apply x⟩
    rcases (hfacets (g.symm '' H)).mp ⟨hpre, hRpre⟩ with hh | hh
    · left
      rw [← hh, affineIsometry_image_symm_image]
    · right
      rw [← hh, affineIsometry_image_symm_image]
  · rintro (rfl | rfl)
    · have hh := (hfacets F).mpr (Or.inl rfl)
      exact ⟨facet_image g hh.1, Set.image_mono hh.2⟩
    · have hh := (hfacets G).mpr (Or.inr rfl)
      exact ⟨facet_image g hh.1, Set.image_mono hh.2⟩

theorem twoContainingFacets_image_iff (g : E ≃ᵃⁱ[ℝ] E) (P R : Set E) :
    TwoContainingFacets (g '' P) (g '' R) ↔ TwoContainingFacets P R :=
  ⟨fun h => by simpa only [affineIsometry_symm_image_image] using twoContainingFacets_image g.symm h,
    twoContainingFacets_image g⟩

/-- Facet incidence above a nontrivial apex face is preserved by a genuine
small section. This is a consequence of the geometric face correspondence. -/
theorem twoContainingFacets_of_heightSection [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hdim : 2 ≤ affineDimension (convexHull ℝ (V : Set E)))
    {R : Set E} (hR : IsConvexFace (convexHull ℝ (V : Set E)) R)
    (hzR : (0 : E) ∈ R)
    (h : TwoContainingFacets (heightSection (convexHull ℝ (V : Set E)) L)
      (R ∩ heightSection (convexHull ℝ (V : Set E)) L)) :
    TwoContainingFacets (convexHull ℝ (V : Set E)) R := by
  let P := convexHull ℝ (V : Set E)
  let S := heightSection P L
  obtain ⟨A, B, hAB, hfacets⟩ := h
  have hA := (hfacets A).mpr (Or.inl rfl)
  have hB := (hfacets B).mpr (Or.inr rfl)
  let F := sectionFaceLift P L A
  let G := sectionFaceLift P L B
  have hF : Facet P F := sectionFacet_lift_facet V hzero L hheight hA.1
  have hG : Facet P G := sectionFacet_lift_facet V hzero L hheight hB.1
  have hFzero : (0 : E) ∈ F := ⟨subset_convexHull ℝ (V : Set E) hzero, Or.inl rfl⟩
  have hGzero : (0 : E) ∈ G := ⟨subset_convexHull ℝ (V : Set E) hzero, Or.inl rfl⟩
  have hFS : F ∩ S = A := sectionFaceLift_section L hA.1.1.2.1
  have hGS : G ∩ S = B := sectionFaceLift_section L hB.1.1.2.1
  have hRF : R ⊆ F := apexFace_subset_of_section_subset V L hheight hR hF.1 hzR hFzero
    (by rw [hFS]; exact hA.2)
  have hRG : R ⊆ G := apexFace_subset_of_section_subset V L hheight hR hG.1 hzR hGzero
    (by rw [hGS]; exact hB.2)
  refine ⟨F, G, ?_, ?_⟩
  · intro heq
    exact hAB (by rw [← hFS, ← hGS, heq])
  · intro H
    constructor
    · rintro ⟨hH, hRH⟩
      have hHzero := hRH hzR
      have hHS := apexFacet_section_facet V hzero L hheight hdim hH hHzero
      have hRHS : R ∩ S ⊆ H ∩ S := inter_subset_inter_left S hRH
      rcases (hfacets (H ∩ S)).mp ⟨hHS, hRHS⟩ with hh | hh
      · exact Or.inl (apexFace_eq_of_section_eq V L hheight hH.1 hF.1 hHzero hFzero
          (hh.trans hFS.symm))
      · exact Or.inr (apexFace_eq_of_section_eq V L hheight hH.1 hG.1 hHzero hGzero
          (hh.trans hGS.symm))
    · rintro (rfl | rfl)
      · exact ⟨hF, hRF⟩
      · exact ⟨hG, hRG⟩

/-- Repeated genuine vertex sections reduce ridge incidence to the
one-dimensional section of a planar tangent cone. -/
theorem finitePolytope_ridge_two_facets_aux [FiniteDimensional ℝ E]
    (n : ℕ) {P R : Set E} (hP : FinitePolytope P) (hR : IsConvexFace P R)
    (hne : R.Nonempty) (hRdim : affineDimension R = n)
    (hPdim : affineDimension P = n + 2) : TwoContainingFacets P R := by
  induction n using Nat.strong_induction_on generalizing P R with
  | h n ih =>
    have hRfinite := finitePolytope_face hP hR hne
    obtain ⟨v, hvR⟩ := finitePolytope_extremePoints_nonempty hRfinite
    have hvP := hR.2.extremePoints_subset_extremePoints hvR
    let g := (AffineIsometryEquiv.vaddConst ℝ v).symm
    have hgv : g v = 0 := by simp [g]
    let Q := g '' P
    let T := g '' R
    have hQ : FinitePolytope Q := finitePolytope_image g hP
    have hT : IsConvexFace Q T := isConvexFace_image g hR
    have hTzero : (0 : E) ∈ T := ⟨v, hvR.1, hgv⟩
    have hQzero : (0 : E) ∈ Q.extremePoints ℝ := by
      rw [← affineIsometry_image_extremePoints, ← hgv]
      exact mem_image_of_mem g hvP
    have hdQ : affineDimension Q = n + 2 := by rw [affineDimension_image]; exact hPdim
    have hdT : affineDimension T = n := by rw [affineDimension_image]; exact hRdim
    apply (twoContainingFacets_image_iff g P R).mp
    change TwoContainingFacets Q T
    let V := vertices Q hQ
    have hV : convexHull ℝ (V : Set E) = Q := convexHull_vertices hQ
    have hzero : (0 : E) ∈ V := (mem_vertices hQ 0).mpr hQzero
    obtain ⟨L, hheight⟩ := finitePolytope_zero_vertex_height hQ hQzero
    have hT' : IsConvexFace (convexHull ℝ (V : Set E)) T := by rw [hV]; exact hT
    have hdV : affineDimension (convexHull ℝ (V : Set E)) = n + 2 := by rw [hV]; exact hdQ
    rcases n with _ | k
    · obtain ⟨a, hTa⟩ := nonempty_affineDimension_zero_singleton ⟨0, hTzero⟩ hdT
      have ha : (0 : E) = a := by simpa only [hTa, Set.mem_singleton_iff] using hTzero
      have hT0 : T = {0} := by rw [hTa, ← ha]
      obtain ⟨F, G, hFG, hfacets⟩ := finiteHull_dim_two_apex_facets V hzero L hheight hdV
      refine ⟨F, G, hFG, ?_⟩
      intro H
      rw [hT0, Set.singleton_subset_iff]
      simpa only [hV] using hfacets H
    · let S := heightSection (convexHull ℝ (V : Set E)) L
      have hTnot : T ≠ {0} := by
        intro hh
        rw [hh, affineDimension_singleton] at hdT
        omega
      obtain ⟨hS, hdS⟩ := finiteHull_heightSection_finite_dimension V hzero L hheight (by omega)
      have hTS : IsConvexFace S (T ∩ S) :=
        face_heightSection (convex_convexHull ℝ (V : Set E)) hT' L
      have hTSne : (T ∩ S).Nonempty :=
        (apexFace_section_nonempty_iff V L hheight hT' hTzero).mpr hTnot
      have hdTS := apexFace_section_dimension V hzero L hheight hT' hTzero hTnot
      have hdTS' : affineDimension (T ∩ S) = k := by
        change affineDimension (T ∩ S) + 1 = _ at hdTS
        omega
      have hdS' : affineDimension S = k + 2 := by
        change affineDimension S + 1 = _ at hdS
        omega
      have htwosection := ih k (by omega) hS hTS hTSne hdTS' hdS'
      rw [← hV]
      exact twoContainingFacets_of_heightSection V hzero L hheight (by omega)
        hT' hTzero htwosection

/-- Every nonempty actual codimension-two face of a finite polytope lies
in exactly two distinct actual codimension-one facets. No incidence,
quotient-cone, fan, or connectivity premise is supplied. -/
theorem finitePolytope_ridge_two_facets [FiniteDimensional ℝ E]
    {P R : Set E} (hP : FinitePolytope P) (hR : IsConvexFace P R)
    (hne : R.Nonempty) (hcodim : affineDimension R + 2 = affineDimension P) :
    ∃ F G : Set E, F ≠ G ∧ ∀ H, (Facet P H ∧ R ⊆ H) ↔ H = F ∨ H = G :=
  finitePolytope_ridge_two_facets_aux (affineDimension R) hP hR hne rfl hcodim.symm

end Uniform5.Composition
