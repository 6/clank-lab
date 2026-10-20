import Uniform5.CompositionFigureLift
import Uniform5.CompositionDimension

/-!
# Intrinsic dimensions in the geometric face correspondence

The dimension drop is relative to the original affine span, so the same
statement applies to every nontrivial face through the apex.
-/

noncomputable section
namespace Uniform5.Composition
open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonempty set at height one has affine dimension one less than its
own linear span, with no full-dimensionality hypothesis. -/
theorem affineDimension_add_one_eq_finrank_span [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] ℝ) (S : Set E) (hne : S.Nonempty)
    (hlevel : ∀ x ∈ S, L x = 1) :
    affineDimension S + 1 = Module.finrank ℝ (Submodule.span ℝ S) := by
  have hle : vectorSpan ℝ S ≤ Submodule.span ℝ S := by
    rw [← vectorSpan_insert_zero_eq_span]
    exact vectorSpan_mono ℝ (subset_insert 0 S)
  have hstrict : vectorSpan ℝ S < Submodule.span ℝ S := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    obtain ⟨a, ha⟩ := hne
    have haSpan : a ∈ vectorSpan ℝ S := heq.symm ▸ Submodule.subset_span ha
    have haZero := vectorSpan_le_ker_of_level L S 1 hlevel haSpan
    change L a = 0 at haZero
    rw [hlevel a ha] at haZero
    norm_num at haZero
  have hupper := Submodule.finrank_lt_finrank_of_lt hstrict
  have hlower := finrank_vectorSpan_insert_le_set ℝ S (0 : E)
  rw [vectorSpan_insert_zero_eq_span] at hlower
  rw [affineDimension, Uniform5.affineDimension, direction_affineSpan]
  omega

/-- Nonzero pointwise normalization preserves the original linear span;
the normalized hull has one lower affine dimension intrinsically. -/
theorem affineDimension_radialHull_add_one_eq_finrank_span [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] ℝ) (S : Set E) (hne : S.Nonempty)
    (hL : ∀ x ∈ S, L x ≠ 0) :
    affineDimension (convexHull ℝ ((fun x => (L x)⁻¹ • x) '' S)) + 1 =
      Module.finrank ℝ (Submodule.span ℝ S) := by
  have hsp := span_image_pointwise_smul S (fun x => (L x)⁻¹)
    (fun x hx => inv_ne_zero (hL x hx))
  have hlev : ∀ y ∈ ((fun x => (L x)⁻¹ • x) '' S), L y = 1 := by
    rintro y ⟨x, hx, rfl⟩
    simp [hL x hx]
  have hd := affineDimension_add_one_eq_finrank_span L _ (hne.image _) hlev
  rw [hsp] at hd
  unfold affineDimension Uniform5.affineDimension at *
  rw [affineSpan_convexHull (𝕜 := ℝ)]
  exact hd

/-- A nontrivial finite hull at a zero apex loses exactly one affine
dimension in its radial section, including in a larger ambient space. -/
theorem finiteHull_radialHull_dimension_intrinsic [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ V.erase 0, L x ≠ 0) (hne : (V.erase 0).Nonempty) :
    affineDimension (convexHull ℝ ((fun x => (L x)⁻¹ • x) '' (V.erase 0 : Set E))) + 1 =
      affineDimension (convexHull ℝ (V : Set E)) := by
  rw [affineDimension_radialHull_add_one_eq_finrank_span L (V.erase 0 : Set E) hne hL]
  unfold affineDimension Uniform5.affineDimension
  rw [direction_finiteHull_zero V hzero]

/-- A nontrivial apex face contains a nonzero original generator. -/
theorem apexFace_generators_nonzero (V : Finset E) {F : Set E}
    (hF : IsConvexFace (convexHull ℝ (V : Set E)) F) (hzero : (0 : E) ∈ F)
    (hne : F ≠ {0}) : ((V.filter (fun x => x ∈ F)).erase 0).Nonempty := by
  by_contra hn
  apply hne
  apply Set.Subset.antisymm
  · rw [face_convexHull_eq hF]
    apply convexHull_min _ (convex_singleton 0)
    intro x hx
    by_cases hx0 : x = 0
    · exact hx0
    exact False.elim (hn ⟨x, Finset.mem_erase.mpr
      ⟨hx0, Finset.mem_filter.mpr ⟨hx.1, hx.2⟩⟩⟩)
  · exact singleton_subset_iff.mpr hzero

/-- The only apex face with empty vertex section is the apex singleton. -/
theorem apexFace_section_nonempty_iff (V : Finset E) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hzero : (0 : E) ∈ F) :
    (F ∩ heightSection (convexHull ℝ (V : Set E)) L).Nonempty ↔ F ≠ {0} := by
  constructor
  · rintro ⟨x, hxF, hxC⟩ heq
    have hx0 : x = 0 := by simpa [heq] using hxF
    have := hxC.2
    simp [hx0] at this
  · intro hne
    obtain ⟨x, hx⟩ := apexFace_generators_nonzero V hF hzero hne
    have hxne := (Finset.mem_erase.mp hx).1
    have hxF := Finset.mem_filter.mp (Finset.mem_erase.mp hx).2
    have hxV : x ∈ V.erase 0 := Finset.mem_erase.mpr ⟨hxne, hxF.1⟩
    have hrad := (radialPoint_mem_face_iff hF hzero L
      (subset_convexHull ℝ (V : Set E) hxF.1) (hheight x hxV)).mpr hxF.2
    exact ⟨radialPoint L x, hrad, hF.2.1 hrad,
      linear_radialPoint L (ne_of_gt (lt_of_lt_of_le zero_lt_one (hheight x hxV)))⟩

/-- Every nontrivial actual apex face loses exactly one affine dimension in
its geometric vertex section. This supplies the paper's face rank shift. -/
theorem apexFace_section_dimension [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hFzero : (0 : E) ∈ F) (hne : F ≠ {0}) :
    affineDimension (F ∩ heightSection (convexHull ℝ (V : Set E)) L) + 1 =
      affineDimension F := by
  let W := V.filter (fun x => x ∈ F)
  have hWzero : 0 ∈ W := Finset.mem_filter.mpr ⟨hzero, hFzero⟩
  have hWheight : ∀ x ∈ W.erase 0, L x ≠ 0 := by
    intro x hx
    have hx' := Finset.mem_erase.mp hx
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one
      (hheight x (Finset.mem_erase.mpr ⟨hx'.1, (Finset.mem_filter.mp hx'.2).1⟩)))
  have hFhull : F = convexHull ℝ (W : Set E) := by
    simpa only [W, Finset.coe_filter] using face_convexHull_eq hF
  rw [apexFace_section_eq_radialHull V hzero L hheight hF hFzero]
  conv_rhs => rw [hFhull]
  exact finiteHull_radialHull_dimension_intrinsic W hWzero L.toLinearMap hWheight
    (apexFace_generators_nonzero V hF hFzero hne)

/-- Explicit dimension shift in the actual face-poset order isomorphism. -/
theorem apexFaceSectionEquiv_dimension [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (F : {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val})
    (hne : F.val.val ≠ {0}) :
    affineDimension (apexFaceSectionEquiv V hzero L hheight F).val + 1 =
      affineDimension F.val.val :=
  apexFace_section_dimension V hzero L hheight F.val.property F.property hne

/-- For every nontrivial apex face, being a facet is equivalent to its
section being a facet of the vertex figure. -/
theorem apexFace_facet_iff_section_facet [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {F : Set E} (hF : IsConvexFace (convexHull ℝ (V : Set E)) F)
    (hFzero : (0 : E) ∈ F) (hne : F ≠ {0}) :
    Facet (convexHull ℝ (V : Set E)) F ↔
      Facet (heightSection (convexHull ℝ (V : Set E)) L)
        (F ∩ heightSection (convexHull ℝ (V : Set E)) L) := by
  have hPzero := subset_convexHull ℝ (V : Set E) hzero
  have hPne : convexHull ℝ (V : Set E) ≠ {0} := by
    intro h
    apply hne
    exact (hF.2.1.trans h.subset).antisymm (singleton_subset_iff.mpr hFzero)
  have hPface : IsConvexFace (convexHull ℝ (V : Set E)) (convexHull ℝ (V : Set E)) :=
    ⟨convex_convexHull ℝ (V : Set E), IsExtreme.refl ℝ _⟩
  have hdP := apexFace_section_dimension V hzero L hheight hPface hPzero hPne
  have hinter : convexHull ℝ (V : Set E) ∩
      heightSection (convexHull ℝ (V : Set E)) L =
      heightSection (convexHull ℝ (V : Set E)) L :=
    inter_eq_right.mpr (fun _ hx => hx.1)
  rw [hinter] at hdP
  have hdF := apexFace_section_dimension V hzero L hheight hF hFzero hne
  constructor
  · intro hf
    refine ⟨face_heightSection (convex_convexHull ℝ (V : Set E)) hF L,
      (apexFace_section_nonempty_iff V L hheight hF hFzero).mpr hne, ?_⟩
    have hrank := hf.2.2
    omega
  · intro hf
    refine ⟨hF, ⟨0, hFzero⟩, ?_⟩
    have hrank := hf.2.2
    omega

/-- In dimension at least two, every facet through the apex cuts out a
facet of the actual vertex figure; nontriviality follows from dimensions. -/
theorem apexFacet_section_facet [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hdim : 2 ≤ affineDimension (convexHull ℝ (V : Set E)))
    {F : Set E} (hF : Facet (convexHull ℝ (V : Set E)) F)
    (hFzero : (0 : E) ∈ F) :
    Facet (heightSection (convexHull ℝ (V : Set E)) L)
      (F ∩ heightSection (convexHull ℝ (V : Set E)) L) := by
  have hne : F ≠ {0} := by
    intro h
    have hrank := hF.2.2
    rw [h, affineDimension_singleton] at hrank
    omega
  exact (apexFace_facet_iff_section_facet V hzero L hheight hF.1 hFzero hne).mp hF

/-- Every facet of the vertex figure lifts to an actual facet through the
apex of the original polytope. -/
theorem sectionFacet_lift_facet [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {G : Set E} (hG : Facet (heightSection (convexHull ℝ (V : Set E)) L) G) :
    Facet (convexHull ℝ (V : Set E))
      (sectionFaceLift (convexHull ℝ (V : Set E)) L G) := by
  have hF := sectionFaceLift_isFace V hzero L hheight hG.1
  have hFzero : (0 : E) ∈ sectionFaceLift (convexHull ℝ (V : Set E)) L G :=
    ⟨subset_convexHull ℝ (V : Set E) hzero, Or.inl rfl⟩
  have hsection := sectionFaceLift_section L hG.1.2.1
  have hne := (apexFace_section_nonempty_iff V L hheight hF hFzero).mp
    (hsection.symm ▸ hG.2.1)
  apply (apexFace_facet_iff_section_facet V hzero L hheight hF hFzero hne).mpr
  rwa [hsection]

end Uniform5.Composition
