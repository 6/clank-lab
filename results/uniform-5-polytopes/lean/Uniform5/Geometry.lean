import Uniform5.Congruence
import Uniform5.Exclusions
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Geometric constructors for the conditional congruence interfaces. -/
noncomputable section
namespace Uniform5
open Set EuclideanGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


/-- A codimension-one affine subspace together with any point outside it
spans its containing affine subspace. This supplies the ridge-and-centre
spanning step from the actual dimension and strict-interiority facts. -/
theorem affineSpan_insert_eq_of_codimension_one [FiniteDimensional ℝ E]
    (G F : AffineSubspace ℝ E) (hne : (G : Set E).Nonempty) (hGF : G ≤ F)
    (hdim : Module.finrank ℝ G.direction + 1 = Module.finrank ℝ F.direction)
    {c : E} (hcF : c ∈ F) (hcG : c ∉ G) :
    affineSpan ℝ (insert c (G : Set E)) = F := by
  let A := affineSpan ℝ (insert c (G : Set E))
  have hGA : G ≤ A := by
    intro x hx
    exact subset_affineSpan ℝ _ (Set.mem_insert_of_mem c hx)
  have hcA : c ∈ A := subset_affineSpan ℝ _ (Set.mem_insert c _)
  have hAF : A ≤ F := affineSpan_le.mpr (by
    intro x hx
    rcases hx with rfl | hx
    · exact hcF
    · exact hGF hx)
  have hlt : G < A := lt_of_le_of_ne hGA (by intro h; exact hcG (h ▸ hcA))
  have hdlt := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hlt hne)
  by_contra hneAF
  have hdlt' := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty (lt_of_le_of_ne hAF hneAF) ⟨c, hcA⟩)
  omega

/-- Geometric ridge spanning in the form consumed by congruence propagation.
Only codimension one and a centre outside the ridge plane are supplied. -/
theorem ridge_centre_spans_of_codimension_one [FiniteDimensional ℝ E]
    (ridge facet : Set E) (c : E) (hne : ridge.Nonempty) (hsub : ridge ⊆ facet)
    (hc : c ∈ affineSpan ℝ facet) (hout : c ∉ affineSpan ℝ ridge)
    (hdim : Module.finrank ℝ (affineSpan ℝ ridge).direction + 1 =
      Module.finrank ℝ (affineSpan ℝ facet).direction) :
    ∀ x ∈ facet, x - c ∈ Submodule.span ℝ ((fun p => p - c) '' ridge) := by
  have heq := affineSpan_insert_eq_of_codimension_one
    (affineSpan ℝ ridge) (affineSpan ℝ facet) (hne.affineSpan ℝ)
    (affineSpan_mono ℝ hsub) hdim hc hout
  rw [affineSpan_insert_affineSpan] at heq
  intro x hx
  apply ridge_centre_span_of_affineSpan ridge c x
  rw [heq]
  exact subset_affineSpan ℝ facet hx

/-- A supporting functional with at least one strictly lower point is strict
at every relative interior point. No full ambient dimension is required. -/
theorem strict_support_of_intrinsicInterior (L : E →ₗ[ℝ] ℝ)
    {P : Set E} {c : E} {b : ℝ} (hsupport : ∀ x ∈ P, L x ≤ b)
    (hproper : ∃ z ∈ P, L z < b) (hc : c ∈ intrinsicInterior ℝ P) : L c < b := by
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨z, hz, hzb⟩ := hproper
  let A := affineSpan ℝ P
  letI : Nonempty A := ⟨c'⟩
  let z' : A := ⟨z, subset_affineSpan ℝ P hz⟩
  have h := AffineMap.lineMap_apply_one (k := ℝ) z' c'
  have hcont : Continuous (AffineMap.lineMap z' c' : ℝ → A) := by
    change Continuous (fun t : ℝ => t • (c' -ᵥ z') +ᵥ z')
    fun_prop
  obtain ⟨t, ht1, ht⟩ := hcont.tendsto' _ _ h |>.eventually_mem
    (mem_interior_iff_mem_nhds.1 hc') |>.exists_gt
  have hb := hsupport _ ht
  have heq : ((AffineMap.lineMap z' c' t : A) : E) =
      t • ((c' : E) - z) + z := by
    simp [AffineMap.lineMap_apply, AffineSubspace.coe_vadd, AffineSubspace.coe_vsub, z']
  rw [heq, map_add, map_smul, map_sub] at hb
  have hcp : (c' : E) ∈ P := @interior_subset _ _ (Subtype.val ⁻¹' P) c' hc'
  have hcb := hsupport (c' : E) hcp
  simp only [smul_eq_mul] at hb
  nlinarith

/-- Proper supported ridge planes miss the facet's relative interior centre. -/
theorem relative_interior_not_on_support (L : E →ₗ[ℝ] ℝ)
    {P ridge : Set E} {c : E} {b : ℝ}
    (hsupport : ∀ x ∈ P, L x ≤ b) (hproper : ∃ z ∈ P, L z < b)
    (hridge : ∀ x ∈ affineSpan ℝ ridge, L x = b)
    (hc : c ∈ intrinsicInterior ℝ P) : c ∉ affineSpan ℝ ridge := by
  intro h
  exact (ne_of_lt (strict_support_of_intrinsicInterior L hsupport hproper hc)) (hridge c h)

/-- A constant linear-functional value on generators extends to their affine span. -/
theorem linear_eq_on_affineSpan (L : E →ₗ[ℝ] ℝ) {s : Set E} {b : ℝ}
    (hs : ∀ x ∈ s, L x = b) : ∀ x ∈ affineSpan ℝ s, L x = b := by
  intro x hx
  exact affineSpan_induction (p := fun y => L y = b) hx hs (by
    intro a u v w hu hv hw
    simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, hu, hv, hw]
    simp)

/-- Two circumspheres on the same spanning set have centres differing in a
normal direction if one centre belongs to that affine span. Thus the facet
circumcentre's projection orthogonality follows from the sphere data. -/
theorem circumsphere_centres_orthogonal {s : Set E} {c o : E} {R r : ℝ}
    (ho : o ∈ affineSpan ℝ s)
    (hR : ∀ x ∈ s, dist x c = R) (hr : ∀ x ∈ s, dist x o = r) :
    ∀ x ∈ affineSpan ℝ s, ⟪x - o, c - o⟫ = 0 := by
  let L : E →ₗ[ℝ] ℝ := (innerSL ℝ (c - o)).toLinearMap
  let b : ℝ := (‖c‖ ^ 2 - ‖o‖ ^ 2 + r ^ 2 - R ^ 2) / 2
  have hbase : ∀ x ∈ s, L x = b := by
    intro x hx
    have h₁ := norm_sub_sq_real x c
    have h₂ := norm_sub_sq_real x o
    have hxR : ‖x - c‖ = R := by simpa [dist_eq_norm] using hR x hx
    have hxr : ‖x - o‖ = r := by simpa [dist_eq_norm] using hr x hx
    rw [hxR] at h₁
    rw [hxr] at h₂
    change ⟪c - o, x⟫ = b
    rw [real_inner_comm, inner_sub_right]
    dsimp [b]
    linarith
  have hall := linear_eq_on_affineSpan L hbase
  intro x hx
  have heq : L (x - o) = 0 := by rw [map_sub, hall x hx, hall o ho, sub_self]
  simpa only [L, ContinuousLinearMap.coe_coe, innerSL_apply, real_inner_comm] using heq

/-- Projection supplies the radius orthogonality without an extra premise. -/
theorem affine_projection_radius_orthogonal [FiniteDimensional ℝ E]
    (F : AffineSubspace ℝ E) [Nonempty F] (c : E) {x : E} (hx : x ∈ F) :
    ⟪x - (EuclideanGeometry.orthogonalProjection F c : E),
      c - (EuclideanGeometry.orthogonalProjection F c : E)⟫ = 0 := by
  exact Submodule.inner_right_of_mem_orthogonal
    (F.vsub_mem_direction hx (EuclideanGeometry.orthogonalProjection_mem c))
    (EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal F c)

/-- Radius strictness from an actual affine facet projection. The support
level of the projected centre and all projection orthogonality are derived. -/
theorem facet_radius_lt_of_affine_projection [FiniteDimensional ℝ E]
    (F : AffineSubspace ℝ E) [Nonempty F] (L : E →L[ℝ] ℝ)
    (hL : ∃ y, L y ≠ 0) {P : Set E} {c x : E} {b R r : ℝ}
    (hsupport : ∀ y ∈ P, L y ≤ b) (hc : c ∈ interior P)
    (hF : ∀ y ∈ F, L y = b) (hx : x ∈ F)
    (hR : ‖x - c‖ = R)
    (hr : ‖x - (EuclideanGeometry.orthogonalProjection F c : E)‖ = r) : r < R := by
  exact facet_radius_lt_of_projection L hL hsupport hc
    (hF _ (EuclideanGeometry.orthogonalProjection_mem c)) hR hr
    (affine_projection_radius_orthogonal F c hx)

/-- A nonempty proper exposed face supplies a genuine supporting functional,
constant on its affine span, with a strict point in the original set. -/
theorem proper_exposed_face_support {P F : Set E} (hF : IsExposed ℝ P F)
    (hne : F.Nonempty) (hproper : F ≠ P) :
    ∃ (L : E →L[ℝ] ℝ) (b : ℝ),
      (∃ y, L y ≠ 0) ∧ (∀ y ∈ P, L y ≤ b) ∧
      (∀ y ∈ affineSpan ℝ F, L y = b) ∧ (∃ z ∈ P, L z < b) := by
  obtain ⟨L, hrepr⟩ := hF hne
  obtain ⟨w, hw⟩ := hne
  have hw' : w ∈ P ∧ ∀ y ∈ P, L y ≤ L w := by simpa only [hrepr, Set.mem_setOf_eq] using hw
  obtain ⟨z, hz, hzF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  have hlt : L z < L w := lt_of_le_of_ne (hw'.2 z hz) (by
    intro heq
    apply hzF
    rw [hrepr]
    exact ⟨hz, fun y hy => (hw'.2 y hy).trans_eq heq.symm⟩)
  refine ⟨L, L w, ⟨w - z, ?_⟩, hw'.2, ?_, ⟨z, hz, hlt⟩⟩
  · rw [map_sub]
    exact sub_ne_zero.mpr (ne_of_gt hlt)
  · apply linear_eq_on_affineSpan L.toLinearMap
    intro y hy
    have hy' : y ∈ P ∧ ∀ x ∈ P, L x ≤ L y := by simpa only [hrepr, Set.mem_setOf_eq] using hy
    exact le_antisymm (hw'.2 y hy'.1) (hy'.2 w hw'.1)

/-- A proper exposed ridge has a supporting plane missing the relative
interior centre; codimension one then supplies the propagation span. -/
theorem ridge_centre_spans_of_exposed_face [FiniteDimensional ℝ E]
    {P G : Set E} {c : E} (hG : IsExposed ℝ P G) (hne : G.Nonempty)
    (hproper : G ≠ P) (hc : c ∈ intrinsicInterior ℝ P)
    (hdim : Module.finrank ℝ (affineSpan ℝ G).direction + 1 =
      Module.finrank ℝ (affineSpan ℝ P).direction) :
    ∀ x ∈ P, x - c ∈ Submodule.span ℝ ((fun p => p - c) '' G) := by
  obtain ⟨L, b, _, hs, hg, hp⟩ := proper_exposed_face_support hG hne hproper
  exact ridge_centre_spans_of_codimension_one G P c hne hG.subset
    (subset_affineSpan ℝ P (intrinsicInterior_subset hc))
    (relative_interior_not_on_support L.toLinearMap hs hp hg hc) hdim

/-- The strict radius inequality with both the support and the projection
orthogonality derived from the exposed-face and circumsphere data. -/
theorem facet_radius_lt_of_exposed_face [FiniteDimensional ℝ E]
    {P F : Set E} {c o x : E} {R r : ℝ}
    (hF : IsExposed ℝ P F) (hne : F.Nonempty) (hproper : F ≠ P)
    (hc : c ∈ interior P) (ho : o ∈ affineSpan ℝ F) (hx : x ∈ F)
    (hR : ∀ y ∈ F, dist y c = R) (hr : ∀ y ∈ F, dist y o = r) : r < R := by
  obtain ⟨L, b, hL, hs, hf, _⟩ := proper_exposed_face_support hF hne hproper
  exact facet_radius_lt_of_projection L hL hs hc (hf o ho)
    (by simpa [dist_eq_norm] using hR x hx)
    (by simpa [dist_eq_norm] using hr x hx)
    (circumsphere_centres_orthogonal ho hR hr x (subset_affineSpan ℝ F hx))

/-- Vertex-set form of the preceding ridge span theorem. Convex hulls are
used for the exposed faces; the conclusion spans only the ridge vertices. -/
theorem ridge_vertex_spans_of_exposed_hulls [FiniteDimensional ℝ E]
    {P G : Set E} {c : E}
    (hG : IsExposed ℝ (convexHull ℝ P) (convexHull ℝ G))
    (hne : G.Nonempty) (hsub : G ⊆ P)
    (hproper : convexHull ℝ G ≠ convexHull ℝ P)
    (hc : c ∈ intrinsicInterior ℝ (convexHull ℝ P))
    (hdim : Module.finrank ℝ (affineSpan ℝ G).direction + 1 =
      Module.finrank ℝ (affineSpan ℝ P).direction) :
    ∀ x ∈ P, x - c ∈ Submodule.span ℝ ((fun p => p - c) '' G) := by
  obtain ⟨L, b, _, hs, hg, hp⟩ := proper_exposed_face_support hG
    (hne.mono (subset_convexHull ℝ G)) hproper
  have hcspan : c ∈ affineSpan ℝ P := by
    rw [← affineSpan_convexHull P]
    exact subset_affineSpan ℝ _ (intrinsicInterior_subset hc)
  have hout := relative_interior_not_on_support L.toLinearMap hs hp hg hc
  rw [affineSpan_convexHull] at hout
  exact ridge_centre_spans_of_codimension_one G P c hne hsub hcspan hout hdim

/-- Lemma D with initial linear extension and ridge-and-centre spanning
constructed from sphere norms, actual exposed ridge hulls, codimension one
and relatively interior facet centres. The projected opposite-side plane and
facet graph inputs remain explicit. -/
theorem congruence_from_exposed_ridge_geometry [FiniteDimensional ℝ E]
    {I F : Type*} (V V' : I → E) (facet : F → Set I)
    (centre centre' : F → E) (adjacent : F → F → Prop)
    (ridge : F → F → Set I)
    (data : ∀ f, ExactFacetCorrespondence V V' (facet f) (centre f) (centre' f))
    (root : F) (root_norms : ∀ i ∈ facet root, ‖V' i‖ = ‖V i‖)
    (facet_graph_connected : ∀ f, Relation.ReflTransGen adjacent root f)
    (facet_covers : ∀ i, ∃ f, i ∈ facet f)
    (ridge_in_facets : ∀ f g, adjacent f g → ridge f g ⊆ facet f ∩ facet g)
    (ridge_nonempty : ∀ f g, adjacent f g → (ridge f g).Nonempty)
    (ridge_exposed : ∀ f g, adjacent f g →
      IsExposed ℝ (convexHull ℝ (V '' facet g)) (convexHull ℝ (V '' ridge f g)))
    (ridge_proper : ∀ f g, adjacent f g →
      convexHull ℝ (V '' ridge f g) ≠ convexHull ℝ (V '' facet g))
    (ridge_codimension : ∀ f g, adjacent f g →
      Module.finrank ℝ (affineSpan ℝ (V '' ridge f g)).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ (V '' facet g)).direction)
    (centre_interior : ∀ f, centre f ∈ intrinsicInterior ℝ (convexHull ℝ (V '' facet f)))
    (opposite_side_projection_data :
      ∀ (A : E ≃ₗᵢ[ℝ] E) f g, adjacent f g →
        (∀ i ∈ facet f, A (V i) = V' i) →
          OppositeTangentData (A (centre g)) (centre' g)) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ i, A (V i) = V' i := by
  apply congruence_from_tangent_ridge_data V V' facet centre centre' adjacent ridge
    data root root_norms facet_graph_connected facet_covers ridge_in_facets
    _ opposite_side_projection_data
  intro f g hfg i hi
  have hspan := ridge_vertex_spans_of_exposed_hulls (ridge_exposed f g hfg)
    ((ridge_nonempty f g hfg).image V)
    (Set.image_mono (fun j hj => (ridge_in_facets f g hfg hj).2))
    (ridge_proper f g hfg) (centre_interior g) (ridge_codimension f g hfg)
    (V i) ⟨i, hi, rfl⟩
  simpa only [Set.image_image, Function.comp_def] using hspan

/-- The circumcentre in the affine span is unique, without a simplex or
independence assumption on the spanning set. -/
theorem circumcenter_unique_in_affineSpan {s : Set E} {c o : E} {R r : ℝ}
    (hc : c ∈ affineSpan ℝ s) (ho : o ∈ affineSpan ℝ s)
    (hR : ∀ x ∈ s, dist x c = R) (hr : ∀ x ∈ s, dist x o = r) : c = o := by
  have h := circumsphere_centres_orthogonal ho hR hr c hc
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h)

/-- A genuine symmetry of a cospherical spanning set fixes its circumcentre.
This supplies the model-centre field in exact facet correspondences. -/
theorem symmetry_fixes_circumcenter (T : E ≃ᵃⁱ[ℝ] E) {s : Set E} {c : E} {R : ℝ}
    (hT : T '' s = s) (hc : c ∈ affineSpan ℝ s)
    (hR : ∀ x ∈ s, dist x c = R) : T c = c := by
  have hTc : T c ∈ affineSpan ℝ s := by
    have h : T c ∈ (affineSpan ℝ s).map T.toAffineEquiv.toAffineMap := ⟨c, hc, rfl⟩
    rw [AffineSubspace.map_span] at h
    change T c ∈ affineSpan ℝ (T '' s) at h
    rwa [hT] at h
  apply circumcenter_unique_in_affineSpan (R := R) hTc hc _ hR
  intro x hx
  rw [← hT] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [T.dist_map]
  exact hR y hy

end Uniform5
