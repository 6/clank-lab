import Uniform5.CompositionExposedFaces
import Uniform5.CompositionFaceCenters
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Actual transverse projection at a face

The quotient is realized as orthogonal projection onto the perpendicular
complement of the face directions. Its distinguished origin is proved to
be an actual vertex, not supplied as cone data.
-/
noncomputable section
namespace Uniform5.Composition
open Set Classical
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Arbitrary affine maps preserve the finite convex-hull condition. -/
theorem finitePolytope_affineMap_image (f : E →ᵃ[ℝ] H) {P : Set E}
    (hP : FinitePolytope P) : FinitePolytope (f '' P) := by
  obtain ⟨V, hV, rfl⟩ := hP
  refine ⟨V.image f, hV.image f, ?_⟩
  simpa only [Finset.coe_image] using f.image_convexHull (V : Set E)

variable [FiniteDimensional ℝ E]

/-- Transverse coordinates relative to a chosen point of a face. -/
noncomputable def transverseProjection (G : Set E) (c : E) :
    E →ᵃ[ℝ] (affineSpan ℝ G).directionᗮ :=
  ((affineSpan ℝ G).directionᗮ.orthogonalProjection.toLinearMap.toAffineMap).comp
    (AffineEquiv.constVAdd ℝ E (-c)).toAffineMap

@[simp] theorem transverseProjection_apply (G : Set E) (c x : E) :
    transverseProjection G c x =
      (affineSpan ℝ G).directionᗮ.orthogonalProjection (x - c) := by
  simp [transverseProjection, sub_eq_add_neg, add_comm]

@[simp] theorem transverseProjection_center (G : Set E) (c : E) :
    transverseProjection G c c = 0 := by simp

/-- The projection has precisely the original face directions as kernel. -/
theorem transverseProjection_zero_iff (G : Set E) {c : E} (hc : c ∈ G) (x : E) :
    transverseProjection G c x = 0 ↔ x ∈ affineSpan ℝ G := by
  rw [transverseProjection_apply, Submodule.orthogonalProjection_eq_zero_iff,
    Submodule.orthogonal_orthogonal]
  exact AffineSubspace.vsub_right_mem_direction_iff_mem (subset_affineSpan ℝ G hc) x

theorem transverseProjection_surjective (G : Set E) (c : E) :
    Function.Surjective (transverseProjection G c) := by
  intro y
  refine ⟨(y : E) + c, ?_⟩
  rw [transverseProjection_apply, add_sub_cancel_right,
    Submodule.orthogonalProjection_mem_subspace_eq_self]

/-- The face itself, rather than a larger part of the polytope, is the
zero fiber of the actual quotient. -/
theorem transverseProjection_zero_fiber {P G : Set E}
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) :
    P ∩ (transverseProjection G c) ⁻¹' {0} = G := by
  have hpre : (transverseProjection G c) ⁻¹' {0} = (affineSpan ℝ G : Set E) := by
    ext x
    exact transverseProjection_zero_iff G hc x
  rw [hpre]
  exact face_affineSpan_inter hG ⟨c, hc⟩

/-- Every point of the face projects to the distinguished origin. -/
theorem transverseProjection_face_image (G : Set E) {c : E} (hc : c ∈ G) :
    transverseProjection G c '' G = {0} := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (transverseProjection_zero_iff G hc x).mpr (subset_affineSpan ℝ G hx)
  · rintro y rfl
    exact ⟨c, hc, transverseProjection_center G c⟩

/-- The transverse image is an actual finite convex polytope. -/
theorem finitePolytope_transverse {P : Set E} (hP : FinitePolytope P)
    (G : Set E) (c : E) : FinitePolytope (transverseProjection G c '' P) :=
  finitePolytope_affineMap_image _ hP

/-- Collapsing a face produces an actual extreme vertex of the quotient. -/
theorem transverse_origin_extreme {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) :
    (0 : (affineSpan ℝ G).directionᗮ) ∈
      (transverseProjection G c '' P).extremePoints ℝ := by
  let f := transverseProjection G c
  refine ⟨⟨c, hG.2.1 hc, transverseProjection_center G c⟩, ?_⟩
  rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ hs
  rw [← image_openSegment ℝ f x y] at hs
  obtain ⟨z, hzseg, hzf⟩ := hs
  have hzP := (finitePolytope_convex hP).segment_subset hx hy (openSegment_subset_segment ℝ x y hzseg)
  have hzG : z ∈ G := by
    rw [← transverseProjection_zero_fiber hG hc]
    exact ⟨hzP, hzf⟩
  obtain ⟨hxG, hyG⟩ := hG.2.2 hx hy hzG hzseg
  exact ⟨(transverseProjection_zero_iff G hc x).mpr (subset_affineSpan ℝ G hxG),
    (transverseProjection_zero_iff G hc y).mpr (subset_affineSpan ℝ G hyG)⟩

/-- A full-dimensional parent projects onto a full-dimensional quotient. -/
theorem transverse_affineSpan_eq_top {P : Set E} (hfull : affineSpan ℝ P = ⊤)
    (G : Set E) (c : E) :
    affineSpan ℝ (transverseProjection G c '' P) = ⊤ := by
  rw [← AffineSubspace.map_span, hfull]
  exact AffineMap.map_top_of_surjective _ (transverseProjection_surjective G c)

/-- The quotient loses exactly the dimension of the collapsed face. -/
theorem transverse_dimension_add {P : Set E} (hfull : affineSpan ℝ P = ⊤)
    (G : Set E) (c : E) :
    affineDimension (transverseProjection G c '' P) + affineDimension G = Module.finrank ℝ E := by
  rw [affineDimension, Uniform5.affineDimension, transverse_affineSpan_eq_top hfull, AffineSubspace.direction_top,
    finrank_top]
  have hh := (affineSpan ℝ G).direction.finrank_add_finrank_orthogonal
  change Module.finrank ℝ (affineSpan ℝ G).directionᗮ +
    Module.finrank ℝ (affineSpan ℝ G).direction = Module.finrank ℝ E
  omega

/-- For an actual polygon face of a unit-uniform five-polytope, the
transverse image is a genuine full-dimensional three-polytope with an
actual vertex at zero. The chosen center can be its proven face centroid. -/
theorem unitUniform5_polygon_transverse {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {k : ℕ} (hG : PolygonFace P G k) {c : Space 5} (hc : c ∈ G) :
    FinitePolytope (transverseProjection G c '' P) ∧
    affineDimension (transverseProjection G c '' P) = 3 ∧
    affineSpan ℝ (transverseProjection G c '' P) = ⊤ ∧
    transverseProjection G c '' G = {0} ∧
    (0 : (affineSpan ℝ G).directionᗮ) ∈
      (transverseProjection G c '' P).extremePoints ℝ := by
  have hfull := uniform5_affineSpan_eq_top hP.1
  refine ⟨finitePolytope_transverse (uniform_finitePolytope hP.1) G c, ?_,
    transverse_affineSpan_eq_top hfull G c, transverseProjection_face_image G hc,
    transverse_origin_extreme (uniform_finitePolytope hP.1) hG.1 hc⟩
  have hh := transverse_dimension_add hfull G c
  rw [hG.2.1] at hh
  have hdim : Module.finrank ℝ (Space 5) = 5 := by simp [Space]
  omega

/-- Equal quotient coordinates differ by a direction of the collapsed
face, independently of the choice of center. -/
theorem transverseProjection_eq_iff (G : Set E) (c x y : E) :
    transverseProjection G c x = transverseProjection G c y ↔
      x - y ∈ (affineSpan ℝ G).direction := by
  rw [transverseProjection_apply, transverseProjection_apply, ← sub_eq_zero, ← map_sub]
  have heq : x - c - (y - c) = x - y := by abel
  rw [heq, Submodule.orthogonalProjection_eq_zero_iff, Submodule.orthogonal_orthogonal]

/-- Every actual face containing the collapsed face is saturated in the
parent under the transverse projection. -/
theorem transverse_face_saturated {P G F : Set E}
    (hF : IsConvexFace P F) (hGF : G ⊆ F) {c : E} (hc : c ∈ G) :
    P ∩ (transverseProjection G c) ⁻¹' (transverseProjection G c '' F) = F := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxP, y, hyF, hxy⟩
    have hdir := (transverseProjection_eq_iff G c x y).mp hxy.symm
    have hdir' : x - y ∈ (affineSpan ℝ F).direction :=
      AffineSubspace.direction_le (affineSpan_mono ℝ hGF) hdir
    have hxA := (AffineSubspace.vsub_right_mem_direction_iff_mem
      (subset_affineSpan ℝ F hyF) x).mp hdir'
    rw [← face_affineSpan_inter hF ⟨c, hGF hc⟩]
    exact ⟨hxP, hxA⟩
  · intro x hx
    exact ⟨hF.2.1 hx, mem_image_of_mem _ hx⟩

omit [FiniteDimensional ℝ E] in
/-- A saturated geometric face maps to a genuine geometric face under an
arbitrary affine map; endpoint lifting supplies extremity. -/
theorem affineMap_image_face_of_saturated (f : E →ᵃ[ℝ] H) {P F : Set E}
    (hP : Convex ℝ P) (hF : IsConvexFace P F)
    (hsat : P ∩ f ⁻¹' (f '' F) = F) : IsConvexFace (f '' P) (f '' F) := by
  refine ⟨hF.1.affine_image f, image_mono hF.2.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
  rw [← image_openSegment ℝ f x y] at hseg
  obtain ⟨w, hwseg, hwf⟩ := hseg
  have hwP := hP.segment_subset hx hy (openSegment_subset_segment ℝ x y hwseg)
  have hwF : w ∈ F := by
    rw [← hsat]
    exact ⟨hwP, z, hz, hwf.symm⟩
  obtain ⟨hxF, hyF⟩ := hF.2.2 hx hy hwF hwseg
  exact ⟨mem_image_of_mem f hxF, mem_image_of_mem f hyF⟩

/-- Actual parent faces containing the polygon project to actual quotient
faces. No exposed-face or cone-incidence hypothesis is needed. -/
theorem transverse_face_image {P G F : Set E} (hP : FinitePolytope P)
    (hF : IsConvexFace P F) (hGF : G ⊆ F) {c : E} (hc : c ∈ G) :
    IsConvexFace (transverseProjection G c '' P) (transverseProjection G c '' F) :=
  affineMap_image_face_of_saturated _ (finitePolytope_convex hP) hF
    (transverse_face_saturated hF hGF hc)

omit [FiniteDimensional ℝ E] in
/-- Pulling a genuine image face back inside the parent preserves its
actual convex-face property. -/
theorem affineMap_preimage_face (f : E →ᵃ[ℝ] H) {P : Set E} (hP : Convex ℝ P)
    {C : Set H} (hC : IsConvexFace (f '' P) C) : IsConvexFace P (P ∩ f ⁻¹' C) := by
  refine ⟨hP.inter (hC.1.affine_preimage f), inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  have hseg' : f z ∈ openSegment ℝ (f x) (f y) := by
    rw [← image_openSegment ℝ f x y]
    exact mem_image_of_mem f hseg
  obtain ⟨hxC, hyC⟩ := hC.2.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) hz.2 hseg'
  exact ⟨⟨hx, hxC⟩, ⟨hy, hyC⟩⟩

omit [FiniteDimensional ℝ E] in
theorem affineMap_image_preimage_face (f : E →ᵃ[ℝ] H) {P : Set E} {C : Set H}
    (hC : C ⊆ f '' P) : f '' (P ∩ f ⁻¹' C) = C := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hC hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

/-- Genuine parent faces containing `G` and genuine quotient faces
containing zero form order-isomorphic face posets. -/
noncomputable def transverseFaceEquiv {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) :
    {F : GeometricFace P // G ⊆ F.val} ≃o
      {C : GeometricFace (transverseProjection G c '' P) // (0 : (affineSpan ℝ G).directionᗮ) ∈ C.val} where
  toFun F := ⟨⟨transverseProjection G c '' F.val.val,
    transverse_face_image hP F.val.property F.property hc⟩,
    ⟨c, F.property hc, transverseProjection_center G c⟩⟩
  invFun C := ⟨⟨P ∩ (transverseProjection G c) ⁻¹' C.val.val,
    affineMap_preimage_face _ (finitePolytope_convex hP) C.val.property⟩, by
      intro x hx
      refine ⟨hG.2.1 hx, ?_⟩
      have hz := (transverseProjection_zero_iff G hc x).mpr (subset_affineSpan ℝ G hx)
      change transverseProjection G c x ∈ C.val.val
      rw [hz]
      exact C.property⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    exact transverse_face_saturated F.val.property F.property hc
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact affineMap_image_preimage_face _ C.val.property.2.1
  map_rel_iff' := by
    intro F H
    constructor
    · intro hFH x hx
      change x ∈ H.val.val
      rw [← transverse_face_saturated H.val.property H.property hc]
      exact ⟨F.val.property.2.1 hx, hFH (mem_image_of_mem _ hx)⟩
    · intro hFH
      exact image_mono hFH

@[simp] theorem transverseProjection_linear (G : Set E) (c : E) :
    (transverseProjection G c).linear =
      (affineSpan ℝ G).directionᗮ.orthogonalProjection.toLinearMap := by
  rfl

/-- Rank-nullity for an orthogonal quotient restricted to a subspace
containing all collapsed directions. -/
theorem orthogonalProjection_map_dimension_add (K S : Submodule ℝ E) (hKS : K ≤ S) :
    Module.finrank ℝ (S.map Kᗮ.orthogonalProjection.toLinearMap) + Module.finrank ℝ K =
      Module.finrank ℝ S := by
  let q := Kᗮ.orthogonalProjection.toLinearMap.comp S.subtype
  have hrange : LinearMap.range q = S.map Kᗮ.orthogonalProjection.toLinearMap := by
    dsimp only [q]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker q = K.comap S.subtype := by
    ext x
    change Kᗮ.orthogonalProjection (x : E) = 0 ↔ (x : E) ∈ K
    rw [Submodule.orthogonalProjection_eq_zero_iff, Submodule.orthogonal_orthogonal]
  have hkerdim : Module.finrank ℝ (LinearMap.ker q) = Module.finrank ℝ K := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hKS).finrank_eq
  have hh := q.finrank_range_add_finrank_ker
  rwa [hrange, hkerdim] at hh

/-- Every set containing the collapsed face loses exactly that face's
affine dimension under projection. In particular this applies to each
actual cell or facet incident to the polygon. -/
theorem transverse_image_dimension_add {G F : Set E} (hGF : G ⊆ F) (c : E) :
    affineDimension (transverseProjection G c '' F) + affineDimension G = affineDimension F := by
  unfold affineDimension Uniform5.affineDimension
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction, transverseProjection_linear]
  exact orthogonalProjection_map_dimension_add _ _
    (AffineSubspace.direction_le (affineSpan_mono ℝ hGF))

@[simp] theorem transverseFaceEquiv_apply {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (F : {F : GeometricFace P // G ⊆ F.val}) :
    (transverseFaceEquiv hP hG hc F).val.val = transverseProjection G c '' F.val.val := rfl

/-- The actual quotient face-poset isomorphism carries the proven rank
shift, with no assumption about incidence labels. -/
theorem transverseFaceEquiv_dimension {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (F : {F : GeometricFace P // G ⊆ F.val}) :
    affineDimension (transverseFaceEquiv hP hG hc F).val.val + affineDimension G =
      affineDimension F.val.val := transverse_image_dimension_add F.property c

end Uniform5.Composition
