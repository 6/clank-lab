import Uniform5.CompositionTransversePole

/-! Orthogonal tangent-plane transport of the actual transverse link.
The height plane is not assumed perpendicular to the centroid axis. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Orthogonal projection to the plane perpendicular to the actual axis. -/
noncomputable def axialProjection (y : E) : E →L[ℝ] (ℝ ∙ y)ᗮ :=
  (ℝ ∙ y)ᗮ.orthogonalProjection

omit [FiniteDimensional ℝ E] in
@[simp] theorem axialProjection_self (y : E) : axialProjection y y = 0 := by
  rw [axialProjection, Submodule.orthogonalProjection_eq_zero_iff,
    Submodule.orthogonal_orthogonal]
  exact Submodule.mem_span_singleton_self y

omit [FiniteDimensional ℝ E] in
/-- Orthogonal projection is injective on any cutting plane transverse
to the axis. -/
theorem axialProjection_injOn_level (y : E) (L : E →L[ℝ] ℝ) (hy : L y ≠ 0) :
    Set.InjOn (axialProjection y) {x | L x = 1} := by
  intro x hx z hz heq
  change L x = 1 at hx
  change L z = 1 at hz
  have hh : axialProjection y (x - z) = 0 := by rw [map_sub, heq, sub_self]
  rw [axialProjection, Submodule.orthogonalProjection_eq_zero_iff,
    Submodule.orthogonal_orthogonal] at hh
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hh
  have hLa := congrArg L ha
  have ha0 : a = 0 := by
    have hh : a * L y = 0 := by simpa only [map_smul, map_sub, hx, hz, sub_self,
      smul_eq_mul] using hLa
    exact (mul_eq_zero.mp hh).resolve_right hy
  rw [ha0, zero_smul] at ha
  exact sub_eq_zero.mp ha.symm

omit [FiniteDimensional ℝ E] in
/-- Every point in the orthogonal plane has a unique lift to height one. -/
theorem axialProjection_level_surjective (y : E) (L : E →L[ℝ] ℝ) (hy : L y ≠ 0)
    (z : (ℝ ∙ y)ᗮ) :
    ∃! x : E, L x = 1 ∧ axialProjection y x = z := by
  let x : E := z + ((1 - L z) / L y) • y
  have hxL : L x = 1 := by
    simp only [x, map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
    ring
  have hxπ : axialProjection y x = z := by
    simp only [x, map_add, map_smul, axialProjection_self, smul_zero, add_zero]
    exact Submodule.orthogonalProjection_mem_subspace_eq_self z
  refine ⟨x, ⟨hxL, hxπ⟩, ?_⟩
  intro w hw
  exact axialProjection_injOn_level y L hy hw.1 hxL (hw.2.trans hxπ.symm)

/-- The orthogonal axis plane in a three-dimensional transverse space
has dimension two. -/
theorem axialProjection_target_finrank (hE : Module.finrank ℝ E = 3) {y : E} (hy : y ≠ 0) :
    Module.finrank ℝ (ℝ ∙ y)ᗮ = 2 := by
  have hh := (ℝ ∙ y).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hy, hE] at hh
  omega

omit [FiniteDimensional ℝ E] in
/-- A level-one condition extends from a polytope to its affine span. -/
theorem affineSpan_height_one {S : Set E} (L : E →L[ℝ] ℝ)
    (hh : ∀ z ∈ S, L z = 1) {z : E} (hz : z ∈ affineSpan ℝ S) : L z = 1 := by
  have hle : affineSpan ℝ S ≤ (affineSpan ℝ ({1} : Set ℝ)).comap L.toLinearMap.toAffineMap :=
    affineSpan_le.mpr (fun x hx => by simpa using hh x hx)
  simpa using hle hz

/-- The axis projection of a genuine planar section remains a finite
planar polytope, with the projected pole in its ambient interior. -/
theorem axialProjection_polygon_interior (hE : Module.finrank ℝ E = 3)
    {S : Set E} (hS : FinitePolytope S) (hdS : affineDimension S = 2)
    (L : E →L[ℝ] ℝ) (hh : ∀ z ∈ S, L z = 1)
    {y : E} (hy : L y ≠ 0) (hp : radialPoint L y ∈ intrinsicInterior ℝ S) :
    FinitePolytope (axialProjection y '' S) ∧
      affineDimension (axialProjection y '' S) = 2 ∧
      (0 : (ℝ ∙ y)ᗮ) ∈ interior (axialProjection y '' S) := by
  have hy0 : y ≠ 0 := by intro h; apply hy; simp [h]
  have hdT := axialProjection_target_finrank hE hy0
  obtain ⟨f, Q, him, hf0, hQ, hdQ, h0⟩ := exists_centered_complex_polytope hS hdS hp
  have hfull : affineSpan ℝ Q = ⊤ := by
    have hdir : (affineSpan ℝ Q).direction = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa only [Complex.finrank_real_complex] using hdQ
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty ?_).mp hdir
    obtain ⟨q, hq⟩ := finitePolytope_nonempty hQ
    exact ⟨q, subset_affineSpan ℝ Q hq⟩
  have hflevel (z : ℂ) : L (f z) = 1 := by
    apply affineSpan_height_one L hh
    rw [← him]
    change f.toAffineMap z ∈ affineSpan ℝ (f.toAffineMap '' Q)
    rw [← AffineSubspace.map_span, hfull]
    exact ⟨z, Set.mem_univ z, rfl⟩
  let g : ℂ →ᵃ[ℝ] (ℝ ∙ y)ᗮ := (axialProjection y).toLinearMap.toAffineMap.comp f.toAffineMap
  have hg0 : g 0 = 0 := by
    change axialProjection y (f 0) = 0
    rw [hf0]
    simp only [radialPoint, map_smul, axialProjection_self, smul_zero]
  have hginj : Function.Injective g := by
    intro a b hab
    apply f.injective
    exact axialProjection_injOn_level y L hy (hflevel a) (hflevel b) hab
  have hglinj : Function.Injective g.linear := g.linear_injective_iff.mpr hginj
  have hglsurj : Function.Surjective g.linear :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Complex.finrank_real_complex, hdT])).mp hglinj
  let A := LinearMap.toContinuousLinearMap g.linear
  have hAg (z : ℂ) : A z = g z := by
    have hh := g.map_vadd 0 z
    simpa only [vadd_eq_add, add_zero, hg0] using hh.symm
  have hAsurj : Function.Surjective A := hglsurj
  have himage : A '' Q = axialProjection y '' S := by
    rw [← him, image_image]
    exact image_congr (fun z _ => hAg z)
  have hint : (0 : (ℝ ∙ y)ᗮ) ∈ interior (axialProjection y '' S) := by
    rw [← himage]
    have h0' : (0 : ℂ) ∈ interior Q := by
      rwa [intrinsicInterior_eq_interior_of_full_span hfull] at h0
    have hi := A.isOpenMap hAsurj |>.image_interior_subset Q (mem_image_of_mem A h0')
    simpa only [map_zero] using hi
  have hfullT : affineSpan ℝ (axialProjection y '' S) = ⊤ :=
    (((finitePolytope_convex hS).linear_image (axialProjection y).toLinearMap).interior_nonempty_iff_affineSpan_eq_top).mp ⟨0, hint⟩
  refine ⟨finitePolytope_affineMap_image (axialProjection y).toLinearMap.toAffineMap hS, ?_, hint⟩
  unfold affineDimension Uniform5.affineDimension
  rw [hfullT]
  rw [AffineSubspace.direction_top, finrank_top]
  exact hdT

omit [FiniteDimensional ℝ E] in
/-- Projection reflects and preserves each actual face of the cutting
polygon; its injectivity on the height plane supplies saturation. -/
theorem axialProjection_face_iff {S F : Set E} (hS : Convex ℝ S)
    (L : E →L[ℝ] ℝ) (hh : ∀ z ∈ S, L z = 1) {y : E} (hy : L y ≠ 0)
    (hFS : F ⊆ S) :
    IsConvexFace (axialProjection y '' S) (axialProjection y '' F) ↔ IsConvexFace S F := by
  have hsat : S ∩ axialProjection y ⁻¹' (axialProjection y '' F) = F := by
    ext x
    constructor
    · rintro ⟨hx, z, hz, heq⟩
      have hzx := axialProjection_injOn_level y L hy (hh z (hFS hz)) (hh x hx) heq
      exact hzx ▸ hz
    · intro hx
      exact ⟨hFS hx, x, hx, rfl⟩
  constructor
  · intro h
    exact hsat ▸ affineMap_preimage_face (axialProjection y).toLinearMap.toAffineMap hS h
  · intro h
    exact affineMap_image_face_of_saturated (axialProjection y).toLinearMap.toAffineMap hS h hsat

omit [FiniteDimensional ℝ E] in
/-- Actual vertices are preserved and reflected by the axis projection. -/
theorem axialProjection_extreme_iff {S : Set E} (hS : Convex ℝ S)
    (L : E →L[ℝ] ℝ) (hh : ∀ z ∈ S, L z = 1) {y : E} (hy : L y ≠ 0)
    {x : E} (hx : x ∈ S) :
    axialProjection y x ∈ (axialProjection y '' S).extremePoints ℝ ↔ x ∈ S.extremePoints ℝ := by
  rw [← singleton_face_iff_extremePoint, ← singleton_face_iff_extremePoint]
  have hf := axialProjection_face_iff hS L hh hy (singleton_subset_iff.mpr hx)
  simpa only [image_singleton] using hf

/-- Actual edges, not merely adjacency labels, survive the orthogonal
transport of the cutting polygon. -/
theorem axialProjection_edge_iff {S : Set E} (hS : FinitePolytope S)
    (L : E →L[ℝ] ℝ) (hh : ∀ z ∈ S, L z = 1) {y : E} (hy : L y ≠ 0)
    {x z : E} (hx : x ∈ S) (hz : z ∈ S) :
    Edge (axialProjection y '' S) (axialProjection y x) (axialProjection y z) ↔ Edge S x z := by
  have hc := finitePolytope_convex hS
  have hface := axialProjection_face_iff hc L hh hy (hc.segment_subset hx hz)
  have hseg : axialProjection y '' segment ℝ x z =
      segment ℝ (axialProjection y x) (axialProjection y z) :=
    image_segment ℝ (axialProjection y).toLinearMap.toAffineMap x z
  rw [hseg] at hface
  constructor
  · intro he
    refine ⟨(axialProjection_extreme_iff hc L hh hy hx).mp he.1,
      (axialProjection_extreme_iff hc L hh hy hz).mp he.2.1,
      fun hxz => he.2.2.1 (congrArg (axialProjection y) hxz), ?_⟩
    exact finitePolytope_face_isExposed hS (hface.mp (edge_isConvexFace he))
  · intro he
    refine ⟨(axialProjection_extreme_iff hc L hh hy hx).mpr he.1,
      (axialProjection_extreme_iff hc L hh hy hz).mpr he.2.1,
      fun hp => he.2.2.1 (axialProjection_injOn_level y L hy (hh x hx) (hh z hz) hp), ?_⟩
    exact finitePolytope_face_isExposed
      (finitePolytope_affineMap_image (axialProjection y).toLinearMap.toAffineMap hS)
      (hface.mpr (edge_isConvexFace he))

/-- A finite two-dimensional polytope around an interior origin has an
actual cyclic edge fan in its own ambient inner-product space. -/
theorem exists_intrinsic_edge_ray_fan {S : Set E} (hS : FinitePolytope S)
    (hdS : affineDimension S = 2) (h0 : (0 : E) ∈ intrinsicInterior ℝ S) :
    ∃ n : ℕ, ∃ u : ℕ → E,
      u '' Iio n = S.extremePoints ℝ ∧ Set.InjOn u (Iio n) ∧ u n = u 0 ∧
      (∀ i ≤ n, u i ≠ 0) ∧ (∀ i < n, Edge S (u i) (u (i + 1))) ∧
      Nonempty (SphericalFanData n (fun i => InnerProductGeometry.angle (u i) (u (i + 1)))) := by
  obtain ⟨f, Q, him, hf0, hQ, hdQ, hQ0⟩ := exists_centered_complex_polytope hS hdS h0
  obtain ⟨u, hrange, hinj, hcycle, hne, hedge, hfan⟩ :=
    exists_planar_intrinsic_edge_ray_fan hQ hdQ hQ0
  have hflinear (z : ℂ) : f.linearIsometry z = f z := by
    simpa only [vsub_eq_sub, sub_zero, hf0] using f.map_vsub z 0
  have hangle (i : ℕ) : InnerProductGeometry.angle (f (u i)) (f (u (i + 1))) =
      InnerProductGeometry.angle (u i) (u (i + 1)) := by
    rw [← hflinear, ← hflinear]
    exact f.linearIsometry.angle_map _ _
  refine ⟨(vertices Q hQ).card, fun i => f (u i), ?_, ?_, congrArg f hcycle, ?_, ?_, ?_⟩
  · rw [← image_image, hrange, embedding_extremePoints, him]
  · intro i hi j hj hij
    exact hinj hi hj (f.injective hij)
  · intro i hi hz
    apply hne i hi
    exact f.injective (hz.trans hf0.symm)
  · intro i hi
    exact him ▸ embedding_edge_image f (hedge i hi)
  · simpa only [hangle] using hfan

/-- The polygon in the plane orthogonal to the centroid axis has its
actual cyclic edge order and winding, derived from the interior pole. -/
theorem axialProjection_polygon_fan (hE : Module.finrank ℝ E = 3)
    {S : Set E} (hS : FinitePolytope S) (hdS : affineDimension S = 2)
    (L : E →L[ℝ] ℝ) (hh : ∀ z ∈ S, L z = 1)
    {y : E} (hy : L y ≠ 0) (hp : radialPoint L y ∈ intrinsicInterior ℝ S) :
    ∃ n : ℕ, ∃ u : ℕ → (ℝ ∙ y)ᗮ,
      u '' Iio n = (axialProjection y '' S).extremePoints ℝ ∧
      Set.InjOn u (Iio n) ∧ u n = u 0 ∧ (∀ i ≤ n, u i ≠ 0) ∧
      (∀ i < n, Edge (axialProjection y '' S) (u i) (u (i + 1))) ∧
      Nonempty (SphericalFanData n (fun i => InnerProductGeometry.angle (u i) (u (i + 1)))) := by
  obtain ⟨hT, hdT, h0⟩ := axialProjection_polygon_interior hE hS hdS L hh hy hp
  exact exists_intrinsic_edge_ray_fan hT hdT (interior_subset_intrinsicInterior h0)

omit [FiniteDimensional ℝ E] in
/-- The actual tangent projection is the usual orthogonal component. -/
theorem axialProjection_formula (y x : E) :
    (axialProjection y x : E) = x - (⟪y, x⟫ / ‖y‖ ^ 2) • y := by
  have hh := (ℝ ∙ y).orthogonalProjection_add_orthogonalProjection_orthogonal x
  rw [Submodule.orthogonalProjection_singleton] at hh
  change (⟪y, x⟫ / ‖y‖ ^ 2) • y + (axialProjection y x : E) = x at hh
  exact eq_sub_of_add_eq' hh

omit [FiniteDimensional ℝ E] in
/-- Spherical tangents to normalized rays are positive rescalings of the
orthogonal tangent-plane vectors whenever the original ray is nonzero. -/
theorem sphericalTangent_normalized_eq_axialProjection (y x : E) :
    sphericalTangent (‖y‖⁻¹ • y) (‖x‖⁻¹ • x) =
      ‖x‖⁻¹ • (axialProjection y x : E) := by
  rw [sphericalTangent, axialProjection_formula]
  simp only [real_inner_smul_left, real_inner_smul_right, smul_sub, smul_smul]
  congr 1
  congr 1
  rw [real_inner_comm x y]
  simp only [div_eq_mul_inv, inv_pow, pow_two]
  ring

noncomputable local instance (G : Set E) : DecidableEq (affineSpan ℝ G).directionᗮ := Classical.decEq _

/-- The genuine transverse tangent polygon has a cyclic enumeration of
all its actual vertices and edges, and the required angular winding. -/
theorem unitUniform5_transverse_tangent_fan {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) {c : Space 5} (hc : c ∈ G) :
    let hPP := uniform_finitePolytope hP.1
    let y := transverseProjection G c (vertexCentroid (vertices P hPP))
    let T := axialProjection y '' transverseLink hPP hG.1 hc
    ∃ n : ℕ, ∃ u : ℕ → (ℝ ∙ y)ᗮ,
      u '' Iio n = T.extremePoints ℝ ∧ Set.InjOn u (Iio n) ∧ u n = u 0 ∧
      (∀ i ≤ n, u i ≠ 0) ∧ (∀ i < n, Edge T (u i) (u (i + 1))) ∧
      Nonempty (SphericalFanData n (fun i => InnerProductGeometry.angle (u i) (u (i + 1)))) := by
  dsimp only
  let hPP := uniform_finitePolytope hP.1
  have hfull := uniform_affineSpan_eq_top hP.1
  have hproper : affineDimension G < affineDimension P := by
    rw [hG.2.1, uniform_dimension hP.1]
    norm_num
  obtain ⟨hpos, hp⟩ := transverseCentroidPole_mem_intrinsicInterior hPP hfull hG.1 hc hproper
  obtain ⟨hS, hdS⟩ := unitUniform5_transverseLink hP hG hc
  have hE : Module.finrank ℝ (affineSpan ℝ G).directionᗮ = 3 := by
    have hh := (affineSpan ℝ G).direction.finrank_add_finrank_orthogonal
    have hdG := hG.2.1
    change Module.finrank ℝ (affineSpan ℝ G).direction = 2 at hdG
    have hdAmbient : Module.finrank ℝ (Space 5) = 5 := by simp [Space]
    omega
  exact axialProjection_polygon_fan hE hS hdS (transverseCutHeight hPP hG.1 hc)
    (fun z hz => hz.2) hpos.ne' hp

end Uniform5.Composition
