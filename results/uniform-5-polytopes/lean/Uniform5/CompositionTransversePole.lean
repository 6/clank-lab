import Uniform5.CompositionTransverseLink
import Uniform5.CompositionPlanarFanEdges
import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual projected parent centroid supplies an interior pole of the
transverse link; its interior position is derived from the finite hull. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped BigOperators Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ambient interior points normalize to relatively interior points of
the actual section. This uses a neighborhood in the section's affine span. -/
theorem finiteHull_radialPoint_mem_intrinsicInterior (V : Finset E) (hz : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hh : ∀ z ∈ V.erase 0, 1 ≤ L z)
    {y : E} (hy : y ∈ interior (convexHull ℝ (V : Set E))) (hLy : 0 < L y) :
    radialPoint L y ∈ intrinsicInterior ℝ (heightSection (convexHull ℝ (V : Set E)) L) := by
  let S := heightSection (convexHull ℝ (V : Set E)) L
  let A := affineSpan ℝ S
  have hrS : radialPoint L y ∈ S :=
    finiteHull_radialPoint_mem_section V hz L hh (interior_subset hy) hLy
  let r : A := ⟨radialPoint L y, subset_affineSpan ℝ S hrS⟩
  refine ⟨r, ?_, rfl⟩
  have hlevel : ∀ z : A, L (z : E) = 1 := by
    intro z
    have hle : A ≤ (affineSpan ℝ ({1} : Set ℝ)).comap L.toLinearMap.toAffineMap :=
      affineSpan_le.mpr (fun x hx => by simpa using hx.2)
    simpa using hle z.property
  have hcont : Continuous (fun z : A => L y • (z : E)) := continuous_const.smul continuous_subtype_val
  have hr : L y • (r : E) = y := by simp [r, radialPoint, smul_smul, hLy.ne']
  have hn := (hcont.tendsto r).eventually (mem_interior_iff_mem_nhds.mp (hr ▸ hy))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hn] with z hzQ
  have hheight : 0 < L (L y • (z : E)) := by simpa [hlevel z] using hLy
  have hm := finiteHull_radialPoint_mem_section V hz L hh hzQ hheight
  simpa [radialPoint, map_smul, hlevel z, smul_smul, hLy.ne'] using hm

variable [FiniteDimensional ℝ E]

/-- Transverse projection is an open map, so an actual parent interior
point remains interior in the full transverse space. -/
theorem transverseProjection_isOpenMap (G : Set E) (c : E) :
    IsOpenMap (transverseProjection G c) := by
  have hsurj : Function.Surjective (affineSpan ℝ G).directionᗮ.orthogonalProjection := by
    intro z
    exact ⟨z, Submodule.orthogonalProjection_mem_subspace_eq_self z⟩
  have hp := (affineSpan ℝ G).directionᗮ.orthogonalProjection.isOpenMap hsurj
  exact hp.comp (Homeomorph.addLeft (-c)).isOpenMap

/-- A positive-height section functional is strictly positive at every
ambient interior point of its nontrivial finite apex hull. -/
theorem finitePolytope_cutHeight_pos_of_interior {Q : Set E} (hQ : FinitePolytope Q)
    (hz : (0 : E) ∈ Q.extremePoints ℝ) (L : E →L[ℝ] ℝ)
    (hh : ∀ z ∈ (vertices Q hQ).erase 0, 1 ≤ L z)
    (hd : 0 < affineDimension Q) {y : E} (hy : y ∈ interior Q) : 0 < L y := by
  obtain ⟨z, hzS⟩ := finitePolytope_nonempty
    (finitePolytope_heightSection_finite_dimension hQ hz L hh hd).1
  have hsurj : Function.Surjective L := fun a => ⟨a • z, by simp [hzS.2]⟩
  have hnonneg : Q ⊆ {z | 0 ≤ L z} := by
    rw [← convexHull_vertices hQ]
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).linear_preimage L.toLinearMap)
    intro z hzV
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact le_trans zero_le_one (hh z (Finset.mem_erase.mpr ⟨hz0, hzV⟩))
  have hi := L.isOpenMap hsurj |>.image_interior_subset Q (mem_image_of_mem L hy)
  have hsub : L '' Q ⊆ Ici (0 : ℝ) := by rintro _ ⟨z, hzQ, rfl⟩; exact hnonneg hzQ
  have hi' := interior_mono hsub hi
  simpa only [interior_Ici, mem_Ioi] using hi'

noncomputable local instance (G : Set E) : DecidableEq (affineSpan ℝ G).directionᗮ := Classical.decEq _

/-- The parent vertex centroid, projected transversely and normalized to
the chosen cutting plane. -/
noncomputable def transverseCentroidPole {P G : Set E} (hP : FinitePolytope P)
    (hG : IsConvexFace P G) {c : E} (hc : c ∈ G) : (affineSpan ℝ G).directionᗮ :=
  radialPoint (transverseCutHeight hP hG hc)
    (transverseProjection G c (vertexCentroid (vertices P hP)))

/-- The actual projected centroid has positive height, and its normalized
point is relatively interior in the transverse link. -/
theorem transverseCentroidPole_mem_intrinsicInterior {P G : Set E} (hP : FinitePolytope P)
    (hfull : affineSpan ℝ P = ⊤) (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (hd : affineDimension G < affineDimension P) :
    0 < transverseCutHeight hP hG hc
      (transverseProjection G c (vertexCentroid (vertices P hP))) ∧
    transverseCentroidPole hP hG hc ∈ intrinsicInterior ℝ (transverseLink hP hG hc) := by
  let Q := transverseProjection G c '' P
  let hQ := finitePolytope_transverse hP G c
  let y := transverseProjection G c (vertexCentroid (vertices P hP))
  have hcent : vertexCentroid (vertices P hP) ∈ interior P := by
    rw [← intrinsicInterior_eq_interior_of_full_span hfull]
    exact vertexCentroid_mem_intrinsicInterior hP
  have hy : y ∈ interior Q :=
    (transverseProjection_isOpenMap G c).image_interior_subset P (mem_image_of_mem _ hcent)
  have hdim := transverse_image_dimension_add hG.2.1 c
  have hpos := finitePolytope_cutHeight_pos_of_interior hQ
    (transverse_origin_extreme hP hG hc) (transverseCutHeight hP hG hc)
    (transverseCutHeight_ge_one hP hG hc) (by omega) hy
  refine ⟨hpos, ?_⟩
  have hh := finiteHull_radialPoint_mem_intrinsicInterior (vertices Q hQ)
    ((mem_vertices hQ 0).mpr (transverse_origin_extreme hP hG hc))
    (transverseCutHeight hP hG hc) (transverseCutHeight_ge_one hP hG hc)
    (by simpa only [convexHull_vertices] using hy) hpos
  simpa only [convexHull_vertices, Q, transverseCentroidPole, transverseLink, y] using hh

/-- The raw projected centroid is a strictly positive multiple of the
chosen pole, whose cutting height is exactly one. -/
theorem transverseCentroidPole_normalization {P G : Set E} (hP : FinitePolytope P)
    (hfull : affineSpan ℝ P = ⊤) (hG : IsConvexFace P G) {c : E} (hc : c ∈ G)
    (hd : affineDimension G < affineDimension P) :
    let y := transverseProjection G c (vertexCentroid (vertices P hP))
    let L := transverseCutHeight hP hG hc
    0 < L y ∧ L (transverseCentroidPole hP hG hc) = 1 ∧
      y = L y • transverseCentroidPole hP hG hc ∧ transverseCentroidPole hP hG hc ≠ 0 := by
  dsimp only
  have hp := (transverseCentroidPole_mem_intrinsicInterior hP hfull hG hc hd).1
  have hn : transverseCutHeight hP hG hc (transverseCentroidPole hP hG hc) = 1 :=
    linear_radialPoint _ hp.ne'
  refine ⟨hp, hn, ?_, ?_⟩
  · simp only [transverseCentroidPole, radialPoint, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  · intro hz
    rw [hz, map_zero] at hn
    norm_num at hn

/-- A two-dimensional actual finite polytope with a specified relative
interior point has an isometric complex model centered at that point. -/
theorem exists_centered_complex_polytope {P : Set E} (hP : FinitePolytope P)
    (hd : affineDimension P = 2) {c : E} (hc : c ∈ intrinsicInterior ℝ P) :
    ∃ f : ℂ →ᵃⁱ[ℝ] E, ∃ Q : Set ℂ, f '' Q = P ∧ f 0 = c ∧
      FinitePolytope Q ∧ affineDimension Q = 2 ∧ (0 : ℂ) ∈ intrinsicInterior ℝ Q := by
  obtain ⟨f, Q, him, hf0, hQ, hdQ, h0, _⟩ :=
    exists_finitePolytope_centered_intrinsic_model P hP 2 hd c hc
  let e : ℂ ≃ᵃⁱ[ℝ] Space 2 := Complex.orthonormalBasisOneI.repr.toAffineIsometryEquiv
  let R := e.symm '' Q
  have he0 : e 0 = 0 := map_zero Complex.orthonormalBasisOneI.repr
  have hes0 : e.symm 0 = 0 := map_zero Complex.orthonormalBasisOneI.repr.symm
  refine ⟨f.comp e.toAffineIsometry, R, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (f.comp e.toAffineIsometry) '' R = f '' (e '' (e.symm '' Q)) :=
        (Set.image_image f e (e.symm '' Q)).symm
      _ = P := by simpa only [image_image, e.apply_symm_apply, image_id] using him
  · change f (e 0) = c
    rwa [he0]
  · exact finitePolytope_affineMap_image e.symm.toAffineMap hQ
  · exact (affineDimension_affineIsometry_image e.symm.toAffineIsometry Q).trans hdQ
  · have hh := mem_image_of_mem e.symm h0
    change e.symm.toAffineIsometry 0 ∈ e.symm.toAffineIsometry '' intrinsicInterior ℝ Q at hh
    rw [← e.symm.toAffineIsometry.image_intrinsicInterior] at hh
    change e.symm 0 ∈ intrinsicInterior ℝ R at hh
    rw [hes0] at hh
    exact hh

/-- An actual polygon face of a uniform five-polytope has a genuine
complex planar link centered at the normalized projected parent centroid. -/
theorem unitUniform5_transverseLink_complex_model {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) {c : Space 5} (hc : c ∈ G) :
    ∃ f : ℂ →ᵃⁱ[ℝ] (affineSpan ℝ G).directionᗮ, ∃ Q : Set ℂ,
      f '' Q = transverseLink (uniform_finitePolytope hP.1) hG.1 hc ∧
      f 0 = transverseCentroidPole (uniform_finitePolytope hP.1) hG.1 hc ∧
      FinitePolytope Q ∧ affineDimension Q = 2 ∧ (0 : ℂ) ∈ intrinsicInterior ℝ Q := by
  obtain ⟨hS, hdS⟩ := unitUniform5_transverseLink hP hG hc
  apply exists_centered_complex_polytope hS hdS
  apply (transverseCentroidPole_mem_intrinsicInterior (uniform_finitePolytope hP.1)
    (uniform_affineSpan_eq_top hP.1) hG.1 hc ?_).2
  rw [hG.2.1, uniform_dimension hP.1]
  norm_num

end Uniform5.Composition
