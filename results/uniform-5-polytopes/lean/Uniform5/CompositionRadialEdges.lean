import Uniform5.CompositionFaces

/-!
# Radial vertex figures and actual exposed edges

Radial normalization at a vertex preserves distinct actual vertex rays.
A supporting functional of a radial hull vertex pulls back to an exposing
functional of the corresponding edge of the original finite polytope.
-/

noncomputable section

namespace Uniform5.Composition

open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalize a ray to the affine hyperplane where `L` takes value one. -/
noncomputable def radialPoint (L : E →L[ℝ] ℝ) (x : E) : E := (L x)⁻¹ • x

@[simp] theorem linear_radialPoint (L : E →L[ℝ] ℝ) {x : E} (hx : L x ≠ 0) :
    L (radialPoint L x) = 1 := by simp [radialPoint, hx]

theorem radialPoint_recover (L : E →L[ℝ] ℝ) {x : E} (hx : L x ≠ 0) :
    L x • radialPoint L x = x := by simp [radialPoint, smul_smul, hx]

/-- Distinct actual vertices other than the origin have distinct positive
rays from the origin. -/
theorem radialPoint_injOn (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hpos : ∀ x ∈ V.erase 0, 0 < L x) :
    Set.InjOn (radialPoint L) (V.erase 0 : Set E) := by
  classical
  have one_direction {x y : E} (hx : x ∈ V.erase 0) (hy : y ∈ V.erase 0)
      (hxy : radialPoint L x = radialPoint L y) (hle : L x ≤ L y) : x = y := by
    have hxpos := hpos x hx
    have hypos := hpos y hy
    have hratio : x = (L x / L y) • y := by
      calc
        x = L x • radialPoint L x := (radialPoint_recover L hxpos.ne').symm
        _ = L x • radialPoint L y := by rw [hxy]
        _ = (L x / L y) • y := by rw [radialPoint, smul_smul, div_eq_mul_inv]
    have hsegment : x ∈ segment ℝ (0 : E) y := by
      refine ⟨1 - L x / L y, L x / L y, ?_, ?_, by ring, ?_⟩
      · exact sub_nonneg.mpr ((div_le_one hypos).mpr hle)
      · exact div_nonneg hxpos.le hypos.le
      · simpa only [smul_zero, zero_add] using hratio.symm
    have hends := (mem_extremePoints_iff_forall_segment.mp
      (hvertices x (Finset.mem_erase.mp hx).2)).2
      0 (subset_convexHull ℝ (V : Set E) hzero)
      y (subset_convexHull ℝ (V : Set E) (Finset.mem_erase.mp hy).2) hsegment
    exact (hends.resolve_left (Finset.mem_erase.mp hx).1.symm).symm
  intro x hx y hy hxy
  rcases le_total (L x) (L y) with hle | hle
  · exact one_direction hx hy hxy hle
  · exact (one_direction hy hx hxy.symm hle).symm

/-- Every vertex of the radial hull comes from an actual exposed edge at
the origin. The new exposing functional vanishes at precisely its endpoints. -/
theorem radial_extreme_isEdge (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hpos : ∀ x ∈ V.erase 0, 0 < L x)
    {y : E} (hy : y ∈ (convexHull ℝ
      (((V.erase 0).image (radialPoint L)) : Set E)).extremePoints ℝ) :
    ∃ x ∈ V.erase 0, radialPoint L x = y ∧ IsEdge V 0 x := by
  classical
  have hyS := extremePoints_convexHull_subset hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyS
  obtain ⟨M, hM⟩ := finite_extreme_strict_support ((V.erase 0).image (radialPoint L)) hy
  let N : E →L[ℝ] ℝ := M - (M (radialPoint L x)) • L
  have hNx : N x = 0 := by
    have hxrecover := congrArg M (radialPoint_recover L (hpos x hx).ne')
    simp only [map_smul, smul_eq_mul] at hxrecover
    change M x - M (radialPoint L x) * L x = 0
    nlinarith [hxrecover]
  have hNstrict : ∀ z ∈ V, z ≠ 0 → z ≠ x → N z < 0 := by
    intro z hz hz0 hzx
    have hz' : z ∈ V.erase 0 := Finset.mem_erase.mpr ⟨hz0, hz⟩
    have hrad : radialPoint L z ≠ radialPoint L x := by
      intro heq
      exact hzx (radialPoint_injOn V hzero hvertices L hpos hz' hx heq)
    have hless := hM (radialPoint L z) (Finset.mem_image.mpr ⟨z, hz', rfl⟩) hrad
    have hzrecover := congrArg M (radialPoint_recover L (hpos z hz').ne')
    simp only [map_smul, smul_eq_mul] at hzrecover
    change M z - M (radialPoint L x) * L z < 0
    have hscaled := mul_lt_mul_of_pos_left hless (hpos z hz')
    nlinarith [hzrecover]
  refine ⟨x, hx, rfl, hzero, (Finset.mem_erase.mp hx).2,
    (Finset.mem_erase.mp hx).1.symm, ?_⟩
  apply exposes_segment (S := (V : Set E)) hzero (Finset.mem_erase.mp hx).2 N 0
    (map_zero N) hNx
  · intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    by_cases hzx : z = x
    · simpa [hzx] using hNx.le
    exact (hNstrict z hz hz0 hzx).le
  · intro z hz heq
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    by_cases hzx : z = x
    · exact Or.inr hzx
    exact False.elim ((ne_of_lt (hNstrict z hz hz0 hzx)) heq)

end Uniform5.Composition
