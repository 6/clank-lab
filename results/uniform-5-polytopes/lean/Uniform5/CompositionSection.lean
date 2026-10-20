import Uniform5.CompositionRadialEdges
import Mathlib.Analysis.Convex.Combination

/-!
# Radial hyperplane sections of actual finite convex hulls

The section formula is proved by reweighting convex combinations. The
generators may occur at different heights; no assumption that all deleted
vertices lie in the cutting plane is used.
-/

noncomputable section

namespace Uniform5.Composition

open Set Classical
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cutting a finite hull above its zero vertex amounts to projecting each
other generator radially to height one. -/
theorem finiteHull_radial_section (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ z ∈ V.erase 0, 1 ≤ L z) :
    {x ∈ convexHull ℝ (V : Set E) | L x = 1} =
      convexHull ℝ ((fun z : E => (L z)⁻¹ • z) '' (V.erase 0 : Set E)) := by
  classical
  let T := V.erase 0
  let r : E → E := fun z => (L z)⁻¹ • z
  have hpos (z : E) (hz : z ∈ T) : 0 < L z := lt_of_lt_of_le zero_lt_one (hheight z hz)
  have hr (z : E) (hz : z ∈ T) : L (r z) = 1 := by
    simp [r, (hpos z hz).ne']
  have hsub : r '' (T : Set E) ⊆ {x ∈ convexHull ℝ (V : Set E) | L x = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, hr z hz⟩
    have ht0 : 0 ≤ (L z)⁻¹ := inv_nonneg.mpr (hpos z hz).le
    have ht1 : (L z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hheight z hz)
    have hh := (convex_convexHull ℝ (V : Set E))
      (subset_convexHull ℝ (V : Set E) hzero)
      (subset_convexHull ℝ (V : Set E) (Finset.mem_erase.mp hz).2)
      (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 (L z)⁻¹)
    simpa [r] using hh
  have hconv : Convex ℝ {x ∈ convexHull ℝ (V : Set E) | L x = 1} :=
    (convex_convexHull ℝ (V : Set E)).inter
      ((convex_singleton (1 : ℝ)).linear_preimage L.toLinearMap)
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxL⟩
    obtain ⟨w, hw, hsum, hxw⟩ := Finset.mem_convexHull'.mp hx
    let a : E → ℝ := fun z => w z * L z
    have hsuma : ∑ z ∈ T, a z = 1 := by
      have hsumV : ∑ z ∈ V, a z = 1 := by
        calc
          ∑ z ∈ V, a z = L (∑ z ∈ V, w z • z) := by
            simp [a, map_sum, mul_comm]
          _ = 1 := by rw [hxw, hxL]
      simpa [T, a] using (Finset.sum_erase_add V (fun z => a z) hzero).trans hsumV
    have hsumr : ∑ z ∈ T, a z • r z = x := by
      calc
        ∑ z ∈ T, a z • r z = ∑ z ∈ T, w z • z := by
          apply Finset.sum_congr rfl
          intro z hz
          simp [a, r, smul_smul, (hpos z hz).ne']
        _ = ∑ z ∈ V, w z • z := by
          simpa [T] using Finset.sum_erase_add V (fun z => w z • z) hzero
        _ = x := hxw
    have hcm := Finset.centerMass_mem_convexHull (s := r '' (T : Set E)) T
      (w := a) (z := r)
      (fun z hz => mul_nonneg (hw z (Finset.mem_erase.mp hz).2) (hpos z hz).le)
      (by rw [hsuma]; exact zero_lt_one)
      (fun z hz => ⟨z, hz, rfl⟩)
    rw [Finset.centerMass_eq_of_sum_1 T r hsuma, hsumr] at hcm
    exact hcm
  · exact convexHull_min hsub hconv

/-- When each actual edge endpoint has height one, the section is precisely
the hull of the adjacent vertices. This conclusion is not an input to the
definition of a geometric vertex figure. -/
theorem finiteHull_section_eq_convexHull_edges
    (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hheight : ∀ z ∈ V.erase 0, 1 ≤ L z)
    (hedge : ∀ z, IsEdge V 0 z → L z = 1) :
    {x ∈ convexHull ℝ (V : Set E) | L x = 1} =
      convexHull ℝ {z | IsEdge V 0 z} := by
  classical
  let B := (V.erase 0).image (radialPoint L)
  have hsection : {x ∈ convexHull ℝ (V : Set E) | L x = 1} =
      convexHull ℝ (B : Set E) := by
    simpa only [B, Finset.coe_image, radialPoint] using
      finiteHull_radial_section V hzero L hheight
  have hcompact : IsCompact (convexHull ℝ (B : Set E)) := B.finite_toSet.isCompact_convexHull
  have hfinite : ((convexHull ℝ (B : Set E)).extremePoints ℝ).Finite :=
    B.finite_toSet.subset extremePoints_convexHull_subset
  have hverticesHull : convexHull ℝ (B : Set E) =
      convexHull ℝ ((convexHull ℝ (B : Set E)).extremePoints ℝ) := by
    have hk := closure_convexHull_extremePoints hcompact (convex_convexHull ℝ (B : Set E))
    rw [hfinite.isCompact_convexHull.isClosed.closure_eq] at hk
    exact hk.symm
  apply Set.Subset.antisymm
  · rw [hsection, hverticesHull]
    apply convexHull_mono
    intro y hy
    obtain ⟨z, hz, hzy, he⟩ := radial_extreme_isEdge V hzero hvertices L
      (fun z hz => lt_of_lt_of_le zero_lt_one (hheight z hz)) hy
    have hzL := hedge z he
    have : z = y := by simpa [radialPoint, hzL] using hzy
    exact this ▸ he
  · apply convexHull_min
    · intro z hz
      exact ⟨subset_convexHull ℝ (V : Set E) hz.2.1, hedge z hz⟩
    · exact (convex_convexHull ℝ (V : Set E)).inter
        ((convex_singleton (1 : ℝ)).linear_preimage L.toLinearMap)

/-- The linear height of a sphere through the origin. -/
noncomputable def sphereHeight (c : E) : E →L[ℝ] ℝ := (2 : ℝ) • innerSL ℝ c

theorem sphereHeight_eq_norm_sq {c x : E}
    (hx : ‖x - c‖ ^ 2 = ‖c‖ ^ 2) : sphereHeight c x = ‖x‖ ^ 2 := by
  simp only [norm_sub_sq_real] at hx
  simp only [sphereHeight, ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul]
  rw [real_inner_comm]
  linarith

/-- Unit-edge cospherical polytopes have their actual neighbor hull as the
unit-height vertex-figure section at the origin. -/
theorem cospherical_unit_section
    (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (c : E) (R : ℝ) (hsphere : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : ∀ x y, IsEdge V x y → dist x y = 1) :
    {x ∈ convexHull ℝ (V : Set E) | sphereHeight c x = 1} =
      convexHull ℝ {z | IsEdge V 0 z} := by
  have hc : ‖c‖ ^ 2 = R ^ 2 := by simpa using hsphere 0 hzero
  have hL (x : E) (hx : x ∈ V) : sphereHeight c x = ‖x‖ ^ 2 :=
    sphereHeight_eq_norm_sq ((hsphere x hx).trans hc.symm)
  apply finiteHull_section_eq_convexHull_edges V hzero hvertices (sphereHeight c)
  · intro z hz
    rw [hL z (Finset.mem_erase.mp hz).2]
    have hsep := unit_edges_separated V hsphere hunit hzero (Finset.mem_erase.mp hz).2
      (Finset.mem_erase.mp hz).1.symm
    simp only [dist_zero_left] at hsep
    nlinarith
  · intro z hz
    rw [hL z hz.2.1]
    have hlen := hunit 0 z hz
    simp only [dist_zero_left] at hlen
    rw [hlen]
    norm_num

end Uniform5.Composition
