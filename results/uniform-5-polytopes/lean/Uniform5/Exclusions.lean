import Uniform5.Closure
import Mathlib.Data.Finset.Max

/-! Exact flat and degenerate exclusions (`lem:closure(d)`, `lem:exclusions`).
The supporting functional is proper, and the centre is genuinely interior;
the strict supporting inequality is derived rather than supplied.
-/
noncomputable section
namespace Uniform5
open Set
open scoped RealInnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A proper supporting functional is strictly below its bound at every
interior point. The existence of a nonzero value expresses properness. -/
theorem strict_support_of_interior [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (hL : ∃ x, L x ≠ 0)
    {P : Set E} {c : E} {b : ℝ}
    (hsupport : ∀ x ∈ P, L x ≤ b) (hc : c ∈ interior P) : L c < b := by
  have hsurj : Function.Surjective L := by
    obtain ⟨x, hx⟩ := hL
    intro y
    refine ⟨(y / L x) • x, ?_⟩
    simp [hx]
  have hm : L c ∈ interior (Set.Iic b) :=
    center_mem_interior_linear_cone L hsurj (by
      rintro _ ⟨x, hx, rfl⟩
      exact hsupport x hx) hc
  simpa only [interior_Iic, mem_Iio] using hm

/-- A centre on a supporting facet hyperplane contradicts strict interiority. -/
theorem center_not_on_facet_hyperplane [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (hL : ∃ x, L x ≠ 0)
    {P : Set E} {c : E} {b : ℝ}
    (hsupport : ∀ x ∈ P, L x ≤ b) (hc : c ∈ interior P) : L c ≠ b :=
  ne_of_lt (strict_support_of_interior L hL hsupport hc)

/-- Projection orthogonality gives the squared radius decomposition used for
cells and facets. Both radii are actual distances, not free algebraic values. -/
theorem orthogonal_radius_decomposition {c o x : E} {R r : ℝ}
    (hR : ‖x - c‖ = R) (hr : ‖x - o‖ = r)
    (horth : ⟪x - o, c - o⟫ = 0) :
    R ^ 2 = r ^ 2 + ‖c - o‖ ^ 2 := by
  have heq : x - c = (x - o) - (c - o) := by abel
  have h := norm_sub_sq_real (x - o) (c - o)
  rw [← heq, hR, hr, horth] at h
  linarith

/-- The distance form of the same decomposition, used for h and cell offsets. -/
theorem orthogonal_radius_distance {c o x : E} {R r : ℝ}
    (hR : ‖x - c‖ = R) (hr : ‖x - o‖ = r)
    (horth : ⟪x - o, c - o⟫ = 0) :
    ‖c - o‖ = Real.sqrt (R ^ 2 - r ^ 2) := by
  have hd := orthogonal_radius_decomposition hR hr horth
  have heq : R ^ 2 - r ^ 2 = ‖c - o‖ ^ 2 := by linarith
  rw [heq, Real.sqrt_sq (norm_nonneg _)]

/-- Part (d): a facet's circumradius is strictly less than the full radius.
Projection geometry supplies the decomposition; strictness is topological. -/
theorem facet_radius_lt [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (hL : ∃ x, L x ≠ 0)
    {P : Set E} {c o : E} {b R r : ℝ}
    (hsupport : ∀ x ∈ P, L x ≤ b) (hc : c ∈ interior P)
    (ho : L o = b) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hdecomp : R ^ 2 = r ^ 2 + ‖c - o‖ ^ 2) : r < R := by
  have hco : c ≠ o := by
    intro heq
    exact center_not_on_facet_hyperplane L hL hsupport hc (heq ▸ ho)
  have hpos : 0 < ‖c - o‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hco)
  nlinarith [sq_pos_of_pos hpos]

/-- Geometric form of part (d), deriving the radius decomposition from one
common sphere point and the projection orthogonality of the facet centre. -/
theorem facet_radius_lt_of_projection [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (hL : ∃ y, L y ≠ 0)
    {P : Set E} {c o x : E} {b R r : ℝ}
    (hsupport : ∀ y ∈ P, L y ≤ b) (hc : c ∈ interior P)
    (ho : L o = b) (hR : ‖x - c‖ = R) (hr : ‖x - o‖ = r)
    (horth : ⟪x - o, c - o⟫ = 0) : r < R :=
  facet_radius_lt L hL hsupport hc ho
    (hR ▸ norm_nonneg (x - c)) (hr ▸ norm_nonneg (x - o))
    (orthogonal_radius_decomposition hR hr horth)

/-- A flat cycle is inconsistent with the polar spherical geometry. -/
theorem flat_cycle_excluded {ι : Type*} [Fintype ι] {α : ι → ℝ}
    (polar : PolarPolygonData α) : (∑ i, α i) ≠ 2 * Real.pi :=
  ne_of_lt (strict_spherical_perimeter polar)

/-- Equality with the maximum facet radius is impossible: the finite maximum
is attained. No interval approximations enter this exclusion. -/
theorem degenerate_maximum_excluded {ι : Type*} [DecidableEq ι]
    (facets : Finset ι) (hne : facets.Nonempty) (radius : ι → ℝ) (R : ℝ)
    (hstrict : ∀ f ∈ facets, radius f < R) :
    facets.sup' hne radius < R := by
  exact (Finset.sup'_lt_iff hne).mpr hstrict

/-- Direct exact-equality form of the degenerate-root exclusion. -/
theorem degenerate_root_excluded {ι : Type*} [DecidableEq ι]
    (facets : Finset ι) (hne : facets.Nonempty) (radius : ι → ℝ) (R : ℝ)
    (hstrict : ∀ f ∈ facets, radius f < R) :
    R ≠ facets.sup' hne radius :=
  ne_of_gt (degenerate_maximum_excluded facets hne radius R hstrict)

end Uniform5
