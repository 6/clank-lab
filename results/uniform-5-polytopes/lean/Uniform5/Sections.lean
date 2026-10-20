import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Slicing a pyramid at its base, including the all-neighbours case of `lem:vf`. -/
namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the base lies in one level hyperplane and the added point lies strictly
above it, the intersection of their convex hull with that hyperplane is exactly
the convex hull of the base. The base need not be finite or nonempty. -/
theorem convexHull_insert_section (S : Set E) (v : E) (L : E →L[ℝ] ℝ) (b : ℝ)
    (hS : ∀ x ∈ S, L x = b) (hv : b < L v) :
    {x ∈ convexHull ℝ (insert v S) | L x = b} = convexHull ℝ S := by
  have hplane : Convex ℝ {x : E | L x = b} := by
    intro x hx y hy a d ha hd had
    change L x = b at hx
    change L y = b at hy
    change L (a • x + d • y) = b
    simp only [map_add, map_smul, smul_eq_mul, hx, hy]
    linear_combination b * had
  have hHull : ∀ x ∈ convexHull ℝ S, L x = b :=
    convexHull_min hS hplane
  by_cases hne : S.Nonempty
  · ext x
    constructor
    · rintro ⟨hx, hLx⟩
      rw [convexHull_insert hne] at hx
      rcases mem_convexJoin.mp hx with ⟨w, hw, y, hy, hxy⟩
      have hwv : w = v := Set.mem_singleton_iff.mp hw
      subst w
      rcases hxy with ⟨a, d, ha, hd, had, heq⟩
      have heval := congrArg L heq
      simp only [map_add, map_smul, smul_eq_mul, hLx, hHull y hy] at heval
      have hprod : a * (L v - b) = 0 := by
        linear_combination heval - b * had
      have ha0 : a = 0 := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (sub_pos.mpr hv))
      have hd1 : d = 1 := by linarith
      have hyx : y = x := by simpa only [ha0, hd1, zero_smul, one_smul, zero_add] using heq
      exact hyx ▸ hy
    · intro hx
      exact ⟨convexHull_mono (Set.subset_insert v S) hx, hHull x hx⟩
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst S
    simp only [insert_empty_eq, convexHull_singleton, convexHull_empty]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro hx
    subst x
    exact ne_of_gt hv

/-- The finite all-neighbours slice: deleting the distinguished vertex gives
exactly the vertices whose convex hull is the section. -/
theorem finite_vertex_section [DecidableEq E] (V : Finset E) (v : E)
    (L : E →L[ℝ] ℝ) (b : ℝ) (hvV : v ∈ V)
    (hbase : ∀ x ∈ V.erase v, L x = b) (hv : b < L v) :
    {x ∈ convexHull ℝ (V : Set E) | L x = b} =
      convexHull ℝ (V.erase v : Set E) := by
  have hV : (V : Set E) = insert v (V.erase v : Set E) := by
    rw [← Finset.coe_insert, Finset.insert_erase hvV]
  rw [hV]
  exact convexHull_insert_section (V.erase v : Set E) v L b hbase hv

end Uniform5
