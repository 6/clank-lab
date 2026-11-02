import BaseREhrhart.Decomposition

/-! The six specified points form a genuine
five-dimensional simplex. The explicit lifted inverse also establishes
this independence, without a certificate premise. -/

noncomputable section
open scoped BigOperators
namespace BaseREhrhart

theorem vertices_affineIndependent :
    AffineIndependent ℝ (simplexVertex (fun i => (coefficients i : ℝ))) := by
  apply (affineIndependent_iff_of_fintype ℝ _).mpr
  intro w hw hv
  have hv' : ∑ j, w j • simplexVertex (fun i => (coefficients i : ℝ)) j = 0 := by
    simpa [Finset.weightedVSub_eq_linear_combination Finset.univ hw] using hv
  have hcoord : ∀ i : Fin 5, w i.succ = (coefficients i : ℝ) * w 0 := by
    intro i
    have h := congrFun hv' i
    rw [sum_vertex] at h
    exact sub_eq_zero.mp h
  have hs : (D : ℝ) * w 0 = 0 := by
    rw [Fin.sum_univ_succ] at hw
    simp_rw [hcoord] at hw
    rw [← Finset.sum_mul] at hw
    linear_combination hw - w 0 * coefficients_sum_real
  have h0 : w 0 = 0 := (mul_eq_zero.mp hs).resolve_left (by norm_num [D])
  intro j
  refine Fin.cases h0 (fun i => ?_) j
  rw [hcoord, h0, mul_zero]

end BaseREhrhart
