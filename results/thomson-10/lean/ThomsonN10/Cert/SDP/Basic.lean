/- Adapted from global-soundness/n10/project/Thomson10Soundness/Basic.lean; N9 source proof/lean/ThomsonN9/CentroidBound.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Interfaces
namespace ThomsonN10.Cert
open ThomsonN10.Interfaces
theorem pair_distance_pos {x : Configuration} (hx : IsSphereConfiguration x)
    {i j : Fin 10} (hij : i ≠ j) : 0 < ‖x i-x j‖ := by
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hij (hx.2 h)))

theorem twice_pairSum (f : Fin 10 → Fin 10 → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    2 * pairSum f = ∑ i, ∑ j, f i j := by
  classical
  have hterm (i j : Fin 10) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simp [hd]
    · simp [h, not_lt_of_ge h.le]
  have hup : (∑ i : Fin 10, ∑ j : Fin 10, if i < j then f i j else 0) = pairSum f := by
    unfold pairSum
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have hlo : (∑ i : Fin 10, ∑ j : Fin 10, if j < i then f i j else 0) = pairSum f := by
    rw [Finset.sum_comm]
    convert hup using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hh : (∑ i, ∑ j, f i j) = pairSum f + pairSum f := by
    calc
      (∑ i, ∑ j, f i j) =
          ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
      _ = pairSum f + pairSum f := by simp only [Finset.sum_add_distrib, hup, hlo]
  linarith

end ThomsonN10.Cert
