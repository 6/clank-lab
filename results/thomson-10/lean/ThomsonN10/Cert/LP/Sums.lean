/- Adapted from targets/thomson-10/lp-formal/n10/Thomson10/Sums.lean (supplied accepted N10 LP proof). N9 design: aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, proof/lean/ThomsonN9/LP/Concrete.lean. -/
import ThomsonN10.Cert.LP.Definitions

open scoped BigOperators
noncomputable section
namespace ThomsonN10.Cert.LP

def pairSum (f : Fin 10 → Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10, ∑ j ∈ Finset.univ.filter (fun j : Fin 10 => i < j), f i j

theorem sum_symmetric (f : Fin 10 → Fin 10 → ℝ) (hsym : ∀ i j, f i j = f j i) :
    (∑ i : Fin 10, ∑ j : Fin 10, f i j) = 2*pairSum f + ∑ i : Fin 10, f i i := by
  have hf (i j : Fin 10) : f i j =
      (if i < j then f i j else 0)+(if j < i then f j i else 0)+
      (if i=j then f i i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, hsym]
  have hs : (∑ i : Fin 10, ∑ j : Fin 10, f i j) =
      (∑ i : Fin 10, ∑ j : Fin 10, if i < j then f i j else 0)+
      (∑ i : Fin 10, ∑ j : Fin 10, if j < i then f j i else 0)+
      (∑ i : Fin 10, ∑ j : Fin 10, if i=j then f i i else 0) := by
    calc
      _ = ∑ i : Fin 10, ∑ j : Fin 10,
          ((if i < j then f i j else 0)+(if j < i then f j i else 0)+
            (if i=j then f i i else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hf i j
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hswap : (∑ i : Fin 10, ∑ j : Fin 10, if j < i then f j i else 0) =
      (∑ i : Fin 10, ∑ j : Fin 10, if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
  have hdiag : (∑ i : Fin 10, ∑ j : Fin 10, if i=j then f i i else 0) =
      ∑ i : Fin 10, f i i := by simp
  rw [hs, hswap, hdiag]
  simp only [pairSum, Finset.sum_filter]
  ring

theorem pairSum_nonneg (f : Fin 10 → Fin 10 → ℝ)
    (hf : ∀ i j, i < j → 0 ≤ f i j) : 0 ≤ pairSum f := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j hj
  exact hf i j (Finset.mem_filter.mp hj).2

theorem pair_le_pairSum (f : Fin 10 → Fin 10 → ℝ)
    (hf : ∀ i j, i < j → 0 ≤ f i j) (i j : Fin 10) (hij : i < j) :
    f i j ≤ pairSum f := by
  have hi : f i j ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin 10 => i < k), f i k := by
    apply Finset.single_le_sum
    · intro k hk; exact hf i k (Finset.mem_filter.mp hk).2
    · simp [hij]
  have hout : (∑ k ∈ Finset.univ.filter (fun k : Fin 10 => i < k), f i k) ≤ pairSum f := by
    unfold pairSum
    apply Finset.single_le_sum (f := fun u : Fin 10 => ∑ v ∈ Finset.univ.filter (fun v : Fin 10 => u < v), f u v)
    · intro u _
      apply Finset.sum_nonneg
      intro v hv
      exact hf u v (Finset.mem_filter.mp hv).2
    · exact Finset.mem_univ i
  exact hi.trans hout

end ThomsonN10.Cert.LP
