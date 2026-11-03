import UniformTransport
import UniformKernel

/-! The joint law of matrix and tie choices on the good event, with the LP as an
invariant. -/
namespace ADG.Uniform
open Finset
open scoped Classical

noncomputable def gatedPayoff {m n : ℕ} (A : Matrix m n) (F : Matrix m n → ℕ → Prop)
    (T : Finset (Fin n)) : ℝ :=
  if good A ∧ feasible A then phasePayoff A univ (F A) T else 0

lemma kernel_good_average {m n : ℕ} (A : Matrix m n) (F : Matrix m n → ℕ → Prop) :
    countProb A m univ (fun g => good A ∧ feasible A ∧ F A g) =
      (∑ l ∈ Conflict.orders (univ : Finset (Fin n)),
        gatedPayoff A F (Conflict.scanList (conflict A) l (triples A univ))) / n.factorial := by
  by_cases h : good A ∧ feasible A
  · have he : countProb A m univ (fun g => good A ∧ feasible A ∧ F A g) =
        countProb A m univ (F A) :=
      countProb_congr A m univ _ _ (fun g => by simp [h.1, h.2])
    rw [he, countProb_phase A h.2 h.1.1 h.1.2 m univ (by simp)]
    rw [← Conflict.scan_eq_choose (conflict A) univ (triples A univ) (subset_univ _) (phasePayoff A univ (F A)),
      Conflict.scan_average]
    simp only [card_univ, Fintype.card_fin, gatedPayoff, if_pos h]
  · have he : countProb A m univ (fun g => good A ∧ feasible A ∧ F A g) =
        countProb A m univ (fun _ => False) :=
      countProb_congr A m univ _ _ (fun g => by tauto)
    rw [he, countProb_false]
    simp [gatedPayoff, h]

lemma ordered_gated_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n))
    (F : Matrix m n → ℕ → Prop)
    (hF : ∀ A π g, F (relabel A π) g ↔ F A g) :
    gatedPayoff A F (Conflict.scanList (conflict A) ((List.finRange n).map π)
      (triples A univ)) =
      if good (relabel A π) ∧ feasible (relabel A π) ∧
        F (relabel A π) (G (relabel A π)) then 1 else 0 := by
  by_cases h : good A ∧ feasible A
  · rw [gatedPayoff, if_pos h, ordered_payoff_relabel A π h.2 h.1.1 h.1.2]
    simp only [good_relabel, feasible_relabel, hF, h.1, h.2, true_and]
  · simp only [gatedPayoff, if_neg h, good_relabel, feasible_relabel, hF]
    split_ifs with hh
    · exact False.elim (h ⟨hh.1, hh.2.1⟩)
    · rfl

/-- Equality is joint with the matrix: all invariant matrix events and all
invariant count predicates can be included, rather than matching marginals. -/
theorem joint_good_transport (m n : ℕ) (p : ℝ) (F : Matrix m n → ℕ → Prop)
    (hF : ∀ A π g, F (relabel A π) g ↔ F A g) :
    jointProb m n p (fun A g => good A ∧ feasible A ∧ F A g) =
      matrixProb m n p (fun A => good A ∧ feasible A ∧ F A (G A)) := by
  let f : Matrix m n → ℝ := fun A => if good A ∧ feasible A ∧ F A (G A) then 1 else 0
  have horder (l : List (Fin n)) (hl : l ∈ Conflict.orders univ) :
      (∑ A : Matrix m n, iidMass (columnMass m p) A *
        gatedPayoff A F (Conflict.scanList (conflict A) l (triples A univ))) =
      ∑ A : Matrix m n, iidMass (columnMass m p) A * f A := by
    obtain ⟨π, rfl⟩ := order_is_relabel l hl
    simp_rw [ordered_gated_relabel _ _ _ hF]
    exact expectation_relabel π p f
  change (∑ A : Matrix m n, iidMass (columnMass m p) A *
    countProb A m univ (fun g => good A ∧ feasible A ∧ F A g)) = _
  simp_rw [kernel_good_average, ← mul_div_assoc, mul_sum]
  rw [← sum_div, sum_comm]
  rw [sum_congr rfl horder]
  simp only [sum_const, nsmul_eq_mul, Conflict.card_orders, card_univ, Fintype.card_fin]
  rw [mul_div_cancel_left₀ _ (by positivity : (n.factorial : ℝ) ≠ 0)]
  simp only [matrixProb, iidProb, f, mul_ite, mul_one, mul_zero]
  apply sum_congr rfl
  intro A _
  by_cases h : good A ∧ feasible A ∧ F A (G A) <;> simp [h]

end ADG.Uniform
