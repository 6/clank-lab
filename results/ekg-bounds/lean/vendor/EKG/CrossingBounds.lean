import EKG.Crossings
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Sqrt

namespace EKG

theorem upCount_eq_card (a : ℕ → ℕ) (X n : ℕ) :
    upCount a X n =
      ((Finset.range n).filter (fun i => a i < X ∧ X ≤ a (i+1))).card := by
  induction n with
  | zero => simp [upCount]
  | succ n ih =>
    by_cases h : a n < X ∧ X ≤ a (n+1)
    all_goals simp [upCount, Finset.range_add_one, Finset.filter_insert, h, ih]

theorem downCount_eq_card (a : ℕ → ℕ) (X n : ℕ) :
    downCount a X n =
      ((Finset.range n).filter (fun i => X ≤ a i ∧ a (i+1) < X)).card := by
  induction n with
  | zero => simp [downCount]
  | succ n ih =>
    by_cases h : X ≤ a n ∧ a (n+1) < X
    all_goals simp [downCount, Finset.range_add_one, Finset.filter_insert, h, ih]

/-- The window bound needed for missing composites. Unlike the initial-prefix
bound it costs one endpoint, irrespective of which side the window starts on. -/
theorem window_down_le_up_add_one (a : ℕ → ℕ) (X start len : ℕ) :
    downCount (fun n => a (start+n)) X len ≤
      upCount (fun n => a (start+n)) X len + 1 := by
  have h := crossing_balance (fun n => a (start+n)) X len
  have hstart : above (fun n => a (start+n)) X 0 ≤ 1 := by
    unfold above
    split <;> omega
  omega

/-- Exhaustion gives injectivity of labels of genuine greedy upcrossings.
Unlike the abstract crossing inequality, all hypotheses below are local
properties of the crossings; no exhaustion assumption is needed. -/
theorem GreedySeq.upcrossing_card_bound (s : GreedySeq) (X : ℕ)
    (U P : Finset ℕ) (control : ℕ → ℕ)
    (hindex : ∀ i ∈ U, 1 ≤ i)
    (hcross : ∀ i ∈ U, s.a i < X ∧ X ≤ s.a (i+1))
    (hprime : ∀ i ∈ U, (control i).Prime)
    (hcontrol : ∀ i ∈ U, control i ∣ s.a i)
    (hlabels : ∀ i ∈ U, control i ∈ P) :
    U.card ≤ P.card := by
  apply Finset.card_le_card_of_injOn control hlabels
  intro i hi j hj heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hlt : s.a j < s.a (i+1) := lt_of_lt_of_le (hcross j hj).1 (hcross i hi).2
    obtain ⟨k, hk, he⟩ := smaller_multiple_used s (n := i+1)
      (by have := hindex i hi; omega) (hprime i hi)
      (by simpa using hcontrol i hi) (s.positive j)
      (by rw [heq]; exact hcontrol j hj) hlt
    have := s.injective he
    omega
  · have hlt : s.a i < s.a (j+1) := lt_of_lt_of_le (hcross i hi).1 (hcross j hj).2
    obtain ⟨k, hk, he⟩ := smaller_multiple_used s (n := j+1)
      (by have := hindex j hj; omega) (hprime j hj)
      (by simpa using hcontrol j hj) (s.positive i)
      (by rw [← heq]; exact hcontrol i hi) hlt
    have := s.injective he
    omega

/-- F3 in the manuscript: every finite family of composite-base
upcrossings injects into primes at most sqrt X. This theorem is unconditional
for every EKG greedy sequence. -/
theorem GreedySeq.composite_upcrossings_bound (s : GreedySeq) (X : ℕ)
    (U : Finset ℕ)
    (hcomposite : ∀ i ∈ U, 1 < s.a i ∧ ¬ (s.a i).Prime)
    (hcross : ∀ i ∈ U, s.a i < X ∧ X ≤ s.a (i+1)) :
    U.card ≤ Nat.primeCounting (Nat.sqrt X) := by
  classical
  let P := (Nat.sqrt X + 1).primesBelow
  have hcard : P.card = Nat.primeCounting (Nat.sqrt X) :=
    Nat.primesBelow_card_eq_primeCounting' _
  rw [← hcard]
  apply s.upcrossing_card_bound X U P (fun i => (s.a i).minFac)
  · intro i hi
    by_contra hn
    have hii : i = 0 := by omega
    have hbig := (hcomposite i hi).1
    simp [hii, s.seed_zero] at hbig
  · exact hcross
  · intro i hi
    exact Nat.minFac_prime (by have := (hcomposite i hi).1; omega)
  · intro i hi
    exact Nat.minFac_dvd _
  · intro i hi
    apply Nat.mem_primesBelow.mpr
    have hsq := Nat.minFac_sq_le_self (s.positive i) (hcomposite i hi).2
    have hle : (s.a i).minFac ≤ Nat.sqrt X := Nat.le_sqrt'.mpr (by
      exact le_trans hsq (Nat.le_of_lt (hcross i hi).1))
    exact ⟨by omega, Nat.minFac_prime (by have := (hcomposite i hi).1; omega)⟩

theorem GreedySeq.composite_upCount_bound (s : GreedySeq) (X t : ℕ) :
    ((Finset.range t).filter (fun i => 1 < s.a i ∧ ¬ (s.a i).Prime ∧
      s.a i < X ∧ X ≤ s.a (i+1))).card ≤ Nat.primeCounting (Nat.sqrt X) := by
  apply s.composite_upcrossings_bound
  · intro i hi
    exact ⟨(Finset.mem_filter.mp hi).2.1, (Finset.mem_filter.mp hi).2.2.1⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.2.2

end EKG
