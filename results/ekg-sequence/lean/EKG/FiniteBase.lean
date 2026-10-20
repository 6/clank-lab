import EKG.Frontier

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace EKG

namespace FiniteBase

/-- All finite checks use bounded quantifiers and the computable gcd rule. -/
def GreedyRow (f : ℕ → ℕ) (n : ℕ) : Prop :=
  0 < f n ∧ (∀ i : Fin n, f i.val ≠ f n) ∧
  1 < Nat.gcd (f (n-1)) (f n) ∧
  ∀ m : Fin (f n), 0 < m.val → 1 < Nat.gcd (f (n-1)) m.val →
    ∃ i : Fin n, f i.val = m.val

instance (f : ℕ → ℕ) (n : ℕ) : Decidable (GreedyRow f n) := by
  unfold GreedyRow
  infer_instance

structure CertifiedPrefix (f : ℕ → ℕ) (N : ℕ) : Prop where
  seed_zero : f 0 = 1
  seed_one : f 1 = 2
  rows : ∀ n, 2 ≤ n → n < N → GreedyRow f n

/-- Soundness transfers the finite certificate to the actual greedy sequence.
Every smaller positive eligible candidate is covered by the checked row. -/
theorem CertifiedPrefix.agrees {f : ℕ → ℕ} {N : ℕ}
    (cert : CertifiedPrefix f N) (s : GreedySeq) :
    ∀ n, n < N → s.a n = f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hN
    by_cases hn : 2 ≤ n
    · have hr := cert.rows n hn hN
      have hprev := ih (n-1) (by omega) (by omega)
      have hfree : ¬ UsedBefore s.a n (f n) := by
        rintro ⟨i, hi, he⟩
        rw [ih i hi (by omega)] at he
        exact hr.2.1 ⟨i, hi⟩ he
      have helig : SharedPrime (s.a (n-1)) (f n) := by
        apply (sharedPrime_iff_gcd (s.positive (n-1))).mpr
        rw [hprev]
        exact hr.2.2.1
      have hle := s.minimal n hn (f n) hr.1 hfree helig
      apply le_antisymm hle
      by_contra h
      have hlt : s.a n < f n := by omega
      have hgcd : 1 < Nat.gcd (f (n-1)) (s.a n) := by
        rw [← hprev]
        exact (sharedPrime_iff_gcd (s.positive (n-1))).mp (s.eligible n hn)
      obtain ⟨i, hi⟩ := hr.2.2.2 ⟨s.a n, hlt⟩ (s.positive n) hgcd
      have he : s.a i.val = s.a n := (ih i.val i.isLt (by omega)).trans hi
      have := s.injective he
      have := i.isLt
      omega
    · have hs : n = 0 ∨ n = 1 := by omega
      rcases hs with hs | hs <;> subst n
      · exact s.seed_zero.trans cert.seed_zero.symm
      · exact s.seed_one.trans cert.seed_one.symm

def value (n : ℕ) : ℕ :=
  ([1, 2, 4, 6, 3, 9, 12, 8, 10, 5, 15, 18, 14] : List ℕ)[n]?.getD 0

theorem checked_rows : ∀ n : Fin 13, 2 ≤ n.val → GreedyRow value n.val := by
  decide

theorem certified : CertifiedPrefix value 13 := by
  refine ⟨by decide, by decide, ?_⟩
  intro n hn hN
  exact checked_rows ⟨n, hN⟩ hn

theorem first_thirteen (s : GreedySeq) {n : ℕ} (hn : n < 13) : s.a n = value n :=
  certified.agrees s n hn

theorem actualA_first_thirteen {n : ℕ} (hn : n < 13) : actualA n = value n :=
  first_thirteen canonical hn

/-- A computable prefix set used only after the canonical bridge is proved. -/
def usedSet (t : ℕ) : Finset ℕ := (Finset.range (t+1)).image value

def frontierValue (t : ℕ) : ℕ :=
  ([2, 4, 6, 8, 8, 8, 8, 10, 14, 14, 14, 14, 16] : List ℕ)[t]?.getD 0

def FrontierRow (t : ℕ) : Prop :=
  0 < frontierValue t ∧ 2 ∣ frontierValue t ∧ frontierValue t ∉ usedSet t ∧
    ∀ m : Fin (frontierValue t), 0 < m.val → 2 ∣ m.val → m.val ∈ usedSet t

instance (t : ℕ) : Decidable (FrontierRow t) := by
  unfold FrontierRow
  infer_instance

theorem checked_frontiers : ∀ t : Fin 13, FrontierRow t.val := by decide

theorem usedSet_eq (s : GreedySeq) {t : ℕ} (ht : t < 13) :
    (Finset.range (t+1)).image s.a = usedSet t := by
  unfold usedSet
  apply Finset.image_congr
  intro i hi
  exact first_thirteen s (by have := Finset.mem_range.mp hi; omega)

theorem usedBefore_iff_mem (s : GreedySeq) {t m : ℕ} (ht : t < 13) :
    UsedBefore s.a (t+1) m ↔ m ∈ usedSet t := by
  rw [← usedSet_eq s ht]
  simp only [UsedBefore, Finset.mem_image, Finset.mem_range]

theorem frontier_eq (s : GreedySeq) {t : ℕ} (ht : t < 13) :
    frontier s t = frontierValue t := by
  have hr := checked_frontiers ⟨t, ht⟩
  have hle := frontier_le s t (frontierValue t) hr.1 hr.2.1
    (fun hu => hr.2.2.1 ((usedBefore_iff_mem s ht).mp hu))
  apply le_antisymm hle
  by_contra h
  have hlt : frontier s t < frontierValue t := by omega
  have hp := frontier_spec s t
  have hmem := hr.2.2.2 ⟨frontier s t, hlt⟩ hp.1 hp.2.1
  exact hp.2.2 ((usedBefore_iff_mem s ht).mpr hmem)

def earlyCountValue (t : ℕ) : ℕ :=
  ((usedSet t).filter (fun w => 2 ∣ w ∧ frontierValue t < w)).card

theorem earlyEvenCount_eq (s : GreedySeq) {t : ℕ} (ht : t < 13) :
    earlyEvenCount s t = earlyCountValue t := by
  unfold earlyEvenCount earlyCountValue
  rw [usedSet_eq s ht, frontier_eq s ht]

theorem checked_early_base : ∀ t : Fin 10, earlyCountValue t.val ≤ 1 := by decide

/-- The actual canonical count satisfies the requested zero-based cutoff `t ≤ 9`.
This also contains the manuscript's one-based cutoff `t ≤ 9`. -/
theorem earlyEvenBase : ∀ t, t ≤ 9 → earlyEvenCount canonical t ≤ 1 := by
  intro t ht
  rw [earlyEvenCount_eq canonical (by omega : t < 13)]
  exact checked_early_base ⟨t, by omega⟩

end FiniteBase

end EKG
