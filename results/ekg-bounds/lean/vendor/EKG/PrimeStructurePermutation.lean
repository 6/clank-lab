import EKG.PrimeStructure
import Mathlib.Data.Nat.Prime.Infinite

/-! Unconditional global consequences of prime introduction. In particular,
the EKG sequence is a permutation of the positive integers, without assuming
the 2p,p,3p pattern. -/
namespace EKG

theorem every_positive_divisor_has_multiple (s : GreedySeq) {d : ℕ}
    (hd : 0 < d) : ∃ n, d ∣ s.a n := by
  obtain ⟨p, hpd, hp⟩ := Nat.exists_infinite_primes (d+3)
  obtain ⟨n, hn⟩ := every_prime_introduced s hp
  obtain ⟨i, _, hi⟩ := smaller_divisor_seen s hn (by omega) hd (by omega)
  exact ⟨i, hi⟩

theorem multiples_unbounded (s : GreedySeq) {d : ℕ} (hd : 0 < d) (M : ℕ) :
    ∃ n, d ∣ s.a n ∧ M < s.a n := by
  obtain ⟨n, hn⟩ := every_positive_divisor_has_multiple s
    (Nat.mul_pos hd (by omega : 0 < M+1))
  have hlo := Nat.le_of_dvd (s.positive n) hn
  refine ⟨n, dvd_trans (Nat.dvd_mul_right d (M+1)) hn, ?_⟩
  nlinarith

theorem every_positive_occurs (s : GreedySeq) {m : ℕ} (hm : 0 < m) :
    ∃ n, s.a n = m := by
  classical
  by_cases hm1 : m = 1
  · exact ⟨0, s.seed_zero.trans hm1.symm⟩
  by_contra hnone
  have hfree : ∀ n, ¬ UsedBefore s.a n m := by
    rintro n ⟨i, _, hi⟩
    exact hnone ⟨i, hi⟩
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  let D := {n : ℕ // m ∣ s.a n}
  have hnext : ∀ n : D, s.a (n.val+1) ≤ m := by
    intro n
    have hn : 1 ≤ n.val := by
      by_contra hn
      have hn0 : n.val = 0 := by omega
      have hd := n.property
      rw [hn0, s.seed_zero] at hd
      have := Nat.le_of_dvd (by omega : 0 < 1) hd
      omega
    apply s.minimal (n.val+1) (by omega) m hm (hfree _)
    have he : n.val+1-1 = n.val := by omega
    rw [he]
    exact ⟨p, hp, dvd_trans hpm n.property, hpm⟩
  let f : D → Fin (m+1) := fun n => ⟨s.a (n.val+1), by have := hnext n; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : s.a (i.val+1) = s.a (j.val+1) := congrArg Fin.val hij
    have he' := s.injective he
    apply Subtype.ext
    omega
  haveI : Finite D := Finite.of_injective f hf
  letI : Fintype D := Fintype.ofFinite D
  let M := Finset.univ.sup (fun n : D => s.a n.val)
  obtain ⟨n, hdiv, hlarge⟩ := multiples_unbounded s hm M
  have hbound : s.a n ≤ M :=
    Finset.le_sup (f := fun n : D => s.a n.val) (Finset.mem_univ (⟨n, hdiv⟩ : D))
  omega

theorem positive_occurs_unique (s : GreedySeq) {m : ℕ} (hm : 0 < m) :
    ∃! n, s.a n = m := by
  obtain ⟨n, hn⟩ := every_positive_occurs s hm
  exact ⟨n, hn, fun i hi => s.injective (hi.trans hn.symm)⟩

theorem actualA_positive_occurs_unique {m : ℕ} (hm : 0 < m) :
    ∃! n, actualA n = m := positive_occurs_unique canonical hm

end EKG
