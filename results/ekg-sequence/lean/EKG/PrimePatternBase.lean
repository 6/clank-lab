import EKG.FiniteBase
import EKG.PrimeStructure

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace EKG
namespace PrimePatternBase

/-- The first 82 terms, with zero-based indices. The list is certified below
against every smaller candidate in the gcd greedy rule. -/
def value (n : ℕ) : ℕ :=
  ([1, 2, 4, 6, 3, 9, 12, 8, 10, 5, 15, 18, 14, 7, 21, 24,
    16, 20, 22, 11, 33, 27, 30, 25, 35, 28, 26, 13, 39, 36, 32,
    34, 17, 51, 42, 38, 19, 57, 45, 40, 44, 46, 23, 69, 48, 50,
    52, 54, 56, 49, 63, 60, 55, 65, 70, 58, 29, 87, 66, 62, 31,
    93, 72, 64, 68, 74, 37, 111, 75, 78, 76, 80, 82, 41, 123,
    81, 84, 77, 88, 86, 43, 129] : List ℕ)[n]?.getD 0

theorem checked_rows : ∀ n : Fin 82,
    2 ≤ n.val → FiniteBase.GreedyRow value n.val := by
  decide +kernel

theorem certified : FiniteBase.CertifiedPrefix value 82 := by
  refine ⟨by decide, by decide, ?_⟩
  intro n hn hN
  exact checked_rows ⟨n, hN⟩ hn

theorem first_eighty_two (s : GreedySeq) {n : ℕ} (hn : n < 82) :
    s.a n = value n := certified.agrees s n hn

/-- A bounded certificate of all odd-prime triples needed for the finite base.
The bound on `i` also puts both following terms inside the certified prefix. -/
theorem checked_triples : ∀ p : Fin 44, p.val.Prime → p.val ≠ 2 →
    ∃ i : Fin 80, value i.val = 2*p.val ∧
      value (i.val+1) = p.val ∧ value (i.val+2) = 3*p.val := by
  decide +kernel

theorem small_prime_triple (s : GreedySeq) {p : ℕ}
    (hp : p.Prime) (hp43 : p ≤ 43) (hp2 : p ≠ 2) :
    ∃ i : ℕ, i < 80 ∧ s.a i = 2*p ∧ s.a (i+1) = p ∧ s.a (i+2) = 3*p := by
  obtain ⟨i, hfirst, hsecond, hthird⟩ :=
    checked_triples ⟨p, by omega⟩ hp hp2
  refine ⟨i.val, i.isLt, ?_, ?_, ?_⟩
  · exact (first_eighty_two s (by have := i.isLt; omega)).trans hfirst
  · exact (first_eighty_two s (by have := i.isLt; omega)).trans hsecond
  · exact (first_eighty_two s (by have := i.isLt; omega)).trans hthird

/-- Injectivity identifies the checked prime occurrence with the term after
an arbitrary first introduction, so no bound on the given index is assumed. -/
theorem firstMultiple_eq_twice (s : GreedySeq) {n p : ℕ}
    (hnew : NewPrimeAt s n p) (hp43 : p ≤ 43) (hp2 : p ≠ 2) :
    s.a n = 2*p := by
  obtain ⟨i, _, hfirst, hsecond, _⟩ := small_prime_triple s hnew.1 hp43 hp2
  have he := s.injective ((firstMultiple_next_prime s hnew hp2).trans hsecond.symm)
  have hni : n = i := by omega
  simpa [hni] using hfirst

theorem small_prime_introduction (s : GreedySeq) {p : ℕ}
    (hp : p.Prime) (hp43 : p ≤ 43) (hp2 : p ≠ 2) :
    ∃ i : ℕ, i < 80 ∧ NewPrimeAt s i p ∧
      s.a i = 2*p ∧ s.a (i+1) = p ∧ s.a (i+2) = 3*p := by
  obtain ⟨i, hi, hfirst, hsecond, hthird⟩ := small_prime_triple s hp hp43 hp2
  have hnew := (primeOccurrenceIntro s hp hp2 hsecond).2
  refine ⟨i, hi, ?_, hfirst, hsecond, hthird⟩
  simpa using hnew

theorem introduction_triple (s : GreedySeq) {n p : ℕ}
    (hnew : NewPrimeAt s n p) (hp43 : p ≤ 43) (hp2 : p ≠ 2) :
    s.a n = 2*p ∧ s.a (n+1) = p ∧ s.a (n+2) = 3*p := by
  obtain ⟨i, _, hfirst, hsecond, hthird⟩ := small_prime_triple s hnew.1 hp43 hp2
  have he := s.injective ((firstMultiple_next_prime s hnew hp2).trans hsecond.symm)
  have hni : n = i := by omega
  simpa [hni] using And.intro hfirst (And.intro hsecond hthird)

end PrimePatternBase
end EKG
