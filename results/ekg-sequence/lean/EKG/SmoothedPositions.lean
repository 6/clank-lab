import EKG.PrimeStructureGlobal
import EKG.Targets
import EKG.Span

/-! Unconditional structural classification of smoothed EKG positions.
All indices are zero based. Odd primes use the frontier two positions
earlier, odd-prime ticks use the frontier three positions earlier, and
the exceptional values 2 and 6 are checked in the certified finite prefix.
No rate estimate is a hypothesis or a dependency of these conclusions. -/
namespace EKG

theorem smoothValue_of_prime {p : ℕ} (hp : p.Prime) : smoothValue p = 2*p := by
  simp only [smoothValue, if_pos hp]

/-- This includes `p=2`: the current smoothing definition maps `6` to `4`. -/
theorem smoothValue_of_three_mul_prime {p : ℕ} (hp : p.Prime) :
    smoothValue (3*p) = 2*p := by
  have hp2 := hp.two_le
  have hnot : ¬ (3*p).Prime := Nat.not_prime_of_dvd_of_lt
    (Nat.dvd_mul_right 3 p) (by omega : 2 ≤ 3) (by omega : 3 < 3*p)
  have hdiv : 3*p/3 = p := Nat.mul_div_cancel_left p (by omega)
  simp only [smoothValue, if_neg hnot, hdiv, hp, and_self, if_true]

theorem smoothValue_of_ordinary {m : ℕ} (hprime : ¬ m.Prime)
    (htick : ¬ spanTickValue m) (hsix : m ≠ 6) : smoothValue m = m := by
  have htriple : ¬ ((m/3).Prime ∧ m = 3*(m/3)) := by
    rintro ⟨hp, he⟩
    have hp2 : m/3 ≠ 2 := by
      intro htwo
      rw [htwo] at he
      exact hsix he
    exact htick ⟨m/3, hp, hp2, he⟩
  simp only [smoothValue, if_neg hprime, if_neg htriple]

theorem GreedySeq.smoothed_odd_prime_frontier (s : GreedySeq) {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hvalue : s.a n = p) :
    3 ≤ n ∧ smoothValue (s.a n) = 2*p ∧ frontier s (n-2) = 2*p := by
  have hb := prime_occurrence_block s hp hp2 hvalue
  exact ⟨hb.1, by rw [hvalue]; exact smoothValue_of_prime hp, hb.2.2.2⟩

theorem GreedySeq.smoothed_tick_frontier (s : GreedySeq) {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hvalue : s.a n = 3*p) :
    4 ≤ n ∧ smoothValue (s.a n) = 2*p ∧ frontier s (n-3) = 2*p := by
  obtain ⟨i, hnew, hn, _⟩ := odd_prime_tick_unique s hp hp2 hvalue
  have hi := newPrime_index s hnew hp2
  have hindex : n-3 = i-1 := by omega
  have hf := firstMultiple_frontier s hnew hp2
  rw [← hindex] at hf
  exact ⟨by omega, by rw [hvalue]; exact smoothValue_of_three_mul_prime hp, hf⟩

/-- The first three positive-index smoothed terms all equal the frontier
at time one. This covers the prime-two and six exceptions exactly. -/
theorem GreedySeq.smoothed_small_prefix (s : GreedySeq) {n : ℕ}
    (hn : 1 ≤ n) (hn3 : n ≤ 3) : smoothValue (s.a n) = frontier s 1 := by
  have hf : frontier s 1 = 4 := by
    simpa [FiniteBase.frontierValue] using
      (FiniteBase.frontier_eq s (t := 1) (by omega))
  rw [hf]
  have hvalue := FiniteBase.first_thirteen s (n := n) (by omega)
  have hc : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hc with hc | hc | hc <;> subst n
  all_goals rw [hvalue]
  all_goals change smoothValue _ = 4
  all_goals decide

theorem GreedySeq.smoothed_two_exception (s : GreedySeq) {n : ℕ}
    (hvalue : s.a n = 2) :
    n = 1 ∧ smoothValue (s.a n) = 4 ∧ smoothValue (s.a n) = frontier s n := by
  have hn : n = 1 := s.injective (hvalue.trans s.seed_one.symm)
  refine ⟨hn, by rw [hvalue]; exact smoothValue_of_prime Nat.prime_two, ?_⟩
  rw [hn]
  exact s.smoothed_small_prefix (by omega) (by omega)

theorem GreedySeq.smoothed_six_exception (s : GreedySeq) {n : ℕ}
    (hvalue : s.a n = 6) :
    n = 3 ∧ smoothValue (s.a n) = 4 ∧
      smoothValue (s.a n) = frontier s (n-2) := by
  have hsix : s.a 3 = 6 := by
    simpa [FiniteBase.value] using (FiniteBase.first_thirteen s (n := 3) (by omega))
  have hn : n = 3 := s.injective (hvalue.trans hsix.symm)
  refine ⟨hn, ?_, ?_⟩
  · rw [hvalue]
    exact smoothValue_of_three_mul_prime Nat.prime_two
  · rw [hn]
    exact s.smoothed_small_prefix (by omega) (by omega)

/-- After the finite exceptions, smoothing either preserves a non-tick
composite or equals the frontier exactly two or three positions earlier. -/
theorem GreedySeq.smoothed_position_cases (s : GreedySeq) {n : ℕ} (hn : 4 ≤ n) :
    (1 < s.a n ∧ ¬ (s.a n).Prime ∧ ¬ spanTickValue (s.a n) ∧
      smoothValue (s.a n) = s.a n) ∨
    (smoothValue (s.a n) = frontier s (n-2) ∨
      smoothValue (s.a n) = frontier s (n-3)) := by
  by_cases hp : (s.a n).Prime
  · have hp2 : s.a n ≠ 2 := by
      intro htwo
      have hindex := s.injective (htwo.trans s.seed_one.symm)
      omega
    have hb := s.smoothed_odd_prime_frontier hp hp2 rfl
    exact Or.inr (Or.inl (hb.2.1.trans hb.2.2.symm))
  · by_cases htick : spanTickValue (s.a n)
    · obtain ⟨p, hp, hp2, heq⟩ := htick
      have hb := s.smoothed_tick_frontier hp hp2 heq
      exact Or.inr (Or.inr (hb.2.1.trans hb.2.2.symm))
    · have hsix : s.a n ≠ 6 := by
        intro heq
        have hi := (s.smoothed_six_exception heq).1
        omega
      have hone : s.a n ≠ 1 := by
        intro heq
        have hi := s.injective (heq.trans s.seed_zero.symm)
        omega
      exact Or.inl ⟨by have := s.positive n; omega, hp, htick,
        smoothValue_of_ordinary hp htick hsix⟩

/-- Assembly interface valid for every positive index: the ordinary branch
stays at `n`; the frontier branch supplies a witness `k` with `0 ≤ n-k ≤ 3`. -/
theorem GreedySeq.smoothed_nearby_position (s : GreedySeq) {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, k ≤ n ∧ n-k ≤ 3 ∧
      ((k = n ∧ 1 < s.a n ∧ ¬ (s.a n).Prime ∧ ¬ spanTickValue (s.a n) ∧
        smoothValue (s.a n) = s.a n) ∨ smoothValue (s.a n) = frontier s k) := by
  by_cases hn4 : 4 ≤ n
  · rcases s.smoothed_position_cases hn4 with hordinary | hfrontier
    · exact ⟨n, le_rfl, by omega, Or.inl ⟨rfl, hordinary⟩⟩
    · rcases hfrontier with htwo | hthree
      · exact ⟨n-2, by omega, by omega, Or.inr htwo⟩
      · exact ⟨n-3, by omega, by omega, Or.inr hthree⟩
  · exact ⟨1, hn, by omega, Or.inr (s.smoothed_small_prefix hn (by omega))⟩

theorem actualA_smoothed_position_cases {n : ℕ} (hn : 4 ≤ n) :
    (1 < actualA n ∧ ¬ (actualA n).Prime ∧ ¬ spanTickValue (actualA n) ∧
      smoothValue (actualA n) = actualA n) ∨
    (smoothValue (actualA n) = frontier canonical (n-2) ∨
      smoothValue (actualA n) = frontier canonical (n-3)) :=
  canonical.smoothed_position_cases hn

theorem actualA_smoothed_nearby_position {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, k ≤ n ∧ n-k ≤ 3 ∧
      ((k = n ∧ 1 < actualA n ∧ ¬ (actualA n).Prime ∧ ¬ spanTickValue (actualA n) ∧
        smoothValue (actualA n) = actualA n) ∨
        smoothValue (actualA n) = frontier canonical k) :=
  canonical.smoothed_nearby_position hn

/-- The only zero-index exception is the initial value one. -/
theorem actualA_smoothed_zero : smoothValue (actualA 0) = 1 := by
  rw [actualA_zero]
  decide

end EKG
