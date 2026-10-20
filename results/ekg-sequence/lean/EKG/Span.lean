import EKG.Frontier
import EKG.Crossings
import EKG.PrimeStructureLocal
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Sqrt

/-! Exact count-to-span conversion for the actual greedy EKG rule.
No prime-introduction pattern or early-even estimate is assumed here.
The final quadratic conversion is also proved independently. -/
namespace EKG

/-- Indices of the positive multiples of `d` strictly between `e` and `v`.
The formula works also when the interval is empty. -/
def progressionIndices (e v d : ℕ) : Finset ℕ :=
  Finset.Ico (e / d + 1) ((v - 1) / d + 1)

theorem progressionIndices_bounds {e v d j : ℕ} (hd : 0 < d)
    (hj : j ∈ progressionIndices e v d) : e < d*j ∧ d*j < v := by
  have hj' := Finset.mem_Ico.mp hj
  have hl := Nat.lt_mul_div_succ e hd
  have hlo : d * (e/d+1) ≤ d*j := Nat.mul_le_mul_left d hj'.1
  have hji : j ≤ (v-1)/d := by omega
  have hhi := (Nat.le_div_iff_mul_le hd).mp hji
  have hjpos : 0 < j := lt_of_lt_of_le (Nat.zero_lt_succ _) hj'.1
  have hprod : 0 < d*j := Nat.mul_pos hd hjpos
  have hhi' : d*j ≤ v-1 := by simpa only [Nat.mul_comm] using hhi
  have hvpos : 0 < v := lt_of_lt_of_le hprod (hhi'.trans (Nat.sub_le v 1))
  exact ⟨hl.trans_le hlo, hhi'.trans_lt (Nat.sub_lt hvpos (by omega))⟩

/-- The exact floor count costs only one rung in converting to a span. -/
theorem progression_span_le {e v d K : ℕ} (hd : 0 < d)
    (hc : (progressionIndices e v d).card ≤ K) : v ≤ e + d*(K+1) := by
  by_cases hve : v ≤ e
  · omega
  have hev : e ≤ v-1 := by omega
  have hdiv : e/d ≤ (v-1)/d := Nat.div_le_div_right hev
  rw [progressionIndices, Nat.card_Ico] at hc
  have hfloor : (v-1)/d ≤ e/d+K := by omega
  have hmul := Nat.mul_le_mul_left d (Nat.add_le_add_right hfloor 1)
  have hupper := Nat.lt_mul_div_succ (v-1) hd
  have hlower := Nat.div_mul_le_self e d
  rw [Nat.mul_comm (e/d) d] at hlower
  have hvle : v ≤ d*((v-1)/d+1) := by omega
  calc
    v ≤ d*((v-1)/d+1) := hvle
    _ ≤ d*(e/d+K+1) := hmul
    _ = d*(e/d) + d*(K+1) := by ring
    _ ≤ e + d*(K+1) := Nat.add_le_add_right hlower _

/-- Greedy exhaustion injects every intermediate multiple of `2q` into
the observed early evens. The selected term may be the next, unobserved term. -/
theorem GreedySeq.even_multiple_interval_card_le (s : GreedySeq)
    {n t q : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1)
    (hq : q.Prime) (hqb : q ∣ s.a (n-1)) :
    (progressionIndices (frontier s t) (s.a n) (2*q)).card ≤
      earlyEvenCount s t := by
  classical
  have hd : 0 < 2*q := Nat.mul_pos (by omega) hq.pos
  unfold earlyEvenCount
  apply Finset.card_le_card_of_injOn (fun j : ℕ => (2*q)*j)
  · intro j hj
    obtain ⟨he, hv⟩ := progressionIndices_bounds hd hj
    have hqdiv : q ∣ (2*q)*j := by
      exact dvd_mul_of_dvd_left (Nat.dvd_mul_left q 2) j
    obtain ⟨i, hi, hval⟩ := smaller_multiple_used s hn hq hqb
      (by omega : 0 < (2*q)*j) hqdiv hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hval⟩, ?_⟩
    exact ⟨dvd_mul_of_dvd_left (Nat.dvd_mul_right 2 q) j, he⟩
  · intro i _ j _ hij
    dsimp at hij
    nlinarith

/-- Unconditional manuscript span (a) for every predecessor prime factor.
It applies even at the next selection and does not require a non-tick assumption. -/
theorem GreedySeq.term_le_frontier_add (s : GreedySeq)
    {n t q : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1)
    (hq : q.Prime) (hqb : q ∣ s.a (n-1)) :
    s.a n ≤ frontier s t + 2*q*(earlyEvenCount s t+1) :=
  progression_span_le (Nat.mul_pos (by omega) hq.pos)
    (s.even_multiple_interval_card_le hn hnt hq hqb)

theorem GreedySeq.term_span_le (s : GreedySeq)
    {n t q : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1)
    (hq : q.Prime) (hqb : q ∣ s.a (n-1)) :
    s.a n - frontier s t ≤ 2*q*(earlyEvenCount s t+1) := by
  have := s.term_le_frontier_add hn hnt hq hqb
  omega

/-- The count-to-span statement specialized to the recursively defined sequence. -/
theorem actualA_span_le {n t q : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1)
    (hq : q.Prime) (hqb : q ∣ actualA (n-1)) :
    actualA n - frontier canonical t ≤ 2*q*(earlyEvenCount canonical t+1) :=
  canonical.term_span_le hn hnt hq hqb

/-- In particular, a tick-value predecessor `3p` supplies the factor three;
this needs neither the prime pattern nor the multiples-of-three frontier. -/
theorem GreedySeq.term_span_le_six (s : GreedySeq)
    {n t : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1) (hthree : 3 ∣ s.a (n-1)) :
    s.a n - frontier s t ≤ 6*(earlyEvenCount s t+1) := by
  simpa using s.term_span_le hn hnt Nat.prime_three hthree

/-- Exact real quadratic conversion used in manuscript span (b). -/
theorem quadratic_span_bound {e k v : ℝ} (he : 0 ≤ e) (hk : 0 ≤ k)
    (hv : 0 ≤ v) (hspan : v-e ≤ 2*k*Real.sqrt v) :
    v-e ≤ 2*k^2 + 2*k*Real.sqrt (k^2+e) := by
  have hsnon := Real.sqrt_nonneg v
  have hqnon := Real.sqrt_nonneg (k^2+e)
  have hsq := Real.sq_sqrt hv
  have hq := Real.sq_sqrt (show 0 ≤ k^2+e by nlinarith [sq_nonneg k])
  have hroot : Real.sqrt v ≤ k+Real.sqrt (k^2+e) := by
    by_contra h
    have hbig : k+Real.sqrt (k^2+e) < Real.sqrt v := lt_of_not_ge h
    have hdiff : 0 < Real.sqrt v-k-Real.sqrt (k^2+e) := by linarith
    have hsum : 0 < Real.sqrt v-k+Real.sqrt (k^2+e) := by linarith
    have hprod := mul_pos hdiff hsum
    nlinarith
  nlinarith

/-- The tick-predecessor bound `6k` is dominated by the quadratic bound
once the frontier is at least nine and the counting parameter at least one. -/
theorem six_mul_le_quadratic {e k : ℝ} (he : 9 ≤ e) (hk : 1 ≤ k) :
    6*k ≤ 2*k^2+2*k*Real.sqrt (k^2+e) := by
  have hs := Real.sqrt_nonneg (k^2+e)
  have hsq := Real.sq_sqrt (show 0 ≤ k^2+e by nlinarith [sq_nonneg k])
  have hthree : 3 ≤ Real.sqrt (k^2+e) := by nlinarith
  nlinarith

/-- Any controlling prime with `q² ≤ v` supplies the quadratic conversion;
no classification of predecessors or prime-introduction pattern is needed. -/
theorem GreedySeq.quadratic_span_of_prime_square_bound (s : GreedySeq)
    {n t q : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1)
    (hq : q.Prime) (hqb : q ∣ s.a (n-1)) (hqsq : q^2 ≤ s.a n) :
    (s.a n : ℝ) - (frontier s t : ℝ) ≤
      2 * (earlyEvenCount s t + 1 : ℕ)^2 +
      2 * (earlyEvenCount s t + 1 : ℕ) *
        Real.sqrt ((earlyEvenCount s t + 1 : ℕ)^2 + (frontier s t : ℝ)) := by
  have hspan := s.term_le_frontier_add hn hnt hq hqb
  have hrreal : (q : ℝ)^2 ≤ (s.a n : ℝ) := by exact_mod_cast hqsq
  have hv : (0 : ℝ) ≤ (s.a n : ℝ) := Nat.cast_nonneg _
  have hrbound : (q : ℝ) ≤ Real.sqrt (s.a n) := by
    have := Real.sqrt_nonneg (s.a n : ℝ)
    have := Real.sq_sqrt hv
    have := Nat.cast_nonneg (α := ℝ) q
    nlinarith
  have hspanreal : (s.a n : ℝ) ≤ (frontier s t : ℝ) +
      2 * (q : ℝ) * (earlyEvenCount s t + 1 : ℕ) := by
    exact_mod_cast hspan
  apply quadratic_span_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _) hv
  have := mul_nonneg (sub_nonneg.mpr hrbound)
    (Nat.cast_nonneg (α := ℝ) (earlyEvenCount s t + 1))
  nlinarith

/-- A composite predecessor bounded by the selected value gives the exact
quadratic span. The predecessor bound is an explicit local hypothesis. -/
theorem GreedySeq.composite_predecessor_quadratic_span (s : GreedySeq)
    {n t : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1)
    (hcomp : 1 < s.a (n-1) ∧ ¬ (s.a (n-1)).Prime)
    (hpred : s.a (n-1) ≤ s.a n) :
    (s.a n : ℝ) - (frontier s t : ℝ) ≤
      2 * (earlyEvenCount s t + 1 : ℕ)^2 +
      2 * (earlyEvenCount s t + 1 : ℕ) *
        Real.sqrt ((earlyEvenCount s t + 1 : ℕ)^2 + (frontier s t : ℝ)) :=
  s.quadratic_span_of_prime_square_bound hn hnt
    (Nat.minFac_prime (by omega : s.a (n-1) ≠ 1)) (Nat.minFac_dvd _)
    ((Nat.minFac_sq_le_self (s.positive (n-1)) hcomp.2).trans hpred)

/-- The two local predecessor cases in the manuscript imply its exact
quadratic span. Classifying a maximal non-tick term is a separate obligation. -/
theorem GreedySeq.quadratic_span_of_local_cases (s : GreedySeq)
    {n t : ℕ} (hn : 2 ≤ n) (hnt : n ≤ t+1) (he : 9 ≤ frontier s t)
    (hcases : 3 ∣ s.a (n-1) ∨
      (1 < s.a (n-1) ∧ ¬ (s.a (n-1)).Prime) ∧ s.a (n-1) ≤ s.a n) :
    (s.a n : ℝ) - (frontier s t : ℝ) ≤
      2 * (earlyEvenCount s t + 1 : ℕ)^2 +
      2 * (earlyEvenCount s t + 1 : ℕ) *
        Real.sqrt ((earlyEvenCount s t + 1 : ℕ)^2 + (frontier s t : ℝ)) := by
  rcases hcases with hthree | ⟨hcomp, hpred⟩
  · have hspan := s.term_le_frontier_add hn hnt Nat.prime_three hthree
    have hspanreal : (s.a n : ℝ) ≤ (frontier s t : ℝ) +
        6 * (earlyEvenCount s t + 1 : ℕ) := by exact_mod_cast hspan
    have he' : (9 : ℝ) ≤ (frontier s t : ℝ) := by exact_mod_cast he
    have hk : (1 : ℝ) ≤ (earlyEvenCount s t + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ earlyEvenCount s t+1 by omega)
    have hquad := six_mul_le_quadratic he' hk
    exact le_trans (by linarith : (s.a n : ℝ) - (frontier s t : ℝ) ≤
      6 * (earlyEvenCount s t + 1 : ℕ)) hquad
  · exact s.composite_predecessor_quadratic_span hn hnt hcomp hpred

/-- A manuscript tick value is `3p` for an odd prime `p` (including `p=3`). -/
def spanTickValue (m : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ m = 3*p

/-- Maximum of the observed values that are not tick values. -/
noncomputable def nonTickTop (s : GreedySeq) (t : ℕ) : ℕ := by
  classical
  exact ((Finset.range (t+1)).filter (fun i => ¬ spanTickValue (s.a i))).sup s.a

theorem nonTick_le_top (s : GreedySeq) {i t : ℕ} (hi : i ≤ t)
    (hnot : ¬ spanTickValue (s.a i)) : s.a i ≤ nonTickTop s t := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnot⟩)

theorem nonTickTop_attained (s : GreedySeq) (t : ℕ) :
    ∃ i, i ≤ t ∧ ¬ spanTickValue (s.a i) ∧ nonTickTop s t = s.a i := by
  classical
  let I := (Finset.range (t+1)).filter (fun i => ¬ spanTickValue (s.a i))
  have hzero : 0 ∈ I := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [s.seed_zero]
    rintro ⟨p, hp, _, heq⟩
    have := hp.two_le
    omega
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup I ⟨0, hzero⟩ s.a
  obtain ⟨hir, hnot⟩ := Finset.mem_filter.mp hi
  exact ⟨i, by have := Finset.mem_range.mp hir; omega, hnot, heq⟩

/-- Only the structural introduction pattern is assumed. The local prime
successor behavior follows from the proved first-introduction lemmas. -/
theorem GreedySeq.odd_prime_successor_tick_of_pattern (s : GreedySeq)
    (hpattern : ∀ n p, NewPrimeAt s n p → p ≠ 2 → s.a n = 2*p)
    {i : ℕ} (hp : (s.a i).Prime) (hp2 : s.a i ≠ 2) :
    spanTickValue (s.a (i+1)) := by
  obtain ⟨n, hn⟩ := every_prime_introduced s hp
  have hi : n+1 = i := s.injective (firstMultiple_next_prime s hn hp2)
  have hfirst := hpattern n (s.a i) hn hp2
  have htick := firstMultiple_next_three_of_twice s hn hp2 hfirst
  have hnext : n+2 = i+1 := by omega
  exact ⟨s.a i, hp, hp2, by rwa [hnext] at htick⟩

/-- Exact manuscript bound for the maximum observed non-tick value.
The sole extra hypothesis says that each observed odd prime is followed
by a tick value; it contains no rate or counting assumption. -/
theorem GreedySeq.nonTickTop_quadratic_of_prime_successors (s : GreedySeq)
    (t : ℕ) (he : 9 ≤ frontier s t)
    (hnext : ∀ i, i < t → (s.a i).Prime → s.a i ≠ 2 →
      spanTickValue (s.a (i+1))) :
    (nonTickTop s t : ℝ) - (frontier s t : ℝ) ≤
      2 * (earlyEvenCount s t + 1 : ℕ)^2 +
      2 * (earlyEvenCount s t + 1 : ℕ) *
        Real.sqrt ((earlyEvenCount s t + 1 : ℕ)^2 + (frontier s t : ℝ)) := by
  by_cases htop : nonTickTop s t ≤ frontier s t
  · have htopreal : (nonTickTop s t : ℝ) ≤ (frontier s t : ℝ) := by
      exact_mod_cast htop
    have hnon := Real.sqrt_nonneg
      ((earlyEvenCount s t + 1 : ℕ)^2 + (frontier s t : ℝ))
    have hk := Nat.cast_nonneg (α := ℝ) (earlyEvenCount s t+1)
    nlinarith [sq_nonneg ((earlyEvenCount s t+1 : ℕ) : ℝ)]
  obtain ⟨n, hnt, hnot, hval⟩ := nonTickTop_attained s t
  have hlarge : frontier s t < s.a n := by omega
  have hn : 2 ≤ n := by
    by_contra h
    have hc : n = 0 ∨ n = 1 := by omega
    rcases hc with hc | hc
    · rw [hc, s.seed_zero] at hlarge
      omega
    · rw [hc, s.seed_one] at hlarge
      omega
  have hnprev : n-1+1 = n := by omega
  have hprevobs : n-1 ≤ t := by omega
  have hodd : ¬ 2 ∣ s.a (n-1) := by
    intro heven
    have hsmall := next_after_even_le_frontier s heven
    rw [hnprev] at hsmall
    have hmono := frontier_monotone s hprevobs
    omega
  have hneone : s.a (n-1) ≠ 1 := by
    intro hone
    have hindex : n-1 = 0 := s.injective (hone.trans s.seed_zero.symm)
    omega
  have hqsq : (s.a (n-1)).minFac^2 ≤ s.a n := by
    by_cases htick : spanTickValue (s.a (n-1))
    · obtain ⟨p, _, _, hmul⟩ := htick
      have hd : 3 ∣ s.a (n-1) := hmul ▸ Nat.dvd_mul_right 3 p
      have hqthree := Nat.minFac_le_of_dvd (by omega : 2 ≤ 3) hd
      nlinarith
    ·
      have hcomp : ¬ (s.a (n-1)).Prime := by
        intro hp
        have hp2 : s.a (n-1) ≠ 2 := by
          intro htwo
          apply hodd
          rw [htwo]
        have hcur := hnext (n-1) (by omega) hp hp2
        rw [hnprev] at hcur
        exact hnot hcur
      have hbound := nonTick_le_top s hprevobs htick
      rw [hval] at hbound
      exact (Nat.minFac_sq_le_self (s.positive (n-1)) hcomp).trans hbound
  rw [hval]
  exact s.quadratic_span_of_prime_square_bound hn (by omega)
    (Nat.minFac_prime hneone) (Nat.minFac_dvd _) hqsq

/-- The Top theorem consumes the same explicit structural obligation as
`EarlyEvens.PrimeIntroductionPattern`, written out to avoid a build dependency.
It does not claim that this obligation has already been proved. -/
theorem GreedySeq.nonTickTop_quadratic_of_prime_pattern (s : GreedySeq)
    (t : ℕ) (he : 9 ≤ frontier s t)
    (hpattern : ∀ n p, NewPrimeAt s n p → p ≠ 2 → s.a n = 2*p) :
    (nonTickTop s t : ℝ) - (frontier s t : ℝ) ≤
      2 * (earlyEvenCount s t + 1 : ℕ)^2 +
      2 * (earlyEvenCount s t + 1 : ℕ) *
        Real.sqrt ((earlyEvenCount s t + 1 : ℕ)^2 + (frontier s t : ℝ)) := by
  apply s.nonTickTop_quadratic_of_prime_successors t he
  intro i _ hp hp2
  exact s.odd_prime_successor_tick_of_pattern hpattern hp hp2

theorem actualA_nonTickTop_quadratic_of_prime_pattern (t : ℕ)
    (he : 9 ≤ frontier canonical t)
    (hpattern : ∀ n p, NewPrimeAt canonical n p → p ≠ 2 → actualA n = 2*p) :
    (nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ) ≤
      2 * (earlyEvenCount canonical t + 1 : ℕ)^2 +
      2 * (earlyEvenCount canonical t + 1 : ℕ) *
        Real.sqrt ((earlyEvenCount canonical t + 1 : ℕ)^2 +
          (frontier canonical t : ℝ)) :=
  canonical.nonTickTop_quadratic_of_prime_pattern t he hpattern

end EKG
