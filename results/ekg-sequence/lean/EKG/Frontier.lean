import EKG.Canonical
import EKG.Crossings
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat

namespace EKG

theorem unused_even_exists (s : GreedySeq) (t : ℕ) :
    ∃ m, 0 < m ∧ 2 ∣ m ∧ ¬ UsedBefore s.a (t+1) m := by
  let M := (Finset.range (t+1)).sup s.a
  refine ⟨2*(M+1), by omega, Nat.dvd_mul_right 2 (M+1), ?_⟩
  rintro ⟨i, hi, he⟩
  have hb : s.a i ≤ M := Finset.le_sup (Finset.mem_range.mpr hi)
  omega

/-- Least unused positive even after the zero-based entries `0, …, t`. -/
noncomputable def frontier (s : GreedySeq) (t : ℕ) : ℕ := by
  classical
  exact Nat.find (unused_even_exists s t)

theorem frontier_spec (s : GreedySeq) (t : ℕ) :
    0 < frontier s t ∧ 2 ∣ frontier s t ∧
      ¬ UsedBefore s.a (t+1) (frontier s t) := by
  classical
  exact Nat.find_spec (unused_even_exists s t)

theorem frontier_le (s : GreedySeq) (t m : ℕ) (hm : 0 < m)
    (heven : 2 ∣ m) (hfree : ¬ UsedBefore s.a (t+1) m) :
    frontier s t ≤ m := by
  classical
  exact Nat.find_min' (unused_even_exists s t) ⟨hm, heven, hfree⟩

theorem frontier_monotone (s : GreedySeq) : Monotone (frontier s) := by
  classical
  intro t u htu
  change Nat.find (unused_even_exists s t) ≤ frontier s u
  apply Nat.find_min'
  have hu := frontier_spec s u
  refine ⟨hu.1, hu.2.1, ?_⟩
  rintro ⟨i, hi, he⟩
  exact hu.2.2 ⟨i, by omega, he⟩

theorem frontier_prime_count_monotone (s : GreedySeq) :
    Monotone (fun t => Nat.primeCounting (Nat.sqrt (frontier s t))) := by
  intro t u htu
  exact Nat.monotone_primeCounting (Nat.sqrt_le_sqrt (frontier_monotone s htu))

noncomputable def earlyEvenCount (s : GreedySeq) (t : ℕ) : ℕ := by
  classical
  exact (((Finset.range (t+1)).image s.a).filter
    (fun w => 2 ∣ w ∧ frontier s t < w)).card

theorem smaller_even_used (s : GreedySeq) {t m : ℕ}
    (hm : 0 < m) (heven : 2 ∣ m) (hlt : m < frontier s t) :
    UsedBefore s.a (t+1) m := by
  classical
  by_contra hfree
  have := frontier_le s t m hm heven hfree
  omega

theorem frontier_ne_used (s : GreedySeq) {i t : ℕ} (hi : i ≤ t) :
    s.a i ≠ frontier s t := by
  intro he
  exact (frontier_spec s t).2.2 ⟨i, by omega, he⟩

theorem frontier_ge_four (s : GreedySeq) {t : ℕ} (ht : 1 ≤ t) :
    4 ≤ frontier s t := by
  have hp := frontier_spec s t
  have hne : frontier s t ≠ 2 := by
    intro he
    exact hp.2.2 ⟨1, by omega, s.seed_one.trans he.symm⟩
  obtain ⟨k, hk⟩ := hp.2.1
  omega

/-- An even predecessor makes the current least unused even eligible. -/
theorem next_after_even_le_frontier (s : GreedySeq) {i : ℕ}
    (heven : 2 ∣ s.a i) : s.a (i+1) ≤ frontier s i := by
  have hi : 1 ≤ i := by
    by_contra h
    have hz : i = 0 := by omega
    rw [hz, s.seed_zero] at heven
    norm_num at heven
  have hp := frontier_spec s i
  apply s.minimal (i+1) (by omega) (frontier s i) hp.1 hp.2.2
  simpa using (show SharedPrime (s.a i) (frontier s i) from
    ⟨2, Nat.prime_two, heven, hp.2.1⟩)

/-- At a later observation time, the frontier is still absent, making the
successor bound strict whenever the successor has already been observed. -/
theorem next_after_even_lt_final_frontier (s : GreedySeq) {i t : ℕ}
    (hit : i < t) (heven : 2 ∣ s.a i) : s.a (i+1) < frontier s t := by
  have hle := (next_after_even_le_frontier s heven).trans
    (frontier_monotone s (by omega : i ≤ t))
  exact lt_of_le_of_ne hle (frontier_ne_used s (by omega))

/-- Every early even except possibly the last entry supplies an actual
strict downward crossing of the final frontier. -/
theorem early_even_forces_down (s : GreedySeq) {i t : ℕ}
    (hit : i < t) (heven : 2 ∣ s.a i) (hearly : frontier s t < s.a i) :
    frontier s t ≤ s.a i ∧ s.a (i+1) < frontier s t :=
  ⟨hearly.le, next_after_even_lt_final_frontier s hit heven⟩

theorem unused_multiple_exists (s : GreedySeq) (q : ℕ) (hq : 0 < q) (t : ℕ) :
    ∃ m, 0 < m ∧ q ∣ m ∧ ¬ UsedBefore s.a (t+1) m := by
  let M := (Finset.range (t+1)).sup s.a
  have hqone : 1 ≤ q := hq
  refine ⟨q*(M+1), Nat.mul_pos hq (by omega), Nat.dvd_mul_right q (M+1), ?_⟩
  rintro ⟨i, hi, he⟩
  have hb : s.a i ≤ M := Finset.le_sup (Finset.mem_range.mpr hi)
  have hmul : M+1 ≤ q*(M+1) := by nlinarith
  omega

/-- Least unused positive `q`-multiple after entries `0, …, t`. -/
noncomputable def multipleFrontier (s : GreedySeq) (q : ℕ) (hqpos : 0 < q)
    (t : ℕ) : ℕ := by
  classical
  exact Nat.find (unused_multiple_exists s q hqpos t)

theorem multipleFrontier_spec (s : GreedySeq) (q : ℕ) (hqpos : 0 < q) (t : ℕ) :
    0 < multipleFrontier s q hqpos t ∧ q ∣ multipleFrontier s q hqpos t ∧
      ¬ UsedBefore s.a (t+1) (multipleFrontier s q hqpos t) := by
  classical
  exact Nat.find_spec (unused_multiple_exists s q hqpos t)

theorem multipleFrontier_le (s : GreedySeq) (q : ℕ) (hqpos : 0 < q)
    (t m : ℕ) (hm : 0 < m) (hqm : q ∣ m)
    (hfree : ¬ UsedBefore s.a (t+1) m) : multipleFrontier s q hqpos t ≤ m := by
  classical
  exact Nat.find_min' (unused_multiple_exists s q hqpos t) ⟨hm, hqm, hfree⟩

theorem smaller_multiple_used_before_frontier (s : GreedySeq) (q : ℕ)
    (hqpos : 0 < q) {t m : ℕ} (hm : 0 < m) (hqm : q ∣ m)
    (hlt : m < multipleFrontier s q hqpos t) : UsedBefore s.a (t+1) m := by
  classical
  by_contra hfree
  have := multipleFrontier_le s q hqpos t m hm hqm hfree
  omega

theorem multipleFrontier_monotone (s : GreedySeq) (q : ℕ) (hqpos : 0 < q) :
    Monotone (multipleFrontier s q hqpos) := by
  intro t u htu
  have hu := multipleFrontier_spec s q hqpos u
  apply multipleFrontier_le s q hqpos t _ hu.1 hu.2.1
  rintro ⟨i, hi, he⟩
  exact hu.2.2 ⟨i, by omega, he⟩

/-- The least unused multiple is eligible whenever its prime divides the
current term; this follows directly from the canonical greedy specification. -/
theorem next_le_multipleFrontier (s : GreedySeq) {q i : ℕ} (hq : q.Prime)
    (hqi : q ∣ s.a i) : s.a (i+1) ≤ multipleFrontier s q hq.pos i := by
  have hi : 1 ≤ i := by
    by_contra h
    have hz : i = 0 := by omega
    rw [hz, s.seed_zero] at hqi
    have hqone : q = 1 := Nat.dvd_one.mp hqi
    have := hq.two_le
    omega
  have hp := multipleFrontier_spec s q hq.pos i
  apply s.minimal (i+1) (by omega) _ hp.1 hp.2.2
  simpa using (show SharedPrime (s.a i) (multipleFrontier s q hq.pos i) from
    ⟨q, hq, hqi, hp.2.1⟩)

theorem next_lt_final_multipleFrontier (s : GreedySeq) {q i t : ℕ}
    (hq : q.Prime) (hqi : q ∣ s.a i) (hit : i < t) :
    s.a (i+1) < multipleFrontier s q hq.pos t := by
  have hle := (next_le_multipleFrontier s hq hqi).trans
    (multipleFrontier_monotone s q hq.pos (by omega : i ≤ t))
  apply lt_of_le_of_ne hle
  intro he
  exact (multipleFrontier_spec s q hq.pos t).2.2 ⟨i+1, by omega, he⟩

/-- Specialization used for the prime-tick self-pairing argument. -/
noncomputable def multiple3Frontier (s : GreedySeq) (t : ℕ) : ℕ :=
  multipleFrontier s 3 (by omega) t

theorem multiple3Frontier_spec (s : GreedySeq) (t : ℕ) :
    0 < multiple3Frontier s t ∧ 3 ∣ multiple3Frontier s t ∧
      ¬ UsedBefore s.a (t+1) (multiple3Frontier s t) := by
  exact multipleFrontier_spec s 3 (by omega) t

theorem smaller_multiple3_used (s : GreedySeq) {t m : ℕ}
    (hm : 0 < m) (hthree : 3 ∣ m) (hlt : m < multiple3Frontier s t) :
    UsedBefore s.a (t+1) m := by
  exact smaller_multiple_used_before_frontier s 3 (by omega) hm hthree hlt

theorem multiple3Frontier_monotone (s : GreedySeq) : Monotone (multiple3Frontier s) := by
  exact multipleFrontier_monotone s 3 (by omega)

/-- The multiples of six strictly between the two frontiers are early evens.
This is the exact finite counting input to the manuscript's span bound. -/
theorem multiple6_interval_card_le_earlyEvenCount (s : GreedySeq) (t : ℕ) :
    (Finset.Ico (frontier s t / 6 + 1) ((multiple3Frontier s t + 5) / 6)).card ≤
      earlyEvenCount s t := by
  classical
  unfold earlyEvenCount
  apply Finset.card_le_card_of_injOn (fun k : ℕ => 6*k)
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    have he : frontier s t < 6*k := by omega
    have hb : 6*k < multiple3Frontier s t := by omega
    have hu := smaller_multiple3_used s (by omega : 0 < 6*k)
      (⟨2*k, by omega⟩ : 3 ∣ 6*k) hb
    obtain ⟨i, hi, hval⟩ := hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hval⟩, ?_⟩
    exact ⟨⟨3*k, by dsimp; omega⟩, he⟩
  · intro i _ j _ hij
    dsimp at hij
    omega

/-- Count-to-span conversion, with no sieve or prime-pattern assumption. -/
theorem multiple3Frontier_le_frontier_add (s : GreedySeq) (t : ℕ) :
    multiple3Frontier s t ≤ frontier s t + 6 * earlyEvenCount s t + 6 := by
  have hc := multiple6_interval_card_le_earlyEvenCount s t
  rw [Nat.card_Ico] at hc
  omega

/-- If the only new even value in a window is its initial frontier, all
intermediate evens below the final frontier were already early evens. -/
theorem frontier_advance_of_only_new_even (s : GreedySeq) {u t : ℕ}
    (hut : u ≤ t)
    (hnew : ∀ i, u < i → i ≤ t → 2 ∣ s.a i → s.a i = frontier s u) :
    frontier s t ≤ frontier s u + 2 * earlyEvenCount s u + 2 := by
  classical
  have hc : (Finset.Ico (frontier s u / 2 + 1) (frontier s t / 2)).card ≤
      earlyEvenCount s u := by
    unfold earlyEvenCount
    apply Finset.card_le_card_of_injOn (fun k : ℕ => 2*k)
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      have he : frontier s u < 2*k := by omega
      have hb : 2*k < frontier s t := by omega
      have hd : 2 ∣ 2*k := ⟨k, rfl⟩
      obtain ⟨i, hi, hval⟩ := smaller_even_used s (by omega : 0 < 2*k) hd hb
      have hiu : i ≤ u := by
        by_contra h
        have heq := hnew i (by omega) (by omega) (by rw [hval]; exact hd)
        omega
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), hval⟩,
        hd, he⟩
    · intro i _ j _ hij
      dsimp at hij
      omega
  rw [Nat.card_Ico] at hc
  have hmono := frontier_monotone s hut
  obtain ⟨ku, hu⟩ := (frontier_spec s u).2.1
  obtain ⟨kt, ht⟩ := (frontier_spec s t).2.1
  omega

/-- Three-entry specialization; the two later entries need only be odd. -/
theorem frontier_advance_three (s : GreedySeq) (u : ℕ)
    (hfirst : s.a (u+1) = frontier s u)
    (hsecond : ¬ 2 ∣ s.a (u+2)) (hthird : ¬ 2 ∣ s.a (u+3)) :
    frontier s (u+3) ≤ frontier s u + 2 * earlyEvenCount s u + 2 := by
  apply frontier_advance_of_only_new_even s (by omega : u ≤ u+3)
  intro i hi hit heven
  have hc : i = u+1 ∨ i = u+2 ∨ i = u+3 := by omega
  rcases hc with rfl | rfl | rfl
  · exact hfirst
  · exact False.elim (hsecond heven)
  · exact False.elim (hthird heven)

/-- The manuscript's frontier advance across an actual `2p,p,3p` tick.
The tick pattern is an explicit input; this theorem does not presume it. -/
theorem frontier_advance_prime_tick (s : GreedySeq) (u p : ℕ)
    (hp : p.Prime) (hpodd : p ≠ 2) (he : frontier s u = 2*p)
    (hfirst : s.a (u+1) = 2*p) (hsecond : s.a (u+2) = p)
    (hthird : s.a (u+3) = 3*p) :
    frontier s (u+3) ≤ 2*p + 2 * earlyEvenCount s u + 2 := by
  have hnp : ¬ 2 ∣ p := by
    intro hd
    exact hpodd ((hp.dvd_iff_eq (by omega : 2 ≠ 1)).mp hd)
  have hnp3 : ¬ 2 ∣ 3*p :=
    Nat.prime_two.not_dvd_mul (by decide : ¬ 2 ∣ 3) hnp
  have hb := frontier_advance_three s u (hfirst.trans he.symm)
    (by simpa only [hsecond] using hnp) (by simpa only [hthird] using hnp3)
  simpa only [he] using hb

/-- Endpoint-indexed form for the recent unpaired-tick interval. -/
theorem frontier_advance_tick_block (s : GreedySeq) {k p : ℕ} (hk : 3 ≤ k)
    (hfirst : s.a (k-2) = 2*p) (hsecond : ¬ 2 ∣ s.a (k-1))
    (hthird : ¬ 2 ∣ s.a k) (he : frontier s (k-3) = 2*p) :
    frontier s k ≤ 2*p + 2 * earlyEvenCount s (k-3) + 2 := by
  have h1 : k-3+1 = k-2 := by omega
  have h2 : k-3+2 = k-1 := by omega
  have h3 : k-3+3 = k := by omega
  have hb := frontier_advance_three s (k-3)
    (by rw [h1]; exact hfirst.trans he.symm)
    (by rwa [h2]) (by rwa [h3])
  simpa only [h3, he] using hb

end EKG
