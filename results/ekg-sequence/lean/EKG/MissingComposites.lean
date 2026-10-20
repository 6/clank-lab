import EKG.EarlyEvens
import EKG.Span
import EKG.VerifiedCounts

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-! The missing-composite window argument. All finite sets use source
indices, so a source in `[b+1,t)` means a crossing into `(b+1,t]`.
The prime introduction pattern is an explicit structural hypothesis. -/
namespace EKG
namespace MissingComposites

noncomputable def windowUps (s : GreedySeq) (h start stop : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico start stop).filter (fun i => s.a i < h ∧ h ≤ s.a (i+1))

noncomputable def windowDowns (s : GreedySeq) (h start stop : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico start stop).filter (fun i => h ≤ s.a i ∧ s.a (i+1) < h)

theorem window_balance (s : GreedySeq) (h start stop : ℕ) (hst : start ≤ stop) :
    (windowDowns s h start stop).card ≤ (windowUps s h start stop).card + 1 := by
  classical
  have hU : (windowUps s h start stop).card =
      upCount (fun n => s.a (start+n)) h (stop-start) := by
    rw [upCount_eq_card]
    symm
    apply Finset.card_bij (fun i _ => start+i)
    · intro i hi
      obtain ⟨hir, hlo, hhi⟩ := Finset.mem_filter.mp hi
      have hil := Finset.mem_range.mp hir
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
        hlo, by simpa [Nat.add_assoc] using hhi⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      obtain ⟨hjr, hlo, hhi⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjl, hju⟩ := Finset.mem_Ico.mp hjr
      refine ⟨j-start, ?_, by omega⟩
      have he : start+(j-start) = j := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        by simpa [he] using hlo, by simpa [← Nat.add_assoc, he] using hhi⟩
  have hD : (windowDowns s h start stop).card =
      downCount (fun n => s.a (start+n)) h (stop-start) := by
    rw [downCount_eq_card]
    symm
    apply Finset.card_bij (fun i _ => start+i)
    · intro i hi
      obtain ⟨hir, hlo, hhi⟩ := Finset.mem_filter.mp hi
      have hil := Finset.mem_range.mp hir
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
        hlo, by simpa [Nat.add_assoc] using hhi⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      obtain ⟨hjr, hlo, hhi⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjl, hju⟩ := Finset.mem_Ico.mp hjr
      refine ⟨j-start, ?_, by omega⟩
      have he : start+(j-start) = j := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        by simpa [he] using hlo, by simpa [← Nat.add_assoc, he] using hhi⟩
  rw [hU, hD]
  exact window_down_le_up_add_one s.a h start (stop-start)

theorem successor_lt_missing (s : GreedySeq) {i t h q : ℕ}
    (hit : i < t) (hh : 0 < h) (hfree : ¬ UsedBefore s.a (t+1) h)
    (hq : q.Prime) (hqa : q ∣ s.a i) (hqh : q ∣ h) : s.a (i+1) < h := by
  have hi : 1 ≤ i := by
    by_contra hn
    have hz : i = 0 := by omega
    rw [hz, s.seed_zero] at hqa
    exact hq.ne_one (Nat.dvd_one.mp hqa)
  have hlocal : ¬ UsedBefore s.a (i+1) h := by
    rintro ⟨j, hj, he⟩
    exact hfree ⟨j, by omega, he⟩
  have hle := s.minimal (i+1) (by omega) h hh hlocal
    (by simpa using (show SharedPrime (s.a i) h from ⟨q, hq, hqa, hqh⟩))
  have hne : s.a (i+1) ≠ h := fun he => hfree ⟨i+1, by omega, he⟩
  omega

noncomputable def forcedDowns (s : GreedySeq) (h q b t : ℕ) : Finset ℕ := by
  classical
  exact (windowDowns s h (b+1) t).filter (fun i => 2*q ∣ s.a i)

theorem progression_card_le_forced (s : GreedySeq) {h q b t : ℕ}
    (hh : 0 < h) (hq : q.Prime) (hqh : q ∣ h)
    (hfree : ¬ UsedBefore s.a (t+1) h) (hearlier : frontier s b ≤ h) :
    (progressionIndices h (frontier s t) (2*q)).card ≤
      earlyEvenCount s b + (forcedDowns s h q b t).card + 1 := by
  classical
  let A := (((Finset.range (b+1)).image s.a).filter
    (fun w => 2 ∣ w ∧ frontier s b < w))
  let D := (forcedDowns s h q b t).image s.a
  have hc : (progressionIndices h (frontier s t) (2*q)).card ≤
      ((A ∪ D) ∪ {s.a t}).card := by
    apply Finset.card_le_card_of_injOn (fun j : ℕ => (2*q)*j)
    · intro j hj
      obtain ⟨hl, hu⟩ := progressionIndices_bounds (by have := hq.pos; omega) hj
      have hdiv : 2*q ∣ (2*q)*j := Nat.dvd_mul_right _ _
      have heven : 2 ∣ (2*q)*j := dvd_mul_of_dvd_left (Nat.dvd_mul_right 2 q) j
      obtain ⟨i, hi, hval⟩ := smaller_even_used s (by omega) heven hu
      change s.a i = (2*q)*j at hval
      by_cases hib : i ≤ b
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
            ⟨i, Finset.mem_range.mpr (by omega), hval⟩, heven, by dsimp; omega⟩))))
      · by_cases hit : i < t
        · apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_image.mpr
          refine ⟨i, Finset.mem_filter.mpr ⟨?_, by rwa [hval]⟩, hval⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Ico.mpr ⟨by omega, hit⟩, by omega, ?_⟩
          apply successor_lt_missing s hit hh hfree hq _ hqh
          rw [hval]
          exact dvd_mul_of_dvd_left (Nat.dvd_mul_left q 2) j
        · have hieq : i = t := by omega
          subst i
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr hval.symm))
    · intro i _ j _ heq
      dsimp at heq
      have := hq.pos
      nlinarith
  have hfirst := Finset.card_union_le (A ∪ D) {s.a t}
  have hsecond := Finset.card_union_le A D
  have himage : D.card ≤ (forcedDowns s h q b t).card := Finset.card_image_le
  have hA : A.card = earlyEvenCount s b := rfl
  have hone : ({s.a t} : Finset ℕ).card = 1 := Finset.card_singleton _
  omega

theorem minFac_ge_three_of_missing (s : GreedySeq) {h t : ℕ}
    (hh : 1 < h) (hbelow : h < frontier s t)
    (hfree : ¬ UsedBefore s.a (t+1) h) : 3 ≤ h.minFac := by
  have hp := Nat.minFac_prime (by omega : h ≠ 1)
  have hodd : ¬ 2 ∣ h := fun hd => hfree (smaller_even_used s (by omega) hd hbelow)
  have hne : h.minFac ≠ 2 := by
    intro he
    exact hodd (he ▸ Nat.minFac_dvd h)
  have := hp.two_le
  omega

theorem prime_up_block (s : GreedySeq) (hpattern : PrimePatternForCounts s)
    {h i : ℕ} (hh : 15 ≤ h) (hp : (s.a i).Prime)
    (hcross : s.a i < h ∧ h ≤ s.a (i+1)) :
    3 ≤ i ∧ s.a (i-1) = 2*s.a i ∧ s.a (i+1) = 3*s.a i ∧
      frontier s (i-2) = 2*s.a i := by
  have hp2 : s.a i ≠ 2 := by
    intro he
    have hi1 : i = 1 := s.injective (he.trans s.seed_one.symm)
    have hv : s.a 2 = 4 := FiniteBase.first_thirteen s (by omega)
    rw [hi1, hv] at hcross
    omega
  obtain ⟨hi3, hnew⟩ := prime_occurrence_backlink s hp hp2 rfl
  have hfirst := hpattern (i-1) (s.a i) hnew hp2
  have htick := firstMultiple_next_three_of_twice s hnew hp2 hfirst
  have hbefore := firstMultiple_frontier_of_twice s hnew hp2 hfirst
  have he1 : i-1+2 = i+1 := by omega
  have he2 : i-1-1 = i-2 := by omega
  exact ⟨hi3, hfirst, by rwa [he1] at htick, by rwa [he2] at hbefore⟩

/-- Interior prime ups cancel against preceding downs. At most one prime
up has its source in the two boundary positions. -/
theorem forced_downs_card_le (s : GreedySeq) (hpattern : PrimePatternForCounts s)
    {h b t : ℕ} (hh : 15 ≤ h) (hnp : ¬ h.Prime)
    (hbelow : h < frontier s t) (hfree : ¬ UsedBefore s.a (t+1) h)
    (hbt : b+1 ≤ t) (hstart : h < frontier s (b+1)) :
    (forcedDowns s h h.minFac b t).card ≤ Nat.primeCounting (Nat.sqrt h) + 2 := by
  classical
  let U := windowUps s h (b+1) t
  let D := windowDowns s h (b+1) t
  let F := forcedDowns s h h.minFac b t
  let C := U.filter (fun i => ¬ (s.a i).Prime)
  let P := U.filter (fun i => (s.a i).Prime)
  let T := P.filter (fun i => b+3 ≤ i)
  let Q := P.filter (fun i => ¬ b+3 ≤ i)
  let J := T.image (fun i => i-1)
  have hq := Nat.minFac_prime (by omega : h ≠ 1)
  have hq3 := minFac_ge_three_of_missing s (by omega) hbelow hfree
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < h) hnp
  have hblock : ∀ i ∈ P, 3 ≤ i ∧ s.a (i-1) = 2*s.a i ∧
      s.a (i+1) = 3*s.a i ∧ frontier s (i-2) = 2*s.a i := by
    intro i hi
    obtain ⟨hui, hp⟩ := Finset.mem_filter.mp hi
    exact prime_up_block s hpattern hh hp (Finset.mem_filter.mp hui).2
  have hJD : J ⊆ D := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hip, hib⟩ := Finset.mem_filter.mp hi
    have hb := hblock i hip
    have hir := Finset.mem_Ico.mp (Finset.mem_filter.mp
      (Finset.mem_filter.mp hip).1).1
    have hhigh := hstart.trans_le (frontier_monotone s (show b+1 ≤ i-2 by omega))
    rw [hb.2.2.2] at hhigh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · rw [hb.2.1]
      omega
    · have he : i-1+1 = i := by omega
      rw [he]
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hip).1).2.1
  have hdis : Disjoint F J := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    have hip := (Finset.mem_filter.mp hi).1
    have hb := hblock i hip
    have hdiv := (Finset.mem_filter.mp hj).2
    rw [hb.2.1] at hdiv
    have hqp : h.minFac ∣ s.a i := Nat.dvd_of_mul_dvd_mul_left (by omega) hdiv
    have hprime := (Finset.mem_filter.mp hip).2
    have heq : h.minFac = s.a i := ((hprime.dvd_iff_eq hq.ne_one).mp hqp).symm
    have hu := (Finset.mem_filter.mp (Finset.mem_filter.mp hip).1).2.2
    rw [hb.2.2.1, ← heq] at hu
    have hne : h ≠ 3*h.minFac := by
      intro he
      apply hfree
      have hit := (Finset.mem_Ico.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp hip).1).1).2
      exact ⟨i+1, by omega, hb.2.2.1.trans (by rw [← heq]; exact he.symm)⟩
    have hlt : h < 3*h.minFac := by omega
    nlinarith
  have hJcard : J.card = T.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    dsimp at he
    have hi3 := (hblock i (Finset.mem_filter.mp hi).1).1
    have hj3 := (hblock j (Finset.mem_filter.mp hj).1).1
    omega
  have hdown : F.card + T.card ≤ D.card := by
    rw [← hJcard, ← Finset.card_union_of_disjoint hdis]
    apply Finset.card_le_card
    exact Finset.union_subset (Finset.filter_subset _ _) hJD
  have hQ : Q.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hip, hib⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjp, hjb⟩ := Finset.mem_filter.mp hj
    have hir := Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hip).1).1
    have hjr := Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hjp).1).1
    have hnotnext : ∀ k ∈ P, ¬ (s.a (k+1)).Prime := by
      intro k hk hpk
      have hb := hblock k hk
      rw [hb.2.2.1] at hpk
      have hd : 3 ∣ 3*s.a k := Nat.dvd_mul_right _ _
      have he := (hpk.dvd_iff_eq (by omega : 3 ≠ 1)).mp hd
      have hp0 := (Finset.mem_filter.mp hk).2.two_le
      omega
    by_contra hne
    have hcases : j = i+1 ∨ i = j+1 := by omega
    rcases hcases with he | he
    · exact hnotnext i hip (he ▸ (Finset.mem_filter.mp hjp).2)
    · exact hnotnext j hjp (he ▸ (Finset.mem_filter.mp hip).2)
  have hC : C.card ≤ Nat.primeCounting (Nat.sqrt h) := by
    apply s.composite_upcrossings_bound
    · intro i hi
      obtain ⟨hui, hnp'⟩ := Finset.mem_filter.mp hi
      have hi1 : 1 < s.a i := by
        have hp := s.positive i
        have hir := (Finset.mem_Ico.mp (Finset.mem_filter.mp hui).1).1
        have hne : s.a i ≠ 1 := by
          intro he
          have := s.injective (he.trans s.seed_zero.symm)
          omega
        omega
      exact ⟨hi1, hnp'⟩
    · intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hUC : P.card + C.card = U.card := Finset.card_filter_add_card_filter_not _
  have hPT : T.card + Q.card = P.card := Finset.card_filter_add_card_filter_not _
  have hbalance := window_balance s h (b+1) t hbt
  change D.card ≤ U.card + 1 at hbalance
  change F.card ≤ Nat.primeCounting (Nat.sqrt h) + 2
  omega

/-- Full geometric estimate from structural pattern and an early-even
bound at the last observation before the frontier passes the hole. -/
theorem hole_span (s : GreedySeq) (hpattern : PrimePatternForCounts s)
    {h b t K : ℕ} (hh : 15 ≤ h) (hnp : ¬ h.Prime)
    (hbelow : h < frontier s t) (hfree : ¬ UsedBefore s.a (t+1) h)
    (hbt : b+1 ≤ t) (hearlier : frontier s b ≤ h)
    (hstart : h < frontier s (b+1)) (hK : earlyEvenCount s b ≤ K) :
    frontier s t - h ≤ 2*h.minFac*(Nat.primeCounting (Nat.sqrt h)+K+4) := by
  have hf := forced_downs_card_le s hpattern hh hnp hbelow hfree hbt hstart
  have hp := Nat.minFac_prime (by omega : h ≠ 1)
  have hc := progression_card_le_forced s (by omega : 0 < h) hp
    (Nat.minFac_dvd h) hfree hearlier
  have hc' : (progressionIndices h (frontier s t) (2*h.minFac)).card ≤
      Nat.primeCounting (Nat.sqrt h)+K+3 := by omega
  have hs : frontier s t ≤ h + 2*h.minFac*(Nat.primeCounting (Nat.sqrt h)+K+4) := by
    simpa only [Nat.add_assoc] using
      (progression_span_le (by have := hp.pos; omega) hc')
  omega

/-- The first frontier passage is chosen from the observed finite prefix,
not assumed as a separate window hypothesis. -/
theorem first_passage (s : GreedySeq) {h t : ℕ} (hh : 15 ≤ h)
    (hbelow : h < frontier s t) :
    ∃ b, b+1 ≤ t ∧ frontier s b ≤ h ∧ h < frontier s (b+1) := by
  classical
  let hex : ∃ r, h < frontier s r := ⟨t, hbelow⟩
  let r := Nat.find hex
  have hr : h < frontier s r := Nat.find_spec hex
  have hrt : r ≤ t := Nat.find_min' hex hbelow
  have hr0 : 0 < r := by
    by_contra hn
    have he : r = 0 := by omega
    have hz : frontier s 0 = 2 := FiniteBase.frontier_eq s (by omega)
    rw [he, hz] at hr
    omega
  have hprev : frontier s (r-1) ≤ h := by
    have hn := Nat.find_min hex (show r-1 < r by omega)
    omega
  exact ⟨r-1, by omega, hprev, by simpa [show r-1+1 = r by omega] using hr⟩

/-- Manuscript Theorem holes, with exactly the two upstream structural
and bootstrap obligations shown as parameters. -/
theorem geometric_bound_of_pattern_and_bootstrap (s : GreedySeq)
    (hpattern : PrimePatternForCounts s)
    (hEE : ∀ u, earlyEvenCount s u ≤
      12*Nat.primeCounting (Nat.sqrt (frontier s u))+720)
    {h t : ℕ} (hh : 15 ≤ h) (hnp : ¬ h.Prime)
    (hbelow : h < frontier s t) (hfree : ¬ UsedBefore s.a (t+1) h) :
    frontier s t - h ≤ 2*h.minFac*(13*Nat.primeCounting (Nat.sqrt h)+724) := by
  obtain ⟨b, hbt, hearlier, hstart⟩ := first_passage s hh hbelow
  have hmono := Nat.monotone_primeCounting (Nat.sqrt_le_sqrt hearlier)
  have hK : earlyEvenCount s b ≤ 12*Nat.primeCounting (Nat.sqrt h)+720 := by
    have hb := hEE b
    omega
  have hs := hole_span s hpattern hh hnp hbelow hfree hbt hearlier hstart hK
  have he : Nat.primeCounting (Nat.sqrt h) +
      (12*Nat.primeCounting (Nat.sqrt h)+720) + 4 =
      13*Nat.primeCounting (Nat.sqrt h)+724 := by omega
  rw [he] at hs
  exact hs

end MissingComposites

/-- Unconditional manuscript Theorem holes for the greedy EKG sequence.
Both structural pattern and bootstrap estimates are proved upstream. -/
theorem GreedySeq.missing_composite_bound (s : GreedySeq) {h t : ℕ}
    (hh : 15 ≤ h) (hnp : ¬ h.Prime) (hbelow : h < frontier s t)
    (hfree : ¬ UsedBefore s.a (t+1) h) :
    frontier s t - h ≤ 2*h.minFac*(13*Nat.primeCounting (Nat.sqrt h)+724) :=
  MissingComposites.geometric_bound_of_pattern_and_bootstrap s
    (primeIntroductionPattern s) (early_even_bound s) hh hnp hbelow hfree

theorem actualA_missing_composite_bound {h t : ℕ}
    (hh : 15 ≤ h) (hnp : ¬ h.Prime) (hbelow : h < frontier canonical t)
    (hfree : ¬ UsedBefore actualA (t+1) h) :
    frontier canonical t - h ≤ 2*h.minFac*(13*Nat.primeCounting (Nat.sqrt h)+724) :=
  canonical.missing_composite_bound hh hnp hbelow hfree

end EKG
