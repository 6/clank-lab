import EKG.Frontier
import EKG.CrossingBounds
import EKG.Bootstrap
import Mathlib.Tactic.Tauto

namespace EKG

/-- Prime sources of upcrossings of the final even frontier. -/
noncomputable def primeUps (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (fun i => (s.a i).Prime ∧
    s.a i < frontier s t ∧ frontier s t ≤ s.a (i+1))

/-- Those prime upcrossings whose odd target immediately crosses down again.
The definition does not presume the prime-neighbor theorem. -/
noncomputable def pairedPrimeUps (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (primeUps s t).filter (fun i =>
    i+1 < t ∧ ¬ 2 ∣ s.a (i+1) ∧ s.a (i+2) < frontier s t)

noncomputable def unpairedPrimeUps (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact primeUps s t \ pairedPrimeUps s t

theorem earlyEvenCount_eq_index_card (s : GreedySeq) (t : ℕ) :
    earlyEvenCount s t = ((Finset.range (t+1)).filter
      (fun i => 2 ∣ s.a i ∧ frontier s t < s.a i)).card := by
  classical
  unfold earlyEvenCount
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ s.injective

/-- The cancellation step of Lemma EE, proved for the actual greedy sequence.
All self-paired prime crossings cancel against disjoint odd-base downs.
Only unpaired prime crossings and one endpoint remain. -/
theorem earlyEvenCount_le_unpaired (s : GreedySeq) (t : ℕ) (ht : 1 ≤ t) :
    earlyEvenCount s t ≤ Nat.primeCounting (Nat.sqrt (frontier s t)) +
      (unpairedPrimeUps s t).card + 1 := by
  classical
  let e := frontier s t
  let U := (Finset.range t).filter (fun i => s.a i < e ∧ e ≤ s.a (i+1))
  let D := (Finset.range t).filter (fun i => e ≤ s.a i ∧ s.a (i+1) < e)
  let F := (Finset.range t).filter (fun i => 2 ∣ s.a i ∧ e < s.a i)
  let C := U.filter (fun i => ¬ (s.a i).Prime)
  let P := pairedPrimeUps s t
  let Q := unpairedPrimeUps s t
  let J := P.image (fun i => i+1)
  have he : 4 ≤ e := frontier_ge_four s ht
  have hFD : F ⊆ D := by
    intro i hi
    obtain ⟨hit, heven, hhigh⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hit,
      early_even_forces_down s (Finset.mem_range.mp hit) heven hhigh⟩
  have hJD : J ⊆ D := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hu, hit, _, hlow⟩ := Finset.mem_filter.mp hi
    have hhigh := (Finset.mem_filter.mp hu).2.2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hit, hhigh, by simpa using hlow⟩
  have hdis : Disjoint F J := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    have hodd := (Finset.mem_filter.mp hi).2.2.1
    exact hodd (Finset.mem_filter.mp hj).2.1
  have hJcard : J.card = P.card :=
    Finset.card_image_of_injective _ (fun i j h => by omega)
  have hdown : F.card + P.card ≤ D.card := by
    rw [← hJcard, ← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hFD hJD)
  have hbalance : D.card ≤ U.card := by
    rw [← downCount_eq_card, ← upCount_eq_card]
    apply downCount_le_upCount
    rw [s.seed_zero]
    omega
  have hC : C.card ≤ Nat.primeCounting (Nat.sqrt e) := by
    apply s.composite_upcrossings_bound
    · intro i hi
      obtain ⟨hui, hnp⟩ := Finset.mem_filter.mp hi
      have hbig : 1 < s.a i := by
        have hp := s.positive i
        by_contra h
        have hi1 : s.a i = 1 := by omega
        have hi0 : i = 0 := s.injective (hi1.trans s.seed_zero.symm)
        have hc := (Finset.mem_filter.mp hui).2.2
        rw [hi0, s.seed_one] at hc
        omega
      exact ⟨hbig, hnp⟩
    · intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hUcard : U.card = C.card + (primeUps s t).card := by
    have hp : U.filter (fun i => (s.a i).Prime) = primeUps s t := by
      ext i
      simp only [U, primeUps, Finset.mem_filter]
      tauto
    rw [← hp]
    have hc := Finset.card_filter_add_card_filter_not (s := U) (p := fun i => (s.a i).Prime)
    dsimp [C]
    omega
  have hPsub : P ⊆ primeUps s t := Finset.filter_subset _ _
  have hPcard : (primeUps s t).card = P.card + Q.card := by
    have hc := Finset.card_sdiff_add_card_eq_card hPsub
    dsimp [P, Q, unpairedPrimeUps] at *
    omega
  have hFcard : earlyEvenCount s t ≤ F.card + 1 := by
    rw [earlyEvenCount_eq_index_card]
    change ((Finset.range (t+1)).filter
      (fun i => 2 ∣ s.a i ∧ e < s.a i)).card ≤ F.card + 1
    have hsubset : ((Finset.range (t+1)).filter
        (fun i => 2 ∣ s.a i ∧ e < s.a i)) ⊆ insert t F := by
      intro i hi
      obtain ⟨hir, hp⟩ := Finset.mem_filter.mp hi
      by_cases hit : i = t
      · exact Finset.mem_insert.mpr (Or.inl hit)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hir; omega), hp⟩))
    have hc := Finset.card_le_card hsubset
    have hd := Finset.card_insert_le t F
    omega
  dsimp [e, Q] at *
  omega

/-- A tick with B₃ below the final frontier supplies its own downward
crossing. No unproved global prime-pattern theorem is a dependency. -/
theorem tick_self_paired (s : GreedySeq) {t i p : ℕ}
    (hu : i ∈ primeUps s t) (hit : i+1 < t)
    (htick : s.a (i+1) = 3*p) (hodd : ¬ 2 ∣ 3*p)
    (hB : multiple3Frontier s (i+1) ≤ frontier s t) :
    i ∈ pairedPrimeUps s t := by
  classical
  have hb := multiple3Frontier_spec s (i+1)
  have hle : s.a (i+2) ≤ multiple3Frontier s (i+1) := by
    apply s.minimal (i+2) (by omega) _ hb.1 hb.2.2
    have hi : i+2-1 = i+1 := by omega
    rw [hi, htick]
    exact ⟨3, Nat.prime_three, Nat.dvd_mul_right 3 p, hb.2.1⟩
  have hne : s.a (i+2) ≠ frontier s t := frontier_ne_used s (by omega)
  apply Finset.mem_filter.mpr
  exact ⟨hu, hit, by rwa [htick], lt_of_le_of_ne (hle.trans hB) hne⟩

/-- The local arithmetic consequence of an actual tick block. The frontier
advance is derived by finite counting, not assumed. This local lemma does not
by itself establish that every prime upcrossing has the required block. -/
theorem unpaired_tick_near_frontier (s : GreedySeq) {t i p : ℕ}
    (hu : i ∈ unpairedPrimeUps s t) (hit : i+1 < t) (hi : 3 ≤ i)
    (hp : s.a i = p) (htwo : s.a (i-1) = 2*p)
    (htick : s.a (i+1) = 3*p) (hodd : ¬ 2 ∣ 3*p)
    (hbefore : frontier s (i-2) = 2*p) :
    2*p < frontier s t ∧ frontier s t <
      2*p + 8*priorPeak (earlyEvenCount s) t + 8 := by
  classical
  obtain ⟨hup, hnot⟩ := Finset.mem_sdiff.mp hu
  have hpodd : ¬ 2 ∣ s.a i := by
    rw [hp]
    intro hd
    exact hodd (dvd_mul_of_dvd_right hd 3)
  have hadvance : frontier s (i+1) ≤
      2*p + 2*earlyEvenCount s (i-2) + 2 := by
    have h1 : i+1-2 = i-1 := by omega
    have h2 : i+1-1 = i := by omega
    have h3 : i+1-3 = i-2 := by omega
    exact frontier_advance_tick_block s (k := i+1) (by omega)
      (by rwa [h1]) (by rwa [h2]) (by rwa [htick]) (by rwa [h3])
  have hB : frontier s t < multiple3Frontier s (i+1) := by
    by_contra h
    exact hnot (tick_self_paired s hup hit htick hodd (by omega))
  have hthree := multiple3Frontier_le_frontier_add s (i+1)
  have hk : earlyEvenCount s (i+1) ≤ priorPeak (earlyEvenCount s) t :=
    Finset.le_sup (Finset.mem_range.mpr hit)
  have hk' : earlyEvenCount s (i-2) ≤ priorPeak (earlyEvenCount s) t :=
    Finset.le_sup (Finset.mem_range.mpr (by omega))
  have hle : 2*p ≤ frontier s t := by
    rw [← hbefore]
    exact frontier_monotone s (by omega)
  have hne : 2*p ≠ frontier s t := by
    intro he
    exact frontier_ne_used s (i := i-1) (by omega) (htwo.trans he)
  exact ⟨lt_of_le_of_ne hle hne, by omega⟩

/-- Sieving the short interval produced by the unpaired-tick calculation. -/
theorem nearby_prime_family_bound (s : GreedySeq) (e K : ℕ)
    (Q : Finset ℕ) (he : 2 ∣ e)
    (hprime : ∀ i ∈ Q, (s.a i).Prime)
    (hnear : ∀ i ∈ Q, 2*s.a i < e ∧ e < 2*s.a i + 8*K + 8) :
    Q.card ≤ 48 * ((4*K+3)/210+1) + 4 := by
  classical
  let start := e/2 - (4*K+3)
  let R := (Finset.Ico start (start+(4*K+3))).filter Nat.Prime
  have hcard : Q.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn s.a
    · intro i hi
      have hp := hprime i hi
      have hn := hnear i hi
      obtain ⟨r, hr⟩ := he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ?_, hp⟩
      dsimp [start]
      omega
    · exact fun i _ j _ hij => s.injective hij
  have hs := prime_interval_sieve start (4*K+3)
  exact hcard.trans hs

end EKG
