import EKG.MissingComposites
import EKG.HoleCounting
import EKG.SmoothedPositions
import EKG.PartAArithmetic

/-! The actual finite successor injection for canonical EKG. Both interval
endpoints are strict. Only the occurrence at the current final index is
removed, with exact cardinal splitting and loss at most one. -/
namespace EKG.PartB

noncomputable def rungs (t h s M : ℕ) : Finset ℕ :=
  progressionIndices ((h + frontier canonical t)/2) (frontier canonical t) (2*s*M)

noncomputable def successorRungs (t h s M : ℕ) : Finset ℕ := by
  classical
  exact (rungs t h s M).filter (fun j => 2*s*M*j ≠ canonical.a t)

noncomputable def discardedRungs (t h s M : ℕ) : Finset ℕ := by
  classical
  exact (rungs t h s M).filter (fun j => 2*s*M*j = canonical.a t)

theorem rungs_card_exact (t h s M : ℕ) :
    (rungs t h s M).card =
      ((frontier canonical t-1)/(2*s*M)+1) -
        (((h+frontier canonical t)/2)/(2*s*M)+1) := by
  simp only [rungs, progressionIndices, Nat.card_Ico]

theorem rungs_card_split (t h s M : ℕ) :
    (successorRungs t h s M).card + (discardedRungs t h s M).card =
      (rungs t h s M).card := by
  classical
  simpa only [successorRungs, discardedRungs, not_not] using
    (Finset.card_filter_add_card_filter_not (s := rungs t h s M)
      (fun j => 2*s*M*j ≠ canonical.a t))

theorem discarded_card_le_one {t h s M : ℕ} (hs : 0 < s) (hM : 0 < M) :
    (discardedRungs t h s M).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjval := (Finset.mem_filter.mp hj).2
  have hkval := (Finset.mem_filter.mp hk).2
  have hd : 0 < 2*s*M := by positivity
  exact Nat.eq_of_mul_eq_mul_left hd (hjval.trans hkval.symm)

/-- Exact lattice count followed by precisely one possible discard costs
at most two rungs in the displacement bound (stronger than loss three). -/
theorem successor_rungs_count {t h s M : ℕ} (hs : 0 < s) (hM : 0 < M) :
    (frontier canonical t : ℝ) - (h : ℝ) ≤
      4 * (s : ℝ) * M * ((successorRungs t h s M).card + 2 : ℕ) := by
  have hd : 0 < 2*s*M := by positivity
  have hc := progression_span_le (e := (h+frontier canonical t)/2)
    (v := frontier canonical t) hd (le_refl (rungs t h s M).card)
  have hmid : 2*((h+frontier canonical t)/2) ≤ h+frontier canonical t := by omega
  have hreal : (frontier canonical t : ℝ) ≤
      (((h+frontier canonical t)/2 : ℕ) : ℝ) +
        (2 : ℝ)*s*M*((rungs t h s M).card+1 : ℕ) := by exact_mod_cast hc
  have hmidreal : 2*(((h+frontier canonical t)/2 : ℕ) : ℝ) ≤
      (h : ℝ)+frontier canonical t := by exact_mod_cast hmid
  have hcard : (rungs t h s M).card ≤ (successorRungs t h s M).card+1 := by
    have := rungs_card_split t h s M
    have := discarded_card_le_one (t:=t) (h:=h) hs hM
    omega
  have hcardreal : ((rungs t h s M).card+1 : ℕ) ≤
      ((successorRungs t h s M).card+2 : ℕ) := by omega
  have hcast : (((rungs t h s M).card+1 : ℕ) : ℝ) ≤
      (((successorRungs t h s M).card+2 : ℕ) : ℝ) := by exact_mod_cast hcardreal
  have hm := mul_le_mul_of_nonneg_left hcast (show (0:ℝ) ≤ 4*s*M by positivity)
  linarith

structure SuccessorWitness (t h s M j i : ℕ) : Prop where
  index_ge : 2 ≤ i
  index_lt : i < t
  value_eq : canonical.a i = 2*s*M*j
  successor_lt : canonical.a (i+1) < h

/-- Every surviving rung has an actual earlier occurrence and a successor
strictly below the still-missing original hole. Successors have multiplicity
one by injectivity of the literal constructed sequence. -/
theorem many_successors {t h s M : ℕ}
    (hh : 2 ≤ h) (hbelow : h < frontier canonical t)
    (hfree : ¬ UsedBefore canonical.a (t+1) h)
    (hs : s.Prime) (hsh : s ∣ h) (hM : 2 ≤ M) :
    ∃ index : ℕ → ℕ,
      (∀ j ∈ successorRungs t h s M, SuccessorWitness t h s M j (index j)) ∧
      Set.InjOn (fun j => canonical.a (index j+1))
        (successorRungs t h s M : Set ℕ) := by
  classical
  have hd : 0 < 2*s*M := by have := hs.pos; positivity
  have hex : ∀ j : ℕ, ∃ i : ℕ, j ∈ successorRungs t h s M →
      SuccessorWitness t h s M j i := by
    intro j
    by_cases hj : j ∈ successorRungs t h s M
    · obtain ⟨hjr,hjlast⟩ := Finset.mem_filter.mp hj
      obtain ⟨hylo,hyhi⟩ := progressionIndices_bounds hd hjr
      have hyh : h < 2*s*M*j := by omega
      have hypos : 0 < 2*s*M*j := by omega
      have heven : 2 ∣ 2*s*M*j :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_mul_right 2 s) M) j
      obtain ⟨i,hi,hval⟩ := smaller_even_used canonical hypos heven hyhi
      have hit : i < t := by
        have hil : i ≤ t := by omega
        have hne : i ≠ t := by intro heq; subst i; exact hjlast hval.symm
        omega
      have hi2 : 2 ≤ i := by
        by_contra hn
        have hc : i=0 ∨ i=1 := by omega
        rcases hc with hc | hc
        · rw [hc,canonical.seed_zero] at hval
          omega
        · rw [hc,canonical.seed_one] at hval
          omega
      have hsi : s ∣ canonical.a i := by
        rw [hval]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_mul_left s 2) M) j
      exact ⟨i,fun _ => ⟨hi2,hit,hval,
        MissingComposites.successor_lt_missing canonical hit (by omega) hfree hs hsi hsh⟩⟩
    · exact ⟨0,fun h => (hj h).elim⟩
  let index : ℕ → ℕ := fun j => Classical.choose (hex j)
  have hw : ∀ j ∈ successorRungs t h s M, SuccessorWitness t h s M j (index j) :=
    fun j => Classical.choose_spec (hex j)
  refine ⟨index,hw,?_⟩
  intro j hj k hk heq
  have hij : index j = index k := by
    have := canonical.injective heq
    omega
  have hval : (2*s*M)*j = (2*s*M)*k := by
    rw [← (hw j hj).value_eq, ← (hw k hk).value_eq,hij]
  exact Nat.eq_of_mul_eq_mul_left hd hval

/-- All structural successor exclusions, at its POST-occurrence frontier. -/
theorem successor_ordinary {s M j i : ℕ}
    (hi : 2 ≤ i) (hs : s.Prime) (hM : 2 ≤ M) (hj : 0 < j)
    (hy : canonical.a i = 2*s*M*j)
    (hbelow : canonical.a (i+1) < frontier canonical i) :
    ¬ (canonical.a (i+1)).Prime ∧
      ¬ spanTickValue (canonical.a (i+1)) ∧
      smoothValue (canonical.a (i+1)) = canonical.a (i+1) := by
  have hfree : ¬ UsedBefore canonical.a (i+1) (canonical.a (i+1)) := term_unused canonical (i+1)
  have hodd : ¬ 2 ∣ canonical.a (i+1) := by
    intro heven
    exact hfree (smaller_even_used canonical (canonical.positive _) heven hbelow)
  have heven : 2 ∣ canonical.a i := by
    rw [hy]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_mul_right 2 s) M) j
  have hcomp : ¬ (canonical.a (i+1)).Prime := by
    intro hp
    have hp2 : canonical.a (i+1) ≠ 2 := by intro heq; apply hodd; rw [heq]
    have hb := prime_occurrence_block canonical hp hp2 rfl
    have htwice : canonical.a i = 2*canonical.a (i+1) := by simpa using hb.2.1
    have heq : canonical.a (i+1) = s*(M*j) := by nlinarith [hy]
    have hMj : 2 ≤ M*j := by nlinarith
    have hsdiv : s ∣ canonical.a (i+1) := by rw [heq]; exact Nat.dvd_mul_right s _
    have hslt : s < canonical.a (i+1) := by rw [heq]; nlinarith [hs.pos]
    exact (Nat.not_prime_of_dvd_of_lt hsdiv hs.two_le hslt) hp
  have hnottick : ¬ spanTickValue (canonical.a (i+1)) := by
    rintro ⟨p,hp,hp2,hval⟩
    obtain ⟨n,hn,hindex,hprev⟩ := odd_prime_tick_unique canonical hp hp2 hval
    have heq : canonical.a i = p := by simpa using hprev
    exact primeStructure_odd_not_two_dvd hp hp2 (by rwa [←heq])
  exact ⟨hcomp,hnottick,smoothValue_of_ordinary hcomp hnottick
    (by intro heq; apply hodd; rw [heq]; norm_num)⟩

end EKG.PartB
