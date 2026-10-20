import EKG.VerifiedSpans
import EKG.SmoothedPositions
import EKG.PartAArithmetic

/-! The finite many-predecessor mechanism, specialized to canonical EKG.
Every numerical premise below will be discharged by the final eventual
argument. No injection, sparsity or new sequence property is assumed. -/
namespace EKG
namespace PartA

/-- An actual top excursion with gap greater than `6k` has a composite
non-tick predecessor, whose least prime factor controls the excursion. -/
theorem controlling_prime {t : ℕ}
    (he : 9 ≤ frontier canonical t)
    (hgap : 6 * (earlyEvenCount canonical t + 1) <
      nonTickTop canonical t - frontier canonical t) :
    ∃ i r : ℕ, i ≤ t ∧ 2 ≤ i ∧
      nonTickTop canonical t = canonical.a i ∧ r.Prime ∧
      r ∣ canonical.a (i-1) ∧ r^2 ≤ nonTickTop canonical t ∧
      nonTickTop canonical t ≤ frontier canonical t +
        2*r*(earlyEvenCount canonical t+1) := by
  obtain ⟨i, hit, hnot, hval⟩ := nonTickTop_attained canonical t
  have hlarge : frontier canonical t < canonical.a i := by omega
  have hi : 2 ≤ i := by
    by_contra h
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with hc | hc
    · rw [hc, canonical.seed_zero] at hlarge
      omega
    · rw [hc, canonical.seed_one] at hlarge
      omega
  have hprev : i-1+1 = i := by omega
  have hprevobs : i-1 ≤ t := by omega
  have hodd : ¬ 2 ∣ canonical.a (i-1) := by
    intro htwo
    have hsmall := next_after_even_le_frontier canonical htwo
    rw [hprev] at hsmall
    have hmono := frontier_monotone canonical hprevobs
    omega
  have hneone : canonical.a (i-1) ≠ 1 := by
    intro hone
    have hindex : i-1 = 0 := canonical.injective
      (hone.trans canonical.seed_zero.symm)
    omega
  have hcomp : ¬ (canonical.a (i-1)).Prime := by
    intro hp
    have hp2 : canonical.a (i-1) ≠ 2 := by
      intro htwo
      apply hodd
      rw [htwo]
    have hb := prime_occurrence_block canonical hp hp2 rfl
    have htick : spanTickValue (canonical.a i) := by
      refine ⟨canonical.a (i-1), hp, hp2, ?_⟩
      simpa only [hprev] using hb.2.2.1
    exact hnot htick
  have hprevnot : ¬ spanTickValue (canonical.a (i-1)) := by
    rintro ⟨p, _, _, heq⟩
    have hthree : 3 ∣ canonical.a (i-1) := by
      rw [heq]
      exact Nat.dvd_mul_right 3 p
    have hb := canonical.term_span_le_six hi (by omega : i ≤ t+1) hthree
    omega
  have hbound := nonTick_le_top canonical hprevobs hprevnot
  have hrsq := (Nat.minFac_sq_le_self (canonical.positive (i-1)) hcomp).trans hbound
  have hspan := canonical.term_le_frontier_add hi (by omega : i ≤ t+1)
    (Nat.minFac_prime hneone) (Nat.minFac_dvd _)
  refine ⟨i, (canonical.a (i-1)).minFac, hit, hi, hval,
    Nat.minFac_prime hneone, Nat.minFac_dvd _, hrsq, ?_⟩
  omega

/-- The current observation count controls every prime factor of every
historical predecessor; the occurrence need not be close to `t`. -/
theorem predecessor_rough {n t : ℕ} {B : ℝ}
    (hn : 2 ≤ n) (hnt : n ≤ t+1)
    (hgap : 2 * B * (earlyEvenCount canonical t+1 : ℕ) <
      (canonical.a n : ℝ) - (frontier canonical t : ℝ)) :
    ∀ p : ℕ, p.Prime → p ∣ canonical.a (n-1) → B < (p : ℝ) := by
  intro p hp hpd
  have hbound := canonical.term_le_frontier_add hn hnt hp hpd
  have hreal : (canonical.a n : ℝ) ≤ (frontier canonical t : ℝ) +
      2 * (p : ℝ) * (earlyEvenCount canonical t+1 : ℕ) := by
    exact_mod_cast hbound
  have hk : (0 : ℝ) ≤ (earlyEvenCount canonical t+1 : ℕ) := by positivity
  by_contra h
  have hpB : (p : ℝ) ≤ B := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_right hpB hk
  linarith

/-- Full predecessor type exclusions for a large even witness, deduced
from roughness and the actual prime-block theorem. -/
theorem even_witness_predecessor {n t : ℕ} {B : ℝ}
    (hn : 2 ≤ n) (hnt : n ≤ t) (hy : 2 ∣ canonical.a n)
    (hB : 3 < B)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ canonical.a (n-1) → B < (p : ℝ)) :
    ¬ (canonical.a (n-1)).Prime ∧
      ¬ spanTickValue (canonical.a (n-1)) ∧
      canonical.a (n-1) ≤ nonTickTop canonical t ∧
      smoothValue (canonical.a (n-1)) = canonical.a (n-1) := by
  have htwo : ¬ 2 ∣ canonical.a (n-1) := by
    intro hd
    have := hrough 2 Nat.prime_two hd
    norm_num at this
    linarith
  have hthree : ¬ 3 ∣ canonical.a (n-1) := by
    intro hd
    have := hrough 3 Nat.prime_three hd
    norm_num at this
    linarith
  have hnot : ¬ spanTickValue (canonical.a (n-1)) := by
    rintro ⟨p, _, _, heq⟩
    apply hthree
    rw [heq]
    exact Nat.dvd_mul_right 3 p
  have hcomp : ¬ (canonical.a (n-1)).Prime := by
    intro hp
    have hp2 : canonical.a (n-1) ≠ 2 := by
      intro heq
      apply htwo
      rw [heq]
    have hb := prime_occurrence_block canonical hp hp2 rfl
    have hprev : n-1+1 = n := by omega
    apply even_not_tick hy
    refine ⟨canonical.a (n-1), hp, hp2, ?_⟩
    simpa only [hprev] using hb.2.2.1
  have hsix : canonical.a (n-1) ≠ 6 := by
    intro heq
    apply htwo
    rw [heq]
    norm_num
  exact ⟨hcomp, hnot, nonTick_le_top canonical (by omega) hnot,
    smoothValue_of_ordinary hcomp hnot hsix⟩

/-- Rungs in the upper half of the actual excursion. Both endpoints are
strict; integer midpoint division is exact for these integer witnesses. -/
noncomputable def rungs (t r M : ℕ) : Finset ℕ :=
  progressionIndices ((frontier canonical t + nonTickTop canonical t)/2)
    (nonTickTop canonical t) (2*r*M)

/-- Literal count of all and only the selected strict-interval rungs. -/
theorem rungs_card_exact (t r M : ℕ) :
    (rungs t r M).card =
      ((nonTickTop canonical t-1)/(2*r*M)+1) -
        (((frontier canonical t+nonTickTop canonical t)/2)/(2*r*M)+1) := by
  simp only [rungs, progressionIndices, Nat.card_Ico]

/-- Exact finite count-to-gap inequality (loss of one rung). -/
theorem rungs_count {t r M : ℕ} (hr : 0 < r) (hM : 0 < M)
    :
    ((nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ)) ≤
      4 * (r : ℝ) * M * ((rungs t r M).card + 1 : ℕ) := by
  have hd : 0 < 2*r*M := by positivity
  have hc := progression_span_le (e := (frontier canonical t + nonTickTop canonical t)/2)
    (v := nonTickTop canonical t) hd (le_refl (rungs t r M).card)
  have hmid : 2 * ((frontier canonical t + nonTickTop canonical t)/2) ≤
      frontier canonical t + nonTickTop canonical t := by omega
  have hreal : (nonTickTop canonical t : ℝ) ≤
      (((frontier canonical t + nonTickTop canonical t)/2 : ℕ) : ℝ) +
        (2 : ℝ)*r*M*((rungs t r M).card+1 : ℕ) := by exact_mod_cast hc
  have hmidreal : 2 * (((frontier canonical t + nonTickTop canonical t)/2 : ℕ) : ℝ) ≤
      (frontier canonical t : ℝ) + nonTickTop canonical t := by exact_mod_cast hmid
  linarith

/-- Data of one actual witness, with every new structural conclusion proved. -/
structure RungWitness (t i r M : ℕ) (B : ℝ) (j n q : ℕ) : Prop where
  index_ge : 2 ≤ n
  index_lt : n < i
  value_eq : canonical.a n = 2*r*M*j
  predecessor_eq : canonical.a (n-1) = r*q
  cofactor_prime : q.Prime
  cofactor_large : B < (q : ℝ)
  predecessor_notprime : ¬ (canonical.a (n-1)).Prime
  predecessor_nottick : ¬ spanTickValue (canonical.a (n-1))
  predecessor_le : canonical.a (n-1) ≤ nonTickTop canonical t
  smooth_value : smoothValue (canonical.a n) = canonical.a n
  smooth_predecessor : smoothValue (canonical.a (n-1)) = canonical.a (n-1)

/-- Every selected upper-half rung has an actual predecessor `r*q` with
prime cofactor, and the entire cofactor map is injective. Numerical scale
premises are explicit and will be discharged before the final endpoint. -/
theorem many_predecessor_injection {t i r M : ℕ} {B : ℝ}
    (he : 9 ≤ frontier canonical t)
    (hlarge : frontier canonical t < nonTickTop canonical t)
    (hi : 2 ≤ i) (hit : i ≤ t)
    (hval : nonTickTop canonical t = canonical.a i)
    (hr : r.Prime) (hri : r ∣ canonical.a (i-1))
    (hM : 2 ≤ M) (hB : 3 < B) (hMB : (M : ℝ) < B)
    (hscale : 4*B*(earlyEvenCount canonical t+1 : ℕ) ≤
      (nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ))
    (hstride : (nonTickTop canonical t : ℝ) ≤ (2*r*M : ℕ)*B)
    (hcube : (nonTickTop canonical t : ℝ) < B^3) :
    ∃ index cofactor : ℕ → ℕ,
      (∀ j ∈ rungs t r M, RungWitness t i r M B j (index j) (cofactor j)) ∧
      Set.InjOn cofactor (rungs t r M : Set ℕ) := by
  classical
  have hd : 0 < 2*r*M := by have := hr.pos; positivity
  have hocc : ∀ j : ℕ, ∃ n : ℕ, j ∈ rungs t r M →
      2 ≤ n ∧ n < i ∧ canonical.a n = 2*r*M*j := by
    intro j
    by_cases hj : j ∈ rungs t r M
    · obtain ⟨hylo, hyhi⟩ := progressionIndices_bounds hd hj
      have hymid : frontier canonical t + nonTickTop canonical t < 2*(2*r*M*j) := by
        omega
      have hyp : 0 < 2*r*M*j := by omega
      have hrdiv : r ∣ 2*r*M*j :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_mul_left r 2) M) j
      have hyi : 2*r*M*j < canonical.a i := by omega
      obtain ⟨n, hni, hnval⟩ := smaller_multiple_used canonical hi hr hri hyp hrdiv hyi
      have hn : 2 ≤ n := by
        by_contra h
        have hcases : n = 0 ∨ n = 1 := by omega
        rcases hcases with hz | ho
        · rw [hz, canonical.seed_zero] at hnval
          omega
        · rw [ho, canonical.seed_one] at hnval
          omega
      exact ⟨n, fun _ => ⟨hn, hni, hnval⟩⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  let index : ℕ → ℕ := fun j => Classical.choose (hocc j)
  have hindex : ∀ j, j ∈ rungs t r M →
      2 ≤ index j ∧ index j < i ∧ canonical.a (index j) = 2*r*M*j :=
    fun j => Classical.choose_spec (hocc j)
  let cofactor : ℕ → ℕ := fun j => canonical.a (index j-1)/r
  have hw : ∀ j ∈ rungs t r M,
      RungWitness t i r M B j (index j) (cofactor j) := by
    intro j hj
    obtain ⟨hn, hni, hyn⟩ := hindex j hj
    obtain ⟨hylo, hyhi⟩ := progressionIndices_bounds hd hj
    have hjpos : 0 < j := by
      by_contra h
      have hz : j = 0 := by omega
      rw [hz, Nat.mul_zero] at hylo
      omega
    have hymid : frontier canonical t + nonTickTop canonical t < 2*(2*r*M*j) := by
      omega
    have hymidreal : (frontier canonical t : ℝ) + nonTickTop canonical t <
        2 * ((2*r*M*j : ℕ) : ℝ) := by exact_mod_cast hymid
    have hrough : ∀ p : ℕ, p.Prime → p ∣ canonical.a (index j-1) → B < (p : ℝ) := by
      apply predecessor_rough hn (by omega : index j ≤ t+1)
      rw [hyn]
      linarith
    have heven : 2 ∣ canonical.a (index j) := by
      rw [hyn]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_mul_right 2 r) M) j
    obtain ⟨hcomp, hnot, hbound, hsmooth⟩ :=
      even_witness_predecessor hn (by omega : index j ≤ t) heven hB hrough
    have hjreal : (2*r*M : ℕ)*(j : ℝ) < (nonTickTop canonical t : ℝ) := by
      exact_mod_cast hyhi
    have hdreal : (0 : ℝ) < (2*r*M : ℕ) := by exact_mod_cast hd
    have hjB : (j : ℝ) < B := by nlinarith
    have hshared := canonical.eligible (index j) hn
    rw [hyn] at hshared
    have hrd : r ∣ canonical.a (index j-1) :=
      partA_factor_forcing hr hshared hrough hB hM hjpos hMB hjB
    have hprime : (cofactor j).Prime := by
      apply partA_prime_cofactor (canonical.positive (index j-1)) hcomp hr hrd hrough
        (by linarith : 0 < B)
      have hb : (canonical.a (index j-1) : ℝ) ≤ nonTickTop canonical t := by
        exact_mod_cast hbound
      exact hb.trans_lt hcube
    have hpred : canonical.a (index j-1) = r*cofactor j :=
      (Nat.mul_div_cancel' hrd).symm
    have hqd : cofactor j ∣ canonical.a (index j-1) := by
      rw [hpred]
      exact Nat.dvd_mul_left (cofactor j) r
    have hybig : 6 < canonical.a (index j) := by omega
    have hynotprime : ¬ (canonical.a (index j)).Prime :=
      Nat.not_prime_of_dvd_of_lt heven (by omega : 2 ≤ 2) (by omega : 2 < canonical.a (index j))
    exact ⟨hn, hni, hyn, hpred, hprime, hrough _ hprime hqd,
      hcomp, hnot, hbound,
      smoothValue_of_ordinary hynotprime (even_not_tick heven) (by omega), hsmooth⟩
  refine ⟨index, cofactor, hw, ?_⟩
  intro j hj k hk heq
  have wj := hw j hj
  have wk := hw k hk
  have hpred : canonical.a (index j-1) = canonical.a (index k-1) := by
    rw [wj.predecessor_eq, wk.predecessor_eq, heq]
  have hidx : index j = index k := by
    have := canonical.injective hpred
    have := wj.index_ge
    have := wk.index_ge
    omega
  have hvalues : 2*r*M*j = 2*r*M*k := by
    rw [← wj.value_eq, ← wk.value_eq, hidx]
  exact Nat.eq_of_mul_eq_mul_left hd hvalues

end PartA
end EKG
