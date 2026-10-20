import EKG.MissingComposites
import EKG.Clock
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-! Finite counting of missing composites by least prime factor. The
odd multiples of a fixed factor have spacing twice that factor. -/
namespace EKG
namespace HoleCounting

theorem odd_multiple_rank_injective {s x y : ℕ} (hs : 0 < s)
    (hx : s ∣ x) (hy : s ∣ y) (hxo : ¬ 2 ∣ x) (hyo : ¬ 2 ∣ y)
    (heq : x/(2*s) = y/(2*s)) : x = y := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  have hko : ¬ 2 ∣ k := by
    intro hd
    apply hxo
    rw [hk]
    exact dvd_mul_of_dvd_right hd s
  have hlo : ¬ 2 ∣ l := by
    intro hd
    apply hyo
    rw [hl]
    exact dvd_mul_of_dvd_right hd s
  have hkm : k%2 = 1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hko
    omega
  have hlm : l%2 = 1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hlo
    omega
  have hkd : (s*k)/(2*s) = k/2 := by
    rw [Nat.mul_comm 2 s, Nat.mul_div_mul_left _ _ hs]
  have hld : (s*l)/(2*s) = l/2 := by
    rw [Nat.mul_comm 2 s, Nat.mul_div_mul_left _ _ hs]
  rw [hk, hl, hkd, hld] at heq
  have hkl : k = l := by omega
  rw [hk, hl, hkl]

/-- A closed lower endpoint and open upper endpoint cost at most `M+1`
rungs, uniformly even when the lower endpoint would be negative. -/
theorem odd_multiple_window_card_le (S : Finset ℕ) {e s M : ℕ} (hs : 0 < s)
    (hS : ∀ x ∈ S, s ∣ x ∧ ¬ 2 ∣ x ∧ x < e ∧ e-x ≤ 2*s*M) :
    S.card ≤ M+1 := by
  classical
  let d := 2*s
  have hd : 0 < d := by dsimp [d]; omega
  let R := Finset.Icc (e/d-M) (e/d)
  have hc : S.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn (fun x => x/d)
    · intro x hx
      obtain ⟨_, _, hxe, hspan⟩ := hS x hx
      have hupper : x/d ≤ e/d := Nat.div_le_div_right hxe.le
      have hspan' : e ≤ x+d*M := by dsimp [d]; omega
      have hlo : e/d ≤ x/d+M := by
        have hdiv : e/d ≤ (x+d*M)/d := Nat.div_le_div_right hspan'
        simpa [Nat.add_mul_div_left _ _ hd] using hdiv
      exact Finset.mem_Icc.mpr ⟨Nat.sub_le_iff_le_add.mpr hlo, hupper⟩
    · intro x hx y hy heq
      have hx' := hS x hx
      have hy' := hS y hy
      exact odd_multiple_rank_injective hs hx'.1 hy'.1 hx'.2.1 hy'.2.1 heq
  have hR : R.card ≤ M+1 := by
    simp only [R, Nat.card_Icc]
    omega
  omega

/-- The manuscript's factor-grouping argument for any finite set of
odd composites satisfying its geometric hole bound. -/
theorem card_le_primeCounting_mul (S : Finset ℕ) {e M : ℕ}
    (hS : ∀ h ∈ S, 1 < h ∧ ¬ h.Prime ∧ ¬ 2 ∣ h ∧ h < e ∧
      e-h ≤ 2*h.minFac*M) :
    S.card ≤ Nat.primeCounting (Nat.sqrt e)*(M+1) := by
  classical
  let P := (Nat.sqrt e+1).primesBelow
  have hlabels : ∀ h ∈ S, h.minFac ∈ P := by
    intro h hh
    have hspec := hS h hh
    have hp := Nat.minFac_prime (by omega : h ≠ 1)
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < h) hspec.2.1
    have hroot : h.minFac ≤ Nat.sqrt e := Nat.le_sqrt'.mpr (by omega)
    exact Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
  have hfiber : ∀ s ∈ P, (S.filter (fun h => h.minFac = s)).card ≤ M+1 := by
    intro s hs
    have hp := (Nat.mem_primesBelow.mp hs).2
    apply odd_multiple_window_card_le _ hp.pos
    intro h hh
    obtain ⟨hmem, hfac⟩ := Finset.mem_filter.mp hh
    have hspec := hS h hmem
    refine ⟨by rw [← hfac]; exact Nat.minFac_dvd h,
      hspec.2.2.1, hspec.2.2.2.1, ?_⟩
    simpa [hfac] using hspec.2.2.2.2
  have hcard : S.card = ∑ s ∈ P, (S.filter (fun h => h.minFac = s)).card :=
    Finset.card_eq_sum_card_fiberwise hlabels
  have hsum : (∑ s ∈ P, (S.filter (fun h => h.minFac = s)).card) ≤
      P.card*(M+1) := by
    calc
      _ ≤ ∑ _s ∈ P, (M+1) := Finset.sum_le_sum hfiber
      _ = _ := by simp
  have hP : P.card = Nat.primeCounting (Nat.sqrt e) :=
    Nat.primesBelow_card_eq_primeCounting' _
  rw [hcard, ← hP]
  exact hsum

noncomputable def holesBelow (s : GreedySeq) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 (frontier s t)).filter
    (fun h => ¬ h.Prime ∧ ¬ UsedBefore s.a (t+1) h)

theorem holesBelow_spec (s : GreedySeq) {h t : ℕ} (hh : h ∈ holesBelow s t) :
    1 < h ∧ ¬ h.Prime ∧ ¬ 2 ∣ h ∧ h < frontier s t ∧
      ¬ UsedBefore s.a (t+1) h := by
  classical
  obtain ⟨hinterval, hnp, hfree⟩ := Finset.mem_filter.mp hh
  obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp hinterval
  have hne1 : h ≠ 1 := by
    intro he
    exact hfree ⟨0, by omega, s.seed_zero.trans he.symm⟩
  exact ⟨by omega, hnp, fun hd => hfree (smaller_even_used s (by omega) hd hu), hu, hfree⟩

theorem missing_composite_ge_fifteen (s : GreedySeq) {h t : ℕ}
    (ht : 8 ≤ t) (hh : 1 < h) (hnp : ¬ h.Prime)
    (hbelow : h < frontier s t) (hfree : ¬ UsedBefore s.a (t+1) h) : 15 ≤ h := by
  have hodd : ¬ 2 ∣ h := fun hd => hfree (smaller_even_used s (by omega) hd hbelow)
  by_contra hn
  have hsmall : h ≤ 14 := by omega
  have hchecked : ∀ k : Fin 15, 1 < k.val → ¬ k.val.Prime → ¬ 2 ∣ k.val → k.val = 9 := by
    decide
  have h9 : h = 9 := hchecked ⟨h, by omega⟩ hh hnp hodd
  subst h
  exact hfree ⟨5, by omega, FiniteBase.first_thirteen s (n := 5) (by omega)⟩

/-- Corollary clock (a), once the missing-composite geometric theorem
has been established. This lemma supplies all finite counting steps. -/
theorem holesBelow_card_of_geometric_bound (s : GreedySeq) {t : ℕ} (ht : 8 ≤ t)
    (hgeom : ∀ h, 15 ≤ h → ¬ h.Prime → h < frontier s t →
      ¬ UsedBefore s.a (t+1) h → frontier s t-h ≤
        2*h.minFac*(13*Nat.primeCounting (Nat.sqrt h)+724)) :
    (holesBelow s t).card ≤ Nat.primeCounting (Nat.sqrt (frontier s t))*
      (13*Nat.primeCounting (Nat.sqrt (frontier s t))+725) := by
  apply card_le_primeCounting_mul (M := 13*Nat.primeCounting (Nat.sqrt (frontier s t))+724)
  intro h hh
  have hspec := holesBelow_spec s hh
  refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, ?_⟩
  have h15 := missing_composite_ge_fifteen s ht hspec.1 hspec.2.1
    hspec.2.2.2.1 hspec.2.2.2.2
  have hs := hgeom h h15 hspec.2.1 hspec.2.2.2.1 hspec.2.2.2.2
  have hm := Nat.monotone_primeCounting (Nat.sqrt_le_sqrt hspec.2.2.2.1.le)
  exact hs.trans (Nat.mul_le_mul_left (2*h.minFac) (by omega))

end HoleCounting

theorem GreedySeq.missing_composites_card_bound (s : GreedySeq) {t : ℕ} (ht : 8 ≤ t) :
    (HoleCounting.holesBelow s t).card ≤ Nat.primeCounting (Nat.sqrt (frontier s t))*
      (13*Nat.primeCounting (Nat.sqrt (frontier s t))+725) :=
  HoleCounting.holesBelow_card_of_geometric_bound s ht
    (fun _ hh hnp hbelow hfree => s.missing_composite_bound hh hnp hbelow hfree)

theorem HoleCounting.holesBelow_eq_clock_holes (s : GreedySeq) (t : ℕ) :
    HoleCounting.holesBelow s t = Clock.holes s t := by
  classical
  ext h
  simp only [HoleCounting.holesBelow, Clock.holes, Clock.missingBelow,
    Finset.mem_filter, Finset.mem_sdiff, Clock.mem_usedValues]
  tauto

/-- Unconditional manuscript Corollary clock (a), in the clock agent's
existing hole-count definition. Zero-based `t ≥ 8` is manuscript `t ≥ 9`. -/
theorem Clock.holes_card_bound (s : GreedySeq) {t : ℕ} (ht : 8 ≤ t) :
    (Clock.holes s t).card ≤ Nat.primeCounting (Nat.sqrt (frontier s t))*
      (13*Nat.primeCounting (Nat.sqrt (frontier s t))+725) := by
  rw [← HoleCounting.holesBelow_eq_clock_holes]
  exact s.missing_composites_card_bound ht

theorem actualA_holes_card_bound {t : ℕ} (ht : 8 ≤ t) :
    (Clock.holes canonical t).card ≤ Nat.primeCounting (Nat.sqrt (frontier canonical t))*
      (13*Nat.primeCounting (Nat.sqrt (frontier canonical t))+725) :=
  Clock.holes_card_bound canonical ht

end EKG
