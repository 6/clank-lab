import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Donkin

/-- The exact pigeonhole bound used at every unused prime above n. -/
theorem big_prime_free_residue (n ell : ℕ) (hn : 2 ≤ n) (he : n < ell)
    (bad : Finset ℕ) (hb : bad.card ≤ n - 2) :
    ∃ r : ℕ, 0 < r ∧ r < ell ∧ r ∉ bad := by
  have hc : bad.card < (Finset.Ico 1 ell).card := by
    simp only [Nat.card_Ico]
    omega
  obtain ⟨r, hr, hbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨r, (Finset.mem_Ico.mp hr).1, (Finset.mem_Ico.mp hr).2, hbad⟩

/-- All affine factors can be made simultaneously nonzero if their number plus
    the excluded seed residue zero is less than the size of the finite field.
    No nonzero-coefficient hypothesis is hidden here. -/
theorem affine_avoidance {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (C : ι → K) (hcard : Fintype.card ι + 1 < Fintype.card K) :
    ∃ r : K, r ≠ 0 ∧ ∀ i, C i * r + 1 ≠ 0 := by
  classical
  let bad : Finset K := insert 0 (Finset.univ.image fun i => -(C i)⁻¹)
  have hb : bad.card ≤ Fintype.card ι + 1 := by
    dsimp [bad]
    exact (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (Finset.card_image_le) 1)
  have hc : bad.card < (Finset.univ : Finset K).card := by
    simpa using lt_of_le_of_lt hb hcard
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hr0 : r ≠ 0 := by
    intro h
    apply hr
    simp [bad, h]
  refine ⟨r, hr0, ?_⟩
  intro i hi
  have hCi : C i ≠ 0 := by
    intro hc
    simp [hc] at hi
  have heq : r = -(C i)⁻¹ := by
    apply (mul_left_cancel₀ hCi)
    calc
      C i * r = -1 := (eq_neg_iff_add_eq_zero).mpr hi
      _ = C i * -(C i)⁻¹ := by simp [hCi]
  apply hr
  simp only [bad, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, heq.symm⟩

/-- At a small odd prime B may explicitly use seed residue -1: every
    subsequent prefix coefficient is 2, so the affine value is -1. -/
theorem small_prime_residue {K : Type*} [Field K] [NeZero (2 : K)] :
    (-1 : K) ≠ 0 ∧ (2 : K) * (-1) + 1 ≠ 0 := by
  constructor <;> norm_num

/-- Divisibility by a prescribed prime and exclusion of every smaller prime
    are precisely what is needed for the least-factor rule. -/
theorem least_factor_from_local {N q : ℕ} (hN : N ≠ 1) (hq : q.Prime)
    (hd : q ∣ N) (hx : ∀ ell : ℕ, ell.Prime → ell < q → ¬ ell ∣ N) :
    N.minFac = q := by
  apply Nat.le_antisymm (Nat.minFac_le_of_dvd hq.two_le hd)
  by_contra h
  have hh : N.minFac < q := Nat.lt_of_not_ge h
  exact hx _ (Nat.minFac_prime hN) hh (Nat.minFac_dvd N)

#print axioms Donkin.big_prime_free_residue
#print axioms Donkin.affine_avoidance
#print axioms Donkin.small_prime_residue
#print axioms Donkin.least_factor_from_local
/-- Literal prefix coefficient after initial factor 2. -/
def coefficient {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℕ :=
  2 * ∏ j ∈ Finset.univ.filter (fun j : Fin m => j < i), q j

/-- B's exact uniform local compatibility. No CRT lift or prime seed assumed. -/
theorem uniform_local_compatibility {m : ℕ} (q : Fin m → ℕ)
    (hq : ∀ i, (q i).Prime) (hmono : StrictMono q)
    (hbig : ∀ i, m + 2 < q i)
    (hsmall : ∀ ell : ℕ, ell.Prime → ell ≤ m + 2 →
      ∀ i, (q i : ZMod ell) = 1)
    (ell : ℕ) (hell : ell.Prime) :
    ∃ r : ZMod ell, r ≠ 0 ∧
      (ell = 2 → r + 1 = 0) ∧
      ∀ i : Fin m,
        (ell = q i → (coefficient q i : ZMod ell) * r + 1 = 0) ∧
        (ell < q i → (coefficient q i : ZMod ell) * r + 1 ≠ 0) := by
  classical
  let : Fact ell.Prime := ⟨hell⟩
  by_cases hs : ell ≤ m + 2
  · have hc (i : Fin m) : (coefficient q i : ZMod ell) = 2 := by
      simp [coefficient, hsmall ell hell hs]
    by_cases he2 : ell = 2
    · subst ell
      refine ⟨1, one_ne_zero, ?_, ?_⟩
      · intro _
        rfl
      · intro i
        constructor
        · intro he
          have := hbig i
          omega
        · intro _
          rw [hc]
          exact of_decide_eq_true rfl
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_, ?_⟩
      · exact fun he => (he2 he).elim
      · intro i
        constructor
        · intro he
          have := hbig i
          omega
        · intro _
          rw [hc]
          norm_num
  · have hlarge : m + 2 < ell := Nat.lt_of_not_ge hs
    by_cases hsel : ∃ k, ell = q k
    · obtain ⟨k, hk⟩ := hsel
      have hc0 : (coefficient q k : ZMod ell) ≠ 0 := by
        rw [coefficient, Nat.cast_mul, Nat.cast_prod]
        apply mul_ne_zero
        · rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hd
          have := Nat.le_of_dvd (by decide : 0 < 2) hd
          omega
        · apply Finset.prod_ne_zero_iff.mpr
          intro j hj
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hd
          have heq : ell = q j := ((hq j).eq_one_or_self_of_dvd ell hd).resolve_left hell.ne_one
          have hjk : j < k := (Finset.mem_filter.mp hj).2
          have := hmono hjk
          omega
      refine ⟨-(coefficient q k : ZMod ell)⁻¹, neg_ne_zero.mpr (inv_ne_zero hc0), ?_, ?_⟩
      · intro he
        omega
      · intro i
        constructor
        · intro hi
          have hik : i = k := hmono.injective (hi.symm.trans hk)
          subst i
          simp [hc0]
        · intro hi
          have hki : k < i := (hmono.lt_iff_lt).mp (by omega)
          have hc : (coefficient q i : ZMod ell) = 0 := by
            rw [coefficient, Nat.cast_mul, Nat.cast_prod]
            suffices (∏ j ∈ Finset.univ.filter (fun j : Fin m => j < i), (q j : ZMod ell)) = 0 by
              rw [this, mul_zero]
            apply Finset.prod_eq_zero (i := k)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki⟩)
            exact (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [hk])
          simp [hc]
    · obtain ⟨r, hr0, hr⟩ := affine_avoidance
        (fun i : Fin m => (coefficient q i : ZMod ell)) (by
          rw [Fintype.card_fin, ZMod.card]
          omega)
      refine ⟨r, hr0, ?_, ?_⟩
      · intro he
        omega
      · intro i
        exact ⟨fun he => (hsel ⟨i, he⟩).elim, fun _ => hr i⟩

#print axioms Donkin.uniform_local_compatibility

end Donkin
