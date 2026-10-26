import Endpoint
import HardStep
import Dependencies

namespace Donkin

private def tailProd {m : ℕ} (q : Fin m → ℕ) (k : ℕ) : ℕ :=
  2 * ∏ j ∈ Finset.univ.filter (fun j : Fin m => j.val < k), q j

private theorem tailProd_zero {m : ℕ} (q : Fin m → ℕ) : tailProd q 0 = 2 := by
  simp [tailProd]

private theorem tailProd_coefficient {m : ℕ} (q : Fin m → ℕ) (i : Fin m) :
    tailProd q i.val = coefficient q i := by
  rfl

private theorem tailProd_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, (q i).Prime) (k : ℕ) :
    0 < tailProd q k := by
  unfold tailProd
  exact Nat.mul_pos (by decide) (Finset.prod_pos (fun i _ => (hq i).pos))

private theorem tailProd_succ {m : ℕ} (q : Fin m → ℕ) (k : ℕ) (hk : k < m) :
    tailProd q (k+1) = tailProd q k * q ⟨k,hk⟩ := by
  have hs : Finset.univ.filter (fun j : Fin m => j.val < k+1) =
      insert ⟨k,hk⟩ (Finset.univ.filter (fun j : Fin m => j.val < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  have hn : (⟨k,hk⟩ : Fin m) ∉ Finset.univ.filter (fun j : Fin m => j.val < k) := by
    simp
  simp only [tailProd, hs, Finset.prod_insert hn]
  ring

/-- The frozen arbitrary-tail interface: no conclusion assumptions. -/
theorem finite_lift {m : ℕ} (q : Fin m → ℕ)
    (hq : ∀ i, (q i).Prime) (hmono : StrictMono q)
    (hbig : ∀ i, m + 2 < q i)
    (hsmall : ∀ ell : ℕ, ell.Prime → ell ≤ m + 2 →
      ∀ i, (q i : ZMod ell) = 1) :
    ∃ p : ℕ, 3 < p ∧ p.Prime ∧ term p 1 = 2 ∧
      ∀ i : Fin m, term p (i.val + 2) = q i := by
  classical
  let B := max 3 (Finset.univ.sup q)
  let t := (Finset.range (B+1)).filter Nat.Prime
  let r (ell : ℕ) (h : ell.Prime) := Classical.choose
    (uniform_local_compatibility q hq hmono hbig hsmall ell h)
  have hr (ell : ℕ) (h : ell.Prime) := Classical.choose_spec
    (uniform_local_compatibility q hq hmono hbig hsmall ell h)
  let a : ℕ → ℕ := fun ell => if h : ell.Prime then (r ell h).val else 0
  have hac (ell : ℕ) (h : ell.Prime) : (a ell : ZMod ell) = r ell h := by
    letI : NeZero ell := ⟨h.ne_zero⟩
    simp only [a, dif_pos h]
    exact ZMod.natCast_zmod_val _
  have ht : ∀ ell ∈ t, ell.Prime := fun ell hel => (Finset.mem_filter.mp hel).2
  have ha : ∀ ell ∈ t, ¬ ell ∣ a ell := by
    intro ell hel hd
    have hz : (a ell : ZMod ell) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [hac ell (ht ell hel)] at hz
    exact (hr ell (ht ell hel)).1 hz
  obtain ⟨p, hp3, hpp, hp⟩ := prime_seed_lift t a ht ha 3
  have hcast (ell : ℕ) (hell : ell.Prime) (hle : ell ≤ B) :
      (p : ZMod ell) = r ell hell := by
    have hel : ell ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hell⟩
    exact ((ZMod.natCast_eq_natCast_iff p (a ell) ell).mpr (hp ell hel)).trans (hac ell hell)
  have hqB (i : Fin m) : q i ≤ B := by
    exact le_trans (Finset.le_sup (f := q) (Finset.mem_univ i)) (le_max_right _ _)
  have hp2 : (p+1).minFac = 2 := by
    apply least_factor_from_local (by omega) Nat.prime_two
    · have hodd := hpp.odd_of_ne_two (by omega)
      exact (hodd.add_odd (by decide : Odd 1)).two_dvd
    · intro ell hell hlt hd
      have := hell.two_le
      omega
  have hterm1 : term p 1 = 2 := hp2
  have hstep (i : Fin m) : (p * coefficient q i + 1).minFac = q i := by
    have hpos := tailProd_pos q hq i.val
    rw [tailProd_coefficient] at hpos
    apply least_factor_from_local (by nlinarith) (hq i)
    · apply (ZMod.natCast_eq_zero_iff _ _).mp
      push_cast
      rw [hcast (q i) (hq i) (hqB i)]
      have hz := ((hr (q i) (hq i)).2.2 i).1 rfl
      change (coefficient q i : ZMod (q i)) * r (q i) (hq i) + 1 = 0 at hz
      rw [mul_comm]
      exact hz
    · intro ell hell hlt hd
      have hle : ell ≤ B := le_trans (Nat.le_of_lt hlt) (hqB i)
      have hz : ((p * coefficient q i + 1 : ℕ) : ZMod ell) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hd
      push_cast at hz
      rw [hcast ell hell hle] at hz
      have hn := ((hr ell hell).2.2 i).2 hlt
      change (coefficient q i : ZMod ell) * r ell hell + 1 ≠ 0 at hn
      apply hn
      rwa [mul_comm] at hz
  have hstate : ∀ k : ℕ, k ≤ m → productState p (k+1) = p * tailProd q k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [productState, hp2, tailProd_zero]
    | succ k ih =>
      intro hk
      have hkm : k < m := by omega
      have ih' := ih (by omega)
      have hsi : (productState p (k+1) + 1).minFac = q ⟨k,hkm⟩ := by
        rw [ih', tailProd_coefficient q ⟨k,hkm⟩]
        exact hstep ⟨k,hkm⟩
      rw [show k+1+1 = (k+1)+1 by omega, productState, hsi, ih',
        tailProd_succ q k hkm]
      ring
  refine ⟨p,hp3,hpp,hterm1,?_⟩
  intro i
  change (productState p (i.val+1) + 1).minFac = q i
  rw [hstate i.val (Nat.le_of_lt i.isLt), tailProd_coefficient]
  exact hstep i

#print axioms Donkin.finite_lift
end Donkin
