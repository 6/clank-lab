/-
Algebraic endpoint only for the extension in the paper. No surface, filling, intersection,
or pseudo-Anosov theorem is asserted. All Artin data are imported unchanged.
-/
import Multitwist
import Mathlib.Algebra.Group.Commute.Basic

namespace Multitwist.V2

/-- Integer normal form; the only additional hypothesis is commutation. -/
theorem integer_identity {G : Type*} [Group G] (A C D : G)
    (h : Commute A C) (k n : ℤ) :
    (A * C) ^ n * (A ^ (-1 : ℤ) * C ^ (-(k+1)) * D) =
      A ^ (n-1) * C ^ (n-k-1) * D := by
  rw [h.mul_zpow]
  have hc := (h.zpow_zpow (-1) n).symm
  calc
    (A ^ n * C ^ n) * (A ^ (-1 : ℤ) * C ^ (-(k+1)) * D) =
        (A ^ n * A ^ (-1 : ℤ)) * (C ^ n * C ^ (-(k+1))) * D := by
      simp only [mul_assoc]
      rw [hc.left_comm]
    _ = A ^ (n-1) * C ^ (n-k-1) * D := by
      rw [← zpow_add, ← zpow_add]
      have e1 : n + -1 = n - 1 := by omega
      have e2 : n + -(k+1) = n-k-1 := by omega
      rw [e1, e2]

/-- The exact natural-number parameterization in the frozen endpoint. -/
def g (k : ℕ) : Monoid.End F := Tai * Tci ^ (k+1) * Td

def t : Monoid.End F := Ta * Tc

/-- Powers cancel from a proved one-sided inverse relation. -/
theorem cancel_powers {M : Type*} [Monoid M] {a b : M} (h : a*b = 1)
    (n : ℕ) : a^n * b^n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc a b, h, one_mul,
      ih]

/-- One step removes Ta and one inverse Tc. -/
theorem first_member (k : ℕ) : t * g k = Tci ^ k * Td := by
  unfold t g
  rw [pow_succ']
  calc
    (Ta * Tc) * (Tai * (Tci * Tci ^ k) * Td) =
        ((Ta * Tc) * (Tai * Tci)) * (Tci ^ k * Td) := by
      simp only [mul_assoc]
    _ = Tci ^ k * Td := by rw [t_pos_inv, one_mul]

/-- The second exceptional member, as an equality of endomorphisms. -/
theorem second_member (k : ℕ) : t ^ (k+1) * g k = Ta ^ k * Td := by
  rw [pow_succ, mul_assoc, first_member]
  unfold t
  have hc : Commute Ta Tc := F2
  rw [hc.mul_pow]
  calc
    (Ta ^ k * Tc ^ k) * (Tci ^ k * Td) =
        Ta ^ k * ((Tc ^ k * Tci ^ k) * Td) := by simp only [mul_assoc]
    _ = Ta ^ k * Td := by rw [cancel_powers Tc_Tci, one_mul]

/-- Exact fixed word at n=1, for every k including zero. -/
theorem fixed_C (k : ℕ) : ((t^1) * g k) wC = wC := by
  rw [pow_one, first_member, coe_mul_apply, Td_fix_C, pow_fix Tci_fix_C]

/-- Exact fixed word at n=k+1, for every k including zero. -/
theorem fixed_Cp (k : ℕ) : ((t^(k+1)) * g k) wCp = wCp := by
  rw [second_member, coe_mul_apply, Td_fix_Cp, pow_fix Ta_fix_Cp]

/-- The initial factor of g, with a proved left inverse below. -/
def initial (k : ℕ) : Monoid.End F := Tai * Tci ^ (k+1)

def undo (k : ℕ) : Monoid.End F := Tc ^ (k+1) * Ta

theorem undo_initial (k : ℕ) : undo k * initial k = 1 := by
  unfold undo initial
  calc
    (Tc ^ (k+1) * Ta) * (Tai * Tci ^ (k+1)) =
        Tc ^ (k+1) * ((Ta * Tai) * Tci ^ (k+1)) := by simp only [mul_assoc]
    _ = 1 := by rw [Ta_Tai, one_mul, cancel_powers Tc_Tci]

/-- Additional commutation support checked on the accepted generators. -/
theorem Ta_Tci : Ta * Tci = Tci * Ta := ext_gen (by decide)

theorem initial_commute_a (k : ℕ) : Commute Ta (initial k) := by
  have h1 : Commute Ta Tai := Ta_Tai.trans Tai_Ta.symm
  have h2 : Commute Ta Tci := Ta_Tci
  exact h1.mul_right (h2.pow_right (k+1))

theorem initial_commute_c (k : ℕ) : Commute Tc (initial k) := by
  have h1 : Commute Tc Tai := Tai_Tc.symm
  have h2 : Commute Tc Tci := Tc_Tci.trans Tci_Tc.symm
  exact h1.mul_right (h2.pow_right (k+1))

/-- A left inverse reflects conjugacy, including the inverse-word case. -/
theorem reflect_conj {e b : Monoid.End F} (hbe : b * e = 1) {u v : F}
    (h : IsConj (e u) (e v)) : IsConj u v := by
  have hb := MonoidHom.map_isConj b h
  change IsConj ((b * e) u) ((b * e) v) at hb
  rw [hbe] at hb
  exact hb

/-- Transport a nonconjugacy pair through a commuting endomorphism with left inverse. -/
theorem transport {e b z : Monoid.End F} {u : F} (hbe : b * e = 1)
    (hc : Commute z e) (hn : ¬ IsConj (z u) u ∧ ¬ IsConj (z u) u⁻¹) :
    ¬ IsConj (z (e u)) (e u) ∧ ¬ IsConj (z (e u)) (e u)⁻¹ := by
  have he : z (e u) = e (z u) := by
    rw [← coe_mul_apply, hc.eq, coe_mul_apply]
  refine ⟨fun h => hn.1 (reflect_conj hbe ?_), fun h => hn.2 (reflect_conj hbe ?_)⟩
  · rwa [he] at h
  · rwa [he, ← map_inv] at h

/-- Required nonconjugacy at Ta, for every k. -/
theorem nonconj_a (k : ℕ) :
    ¬ IsConj (Ta ((g k) wa)) ((g k) wa) ∧
    ¬ IsConj (Ta ((g k) wa)) ((g k) wa)⁻¹ := by
  exact transport (e := initial k) (b := undo k) (u := Td wa) (undo_initial k) (initial_commute_a k) F4_base_a

/-- Required nonconjugacy at Tc, for every k. -/
theorem nonconj_c (k : ℕ) :
    ¬ IsConj (Tc ((g k) wa)) ((g k) wa) ∧
    ¬ IsConj (Tc ((g k) wa)) ((g k) wa)⁻¹ := by
  exact transport (e := initial k) (b := undo k) (u := Td wa) (undo_initial k) (initial_commute_c k) F4_base_c

end Multitwist.V2

