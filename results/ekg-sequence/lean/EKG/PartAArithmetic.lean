import EKG.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
Elementary arithmetic for the finite predecessor injection in Part A.
These lemmas do not assume any additional property of the EKG sequence.
-/

namespace EKG

/-- A large prime shared with `2 * r * M * j` must be the distinguished
prime `r`, when both auxiliary factors are smaller than the lower bound.
-/
theorem partA_factor_forcing {d r M j : ℕ} {B : ℝ}
    (hr : r.Prime) (hshared : SharedPrime d (2 * r * M * j))
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ d → B < (p : ℝ))
    (hB : 3 < B) (hM : 2 ≤ M) (hj : 0 < j)
    (hMB : (M : ℝ) < B) (hjB : (j : ℝ) < B) : r ∣ d := by
  obtain ⟨p, hp, hpd, hpy⟩ := hshared
  have hpB : B < (p : ℝ) := hlarge p hp hpd
  rcases hp.dvd_mul.mp hpy with hp2rM | hpj
  · rcases hp.dvd_mul.mp hp2rM with hp2r | hpM
    · rcases hp.dvd_mul.mp hp2r with hp2 | hpr
      · have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hp2
        have hp_le_two_real : (p : ℝ) ≤ 2 := by exact_mod_cast hp_le_two
        linarith
      · have hpr_eq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
        exact hpr_eq ▸ hpd
    · have hMpos : 0 < M := by omega
      have hp_le_M : p ≤ M := Nat.le_of_dvd hMpos hpM
      have hp_le_M_real : (p : ℝ) ≤ (M : ℝ) := by exact_mod_cast hp_le_M
      linarith
  · have hp_le_j : p ≤ j := Nat.le_of_dvd hj hpj
    have hp_le_j_real : (p : ℝ) ≤ (j : ℝ) := by exact_mod_cast hp_le_j
    linarith

/-- An integer smaller than the cube of a lower bound for all its prime
factors has a prime cofactor after division by any prime factor, provided
that the integer itself is composite. Repeated prime factors are allowed.
-/
theorem partA_prime_cofactor {d r : ℕ} {B : ℝ}
    (hdpos : 0 < d) (hdnotprime : ¬ d.Prime)
    (hr : r.Prime) (hrd : r ∣ d)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ d → B < (p : ℝ))
    (hB : 0 < B) (hdcube : (d : ℝ) < B ^ 3) : (d / r).Prime := by
  obtain ⟨q, hdq⟩ := hrd
  have hquot : d / r = q := by
    rw [hdq]
    exact Nat.mul_div_cancel_left q hr.pos
  rw [hquot]
  have hqpos : 0 < q := by
    by_contra h
    have hqzero : q = 0 := by omega
    rw [hqzero, Nat.mul_zero] at hdq
    omega
  have hqone : q ≠ 1 := by
    intro h
    apply hdnotprime
    rw [hdq, h, Nat.mul_one]
    exact hr
  by_contra hqnotprime
  let p := q.minFac
  have hp : p.Prime := Nat.minFac_prime hqone
  have hqd : q ∣ d := by
    rw [hdq]
    exact Nat.dvd_mul_left q r
  have hpd : p ∣ d := (Nat.minFac_dvd q).trans hqd
  have hrB : B < (r : ℝ) := hlarge r hr ⟨q, hdq⟩
  have hpB : B < (p : ℝ) := hlarge p hp hpd
  have hsq : (p : ℝ) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.minFac_sq_le_self hqpos hqnotprime)
  have hpsq : B ^ 2 < (p : ℝ) ^ 2 :=
    (sq_lt_sq₀ hB.le (hB.le.trans hpB.le)).mpr hpB
  have hqBsq : B ^ 2 < (q : ℝ) := hpsq.trans_le hsq
  have hdreal : (d : ℝ) = (r : ℝ) * (q : ℝ) := by
    exact_mod_cast hdq
  have hcube : B ^ 3 < (d : ℝ) := by
    calc
      B ^ 3 = B * B ^ 2 := by ring
      _ < (r : ℝ) * B ^ 2 := mul_lt_mul_of_pos_right hrB (sq_pos_of_pos hB)
      _ < (r : ℝ) * (q : ℝ) := mul_lt_mul_of_pos_left hqBsq (hB.trans hrB)
      _ = (d : ℝ) := hdreal.symm
  exact lt_asymm hdcube hcube

end EKG
