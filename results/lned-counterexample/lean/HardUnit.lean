import Endpoint
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- One all-index Bernoulli unit. No image-membership assertion is inferred here. -/
namespace LNEDPilot
open scoped Nat Real
open Polynomial

lemma bernoulliFun_rat_eval (n : ℕ) (q : ℚ) :
    bernoulliFun n (q : ℝ) = (((Polynomial.bernoulli n).eval q : ℚ) : ℝ) := by
  rw [bernoulliFun, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (algebraMap ℚ ℝ) q

lemma fourier_scale_ne_zero (n k : ℕ) :
    (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ n / 2 / (n.factorial : ℝ) ≠ 0 := by
  exact div_ne_zero
    (div_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
      (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero n)

lemma bernoulli_half_gap_odd (k : ℕ) (hk : k ≠ 0) :
    (Polynomial.bernoulli (2 * k + 1)).eval (1 / 2 : ℚ) -
      (Polynomial.bernoulli (2 * k + 1)).eval 0 = 0 := by
  have hs := hasSum_one_div_nat_pow_mul_sin hk
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have hf : (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k + 1) *
      Real.sin (2 * Real.pi * n * (1 / 2 : ℝ))) = (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    rw [show 2 * Real.pi * (n : ℝ) * (1 / 2 : ℝ) = (n : ℝ) * Real.pi by ring,
      Real.sin_nat_mul_pi, mul_zero]
  rw [hf] at hs
  have hz := hs.unique (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have hbhalf : bernoulliFun (2 * k + 1) (1 / 2 : ℝ) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (fourier_scale_ne_zero (2 * k + 1) k)
  have hs0 := hasSum_one_div_nat_pow_mul_sin hk
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  simp only [mul_zero, Real.sin_zero] at hs0
  have hz0 := hs0.unique (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have hbzero : bernoulliFun (2 * k + 1) 0 = 0 :=
    (mul_eq_zero.mp hz0).resolve_left (fourier_scale_ne_zero (2 * k + 1) k)
  have hhalf : bernoulliFun (2 * k + 1) (1 / 2 : ℝ) =
      (((Polynomial.bernoulli (2 * k + 1)).eval (1 / 2 : ℚ) : ℚ) : ℝ) := by
    simpa using bernoulliFun_rat_eval (2 * k + 1) (1 / 2)
  have hzero : bernoulliFun (2 * k + 1) 0 =
      (((Polynomial.bernoulli (2 * k + 1)).eval 0 : ℚ) : ℝ) := by
    simpa using bernoulliFun_rat_eval (2 * k + 1) 0
  rw [hhalf] at hbhalf
  rw [hzero] at hbzero
  have hcast : (((Polynomial.bernoulli (2 * k + 1)).eval (1 / 2 : ℚ) : ℚ) : ℝ) -
      (((Polynomial.bernoulli (2 * k + 1)).eval 0 : ℚ) : ℝ) = 0 := by
    rw [hbhalf, hbzero, sub_self]
  exact_mod_cast hcast

lemma bernoulli_half_gap_even (k : ℕ) (hk : k ≠ 0) :
    (Polynomial.bernoulli (2 * k)).eval (1 / 2 : ℚ) -
      (Polynomial.bernoulli (2 * k)).eval 0 ≠ 0 := by
  intro hbad
  have hbq := sub_eq_zero.mp hbad
  have hhalf : bernoulliFun (2 * k) (1 / 2 : ℝ) =
      (((Polynomial.bernoulli (2 * k)).eval (1 / 2 : ℚ) : ℚ) : ℝ) := by
    simpa using bernoulliFun_rat_eval (2 * k) (1 / 2)
  have hzero : bernoulliFun (2 * k) 0 =
      (((Polynomial.bernoulli (2 * k)).eval 0 : ℚ) : ℝ) := by
    simpa using bernoulliFun_rat_eval (2 * k) 0
  have hb : bernoulliFun (2 * k) (1 / 2 : ℝ) = bernoulliFun (2 * k) 0 := by
    rw [hhalf, hzero, hbq]
  have hs0 := hasSum_one_div_nat_pow_mul_cos hk
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have hsh := hasSum_one_div_nat_pow_mul_cos hk
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  let f : ℕ → ℝ := fun n =>
    1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * (0 : ℝ)) -
    1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * Real.pi * n * (1 / 2 : ℝ))
  have hs : HasSum f 0 := by
    have hh := hs0.sub hsh
    change HasSum f (_ * bernoulliFun (2 * k) 0 -
      _ * bernoulliFun (2 * k) (1 / 2 : ℝ)) at hh
    simpa only [hb, sub_self] using hh
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    rw [mul_zero, Real.cos_zero, mul_one]
    have ha : 0 ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
    have hc := Real.cos_le_one (2 * Real.pi * (n : ℝ) * (1 / 2 : ℝ))
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hc)]
  have hf1 : 0 < f 1 := by
    dsimp [f]
    norm_num only [Nat.cast_one, one_pow, div_one, mul_one, mul_zero,
      Real.cos_zero, one_mul]
    rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring, Real.cos_pi]
    norm_num
  have hp := hs.summable.tsum_pos hf 1 hf1
  rw [hs.tsum_eq] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- The single uniform load-bearing unit, indexed exactly for the endpoint's powers. -/
theorem bernoulli_half_gap_all (m : ℕ) (hm : 1 ≤ m) :
    ((Polynomial.bernoulli (2 * m + 1)).eval (1 / 2 : ℚ) -
      (Polynomial.bernoulli (2 * m + 1)).eval 0 = 0) ∧
    ((Polynomial.bernoulli (2 * (m + 1))).eval (1 / 2 : ℚ) -
      (Polynomial.bernoulli (2 * (m + 1))).eval 0 ≠ 0) := by
  exact ⟨bernoulli_half_gap_odd m (by omega),
    bernoulli_half_gap_even (m + 1) (by omega)⟩

#print axioms bernoulli_half_gap_all
end LNEDPilot
