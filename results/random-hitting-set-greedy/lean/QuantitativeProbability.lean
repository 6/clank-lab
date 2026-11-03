import PathProbability
import Mathlib.Data.Nat.Choose.Bounds

/-! Explicit elementary estimates for the parameters m = k, n = k^10,
p = 1/(10 k^4). -/
namespace ADG
open Finset
open scoped Classical

/-- Bernoulli's inequality, in the form used for avoidance probabilities. -/
theorem avoidance_ge_linear (x : ℝ) (hx : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ)*x ≤ (1-x)^n := by
  have h := one_add_mul_le_pow (a := -x) (by linarith : -2 ≤ -x) n
  convert h using 1 <;> ring

theorem pathQ_ge_half {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hmp : (m : ℝ)*p ≤ 1/2) : p^3 / 2 ≤ pathQ m p := by
  have h := avoidance_ge_linear p hp' (m-3)
  have hsub : ((m-3 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 3
  have hmul := mul_le_mul_of_nonneg_right hsub hp
  have hpow : (1/2 : ℝ) ≤ (1-p)^(m-3) := by linarith
  have hres := mul_le_mul_of_nonneg_left hpow (pow_nonneg hp 3)
  unfold pathQ
  nlinarith

theorem forbiddenMass_nonneg {m : ℕ} (t : PathTuple m) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) : 0 ≤ forbiddenMass t p :=
  Finset.sum_nonneg (fun s hs => columnMass_nonneg m p hp hp' s)

theorem path_avoidance_ge_half {m n : ℕ} (t : PathTuple m) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hn : 1 ≤ n)
    (hF : (n : ℝ)*forbiddenMass t p ≤ 1/2) :
    (1/2 : ℝ) ≤ (1-forbiddenMass t p)^(n-3) := by
  have hnon := forbiddenMass_nonneg t p hp hp'
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hFn : forbiddenMass t p ≤ (n : ℝ)*forbiddenMass t p := by nlinarith
  have h := avoidance_ge_linear (forbiddenMass t p) (by linarith) (n-3)
  have hsub : ((n-3 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 3
  have hmul := mul_le_mul_of_nonneg_right hsub hnon
  linarith

theorem parameterP_pos {k : ℕ} (hk : 1 ≤ k) : 0 < parameterP k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  unfold parameterP
  positivity

theorem parameterP_le_one {k : ℕ} (hk : 1 ≤ k) : parameterP k ≤ 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (1 : ℝ) ≤ (k : ℝ)^4 := one_le_pow₀ hk'
  unfold parameterP
  apply (div_le_one (by positivity : 0 < 10*(k : ℝ)^4)).mpr
  linarith

theorem parameterP_row_product {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ)*parameterP k ≤ 1/10 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (k : ℝ) ≤ (k : ℝ)^4 := le_self_pow₀ hk' (by norm_num)
  unfold parameterP
  rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 10*(k : ℝ)^4)]
  nlinarith

theorem parameterQ_ge_half {k : ℕ} (hk : 1 ≤ k) :
    (parameterP k)^3 / 2 ≤ pathQ k (parameterP k) := by
  apply pathQ_ge_half _ (parameterP_pos hk).le (parameterP_le_one hk)
  linarith [parameterP_row_product hk]

theorem parameter_forbidden_scaled {k : ℕ} (hk : 1 ≤ k) (t : PathTuple k) :
    ((k^10 : ℕ) : ℝ)*forbiddenMass t (parameterP k) ≤ 7/1000 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hF := forbiddenMass_le t (parameterP k) (parameterP_pos hk).le (parameterP_le_one hk)
  have hchoose : (((k-1).choose 2 : ℕ) : ℝ) ≤ (k : ℝ)^2 := by
    have h₁ : (k-1).choose 2 ≤ (k-1)^2 := Nat.choose_le_pow _ _
    have h₂ : (k-1)^2 ≤ k^2 := Nat.pow_le_pow_left (Nat.sub_le k 1) 2
    exact_mod_cast h₁.trans h₂
  have hF' : forbiddenMass t (parameterP k) ≤ 7*(k : ℝ)^2*(parameterP k)^3 := by
    calc
      _ ≤ 7*(((k-1).choose 2 : ℕ) : ℝ)*(parameterP k)^3 := hF
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [hchoose] :
          7*(((k-1).choose 2 : ℕ) : ℝ) ≤ 7*(k : ℝ)^2)
          (pow_nonneg (parameterP_pos hk).le 3)
  have hscale := mul_le_mul_of_nonneg_left hF' (show 0 ≤ ((k^10 : ℕ) : ℝ) by positivity)
  convert hscale using 1
  push_cast
  unfold parameterP
  field_simp [hk0]
  <;> ring

theorem parameter_path_avoidance_ge_half {k : ℕ} (hk : 1 ≤ k) (t : PathTuple k) :
    (1/2 : ℝ) ≤ (1-forbiddenMass t (parameterP k))^(k^10-3) := by
  apply path_avoidance_ge_half t _ (parameterP_pos hk).le (parameterP_le_one hk)
  · exact one_le_pow₀ hk
  · linarith [parameter_forbidden_scaled hk t]

theorem path_probability_ge_simple {m n : ℕ} (t : PathTuple m) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hn : 3 ≤ n)
    (hq : p^3 / 2 ≤ pathQ m p)
    (hF : (1/2 : ℝ) ≤ (1-forbiddenMass t p)^(n-3)) :
    ((n*(n-1)*(n-2) : ℕ) : ℝ)*p^9/48 ≤
      matrixProb m n p (fun A => pathOccurs A t) := by
  have hbase : 0 ≤ 1-p := by linarith
  have hqnon : 0 ≤ pathQ m p := by unfold pathQ; positivity
  calc
    _ = (((n*(n-1)*(n-2) : ℕ) : ℝ)/3) * (p^3/2)^3 * (1/2) := by ring
    _ ≤ (((n*(n-1)*(n-2) : ℕ) : ℝ)/3) * (pathQ m p)^3 * (1/2) := by
      gcongr
    _ ≤ (((n*(n-1)*(n-2) : ℕ) : ℝ)/3) * (pathQ m p)^3 *
        (1-forbiddenMass t p)^(n-3) := by gcongr
    _ = _ := (path_probability t p hp hp' hn).symm

theorem fallingThree_ge_quarter (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ)^3 / 4 ≤ ((n*(n-1)*(n-2) : ℕ) : ℝ) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have h₂ : ((n-2 : ℕ) : ℝ) = (n : ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hprod : 0 ≤ (n : ℝ)*((n : ℝ)-1) := mul_nonneg (by positivity) (by linarith)
  push_cast
  rw [h₁, h₂]
  calc
    _ = (n : ℝ)*((n : ℝ)/2)*((n : ℝ)/2) := by ring
    _ ≤ _ := by gcongr <;> linarith

theorem parameter_path_probability_lower {k : ℕ} (hk : 14 ≤ k) (t : PathTuple k) :
    1 / (192 * 10^9 * (k : ℝ)^6) ≤
      matrixProb k (k^10) (parameterP k) (fun A => pathOccurs A t) := by
  have hk1 : 1 ≤ k := by omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hnk : k ≤ k^10 := le_self_pow₀ hk1 (by norm_num)
  have hn : 4 ≤ k^10 := by omega
  calc
    _ = (((k^10 : ℕ) : ℝ)^3/4)*(parameterP k)^9/48 := by
      push_cast
      unfold parameterP
      field_simp [hk0]
      <;> ring
    _ ≤ (((k^10*(k^10-1)*(k^10-2) : ℕ) : ℝ))*(parameterP k)^9/48 := by
      gcongr
      · exact pow_nonneg (parameterP_pos hk1).le 9
      · exact fallingThree_ge_quarter _ hn
    _ ≤ _ := path_probability_ge_simple t _ (parameterP_pos hk1).le
      (parameterP_le_one hk1) (by omega) (parameterQ_ge_half hk1)
      (parameter_path_avoidance_ge_half hk1 t)

theorem parameter_noLarge_failure_bound {k : ℕ} (hk : 1 ≤ k) :
    matrixProb k (k^10) (parameterP k) (fun A => ¬ noLargeColumns A) ≤
      1 / (10000 * (k : ℝ)^2) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  calc
    _ ≤ ((k^10 : ℕ) : ℝ)*(k.choose 4 : ℝ)*(parameterP k)^4 :=
      noLargeColumns_failure_bound _ _ _ (parameterP_pos hk).le (parameterP_le_one hk)
    _ ≤ ((k^10 : ℕ) : ℝ)*(k : ℝ)^4*(parameterP k)^4 := by
      gcongr
      exact_mod_cast Nat.choose_le_pow k 4
    _ = _ := by
      push_cast
      unfold parameterP
      field_simp [hk0]
      <;> ring

/-- The single quadratic binomial term controls iid avoidance. -/
theorem avoidance_le_binomial (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    (1-r)^n ≤ 1 / ((n.choose 2 : ℝ)*r^2) := by
  have hb : 0 ≤ 1-r := by linarith
  have hsum := Finset.single_le_sum
    (s := Finset.range (n+1)) (f := fun j => r^j*(1-r)^(n-j)*(n.choose j : ℝ))
    (fun j hj => by positivity) (show 2 ∈ Finset.range (n+1) by simp; omega)
  have hterm : r^2*(1-r)^(n-2)*(n.choose 2 : ℝ) ≤ 1 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), r^j*(1-r)^(n-j)*(n.choose j : ℝ) := hsum
      _ = 1 := by rw [← add_pow]; simp
  have hc : 0 < (n.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  apply (le_div_iff₀ (mul_pos hc (sq_pos_of_pos hr))).mpr
  calc
    _ ≤ (1-r)^(n-2)*((n.choose 2 : ℝ)*r^2) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hb (by linarith) (Nat.sub_le n 2)) (by positivity)
    _ ≤ 1 := by nlinarith [hterm]

theorem parameter_pair_mass_ge_half {k : ℕ} (hk : 1 ≤ k) :
    (parameterP k)^2/2 ≤ (parameterP k)^2*(1-parameterP k)^(k-2) := by
  have hp := (parameterP_pos hk).le
  have h := avoidance_ge_linear (parameterP k) (parameterP_le_one hk) (k-2)
  have hsub : ((k-2 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 2
  have hm := mul_le_mul_of_nonneg_right hsub hp
  have hsmall := parameterP_row_product hk
  have hh : (1/2 : ℝ) ≤ (1-parameterP k)^(k-2) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (parameterP k))]

theorem chooseTwo_ge_quarter (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ)^2/4 ≤ (n.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem pair_avoidance_le_simple (p : ℝ) (hp : 0 < p) (r : ℝ)
    (hr : p^2/2 ≤ r) (hr' : r ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    (1-r)^n ≤ 16 / ((n : ℝ)^2*p^4) := by
  have hr0 : 0 < r := by nlinarith [sq_pos_of_pos hp]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hden : (n : ℝ)^2*p^4/16 ≤ (n.choose 2 : ℝ)*r^2 := by
    calc
      _ = ((n : ℝ)^2/4)*(p^2/2)^2 := by ring
      _ ≤ _ := by
        apply mul_le_mul (chooseTwo_ge_quarter n hn)
          (pow_le_pow_left₀ (by positivity : 0 ≤ p^2/2) hr 2) (by positivity) (by positivity)
  calc
    _ ≤ 1/((n.choose 2 : ℝ)*r^2) := avoidance_le_binomial r hr0 hr' n hn
    _ ≤ 1/((n : ℝ)^2*p^4/16) := one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by field_simp <;> ring

theorem pathTuple_card_ge {k : ℕ} (hk : 14 ≤ k) :
    (k : ℝ)^7/128 ≤ (Fintype.card (PathTuple k) : ℝ) := by
  rw [Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  have hk' : (14 : ℝ) ≤ k := by exact_mod_cast hk
  have hsub : ((k+1-7 : ℕ) : ℝ) = (k : ℝ)-6 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hfactor : (k : ℝ)^7/128 ≤ (((k+1-7 : ℕ) : ℝ))^7 := by
    rw [hsub]
    calc
      _ = ((k : ℝ)/2)^7 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) 7
  exact hfactor.trans (by exact_mod_cast Nat.pow_sub_le_descFactorial k 7)

theorem parameter_allPairs_failure_bound {k : ℕ} (hk : 2 ≤ k) :
    matrixProb k (k^10) (parameterP k) (fun A => ¬ allExactPairs A) ≤
      160000 / (k : ℝ)^2 := by
  have hk1 : 1 ≤ k := by omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hp := parameterP_pos hk1
  have hp' := parameterP_le_one hk1
  let r := (parameterP k)^2*(1-parameterP k)^(k-2)
  have hb : 0 ≤ 1-parameterP k := by linarith
  have hr : (parameterP k)^2/2 ≤ r := parameter_pair_mass_ge_half hk1
  have hr' : r ≤ 1 := by
    have h₁ := pow_le_one₀ (n := 2) hp.le hp'
    have h₂ := pow_le_one₀ (n := k-2) hb (by linarith : 1-parameterP k ≤ 1)
    dsimp [r]
    calc
      _ ≤ (parameterP k)^2 * 1 :=
        mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
      _ ≤ 1 := by nlinarith
  have hn : 2 ≤ k^10 := (le_self_pow₀ hk1 (by norm_num) : k ≤ k^10) |>.trans' hk
  have havoid := pair_avoidance_le_simple _ hp r hr hr' (k^10) hn
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ)^2 := by exact_mod_cast Nat.choose_le_pow k 2
  calc
    _ ≤ (k.choose 2 : ℝ)*(1-r)^(k^10) :=
      allExactPairs_failure_bound _ _ _ hp.le hp'
    _ ≤ (k : ℝ)^2*(16 / (((k^10 : ℕ) : ℝ)^2*(parameterP k)^4)) := by
      exact mul_le_mul hc havoid (pow_nonneg (by linarith) _) (sq_nonneg _)
    _ = _ := by
      push_cast
      unfold parameterP
      field_simp [hk0]
      <;> ring

end ADG
