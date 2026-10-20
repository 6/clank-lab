import SolutionEndpoint
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open EKG.CanonicalEndpoint Filter Topology

namespace EKGShortCycles

private theorem a_pos (n : ℕ) : 0 < a n := EKG.canonical.positive (n - 1)

/-- Integral factors for the three branches of the smoothing map. -/
private theorem factors (n : ℕ) : ∃ d e : ℕ,
    0 < d ∧ d ≤ 2 ∧ 0 < e ∧ e ≤ 3 ∧ a n * d = b n * e := by
  unfold b smoothValue
  split_ifs with h₁ h₂
  · exact ⟨2, 1, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨2, 3, by omega, by omega, by omega, by omega, by nlinarith [h₂.2.2]⟩
  · exact ⟨1, 1, by omega, by omega, by omega, by omega, by omega⟩

/-- The smoothed value eventually lies strictly above its index and below
any prescribed larger linear function. -/
private theorem eventually_bounds (q : ℝ) (hq : 1 < q) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, (n : ℝ) < b n ∧ (b n : ℝ) ≤ q * n := by
  obtain ⟨N, hN, hmain⟩ := ekg_sharp_all_index (1 / 6) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (1 / (q - 1)))
  refine ⟨max N K, by omega, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnK : K ≤ n := (le_max_right _ _).trans hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlarge : 1 / (q - 1) ≤ Real.log (n : ℝ) := by
    rw [← Real.log_exp (1 / (q - 1))]
    exact Real.log_le_log (Real.exp_pos _) (le_trans hK.le (by exact_mod_cast hnK))
  have hlog : 1 ≤ (q - 1) * Real.log (n : ℝ) := by
    have := (div_le_iff₀ (sub_pos.mpr hq)).mp hlarge
    nlinarith
  have hr : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos hn0 hl
  have hrq : (n : ℝ) / Real.log (n : ℝ) ≤ (q - 1) * n := by
    apply (div_le_iff₀ hl).mpr
    nlinarith
  have herr := abs_le.mp (hmain n hnN)
  have heq : (n : ℝ) / (3 * Real.log (n : ℝ)) =
      ((n : ℝ) / Real.log (n : ℝ)) / 3 := by ring
  rw [heq] at herr
  constructor <;> nlinarith [herr.1, herr.2]

private theorem choose_ratio (L : ℕ) : ∃ q : ℝ,
    1 < q ∧ q ^ L < 1 + 1 / (3 : ℝ) ^ L := by
  have he : 0 < 1 / (3 : ℝ) ^ L := by positivity
  have hc : ContinuousAt (fun x : ℝ => x ^ L) 1 := continuousAt_id.pow L
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc (1 / (3 : ℝ) ^ L) he
  refine ⟨1 + δ / 2, by linarith, ?_⟩
  have hd : dist (1 + δ / 2) (1 : ℝ) < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < 1 + δ / 2 - 1)]
    linarith
  have := hclose hd
  rw [Real.dist_eq, one_pow] at this
  linarith [(abs_lt.mp this).2]

/-- A short cycle cannot stay wholly beyond the asymptotic threshold. -/
private theorem cycle_hits_small (L : ℕ) (q : ℝ) (hq : 1 < q)
    (hql : q ^ L < 1 + 1 / (3 : ℝ) ^ L) (N : ℕ)
    (hb : ∀ n ≥ N, (n : ℝ) < b n ∧ (b n : ℝ) ≤ q * n)
    (m l : ℕ) (hm : 0 < m) (hl : 0 < l) (hlL : l ≤ L)
    (hcycle : a^[l] m = m) : ∃ j < l, a^[j] m < N := by
  classical
  by_contra! hlarge
  let x : ℕ → ℕ := fun j => a^[j] m
  have hxpos : ∀ j, 0 < x j := by
    intro j
    cases j with
    | zero => exact hm
    | succ j =>
      change 0 < a^[j + 1] m
      rw [Function.iterate_succ_apply']
      exact a_pos _
  have hshift : (∏ j ∈ Finset.range l, a (x j)) = ∏ j ∈ Finset.range l, x j := by
    have h := (Finset.prod_range_succ x l).symm.trans (Finset.prod_range_succ' x l)
    have hxl : x l = m := hcycle
    have hx0 : x 0 = m := rfl
    rw [hxl, hx0] at h
    have hh := mul_right_cancel₀ (ne_of_gt hm) h
    simpa only [x, Function.iterate_succ_apply'] using hh.symm
  choose d e hd using factors
  let D : ℕ := ∏ j ∈ Finset.range l, d (x j)
  let E : ℕ := ∏ j ∈ Finset.range l, e (x j)
  let P : ℝ := ∏ j ∈ Finset.range l, (x j : ℝ)
  let Q : ℝ := ∏ j ∈ Finset.range l, (b (x j) : ℝ)
  have hDpos : 0 < D := Finset.prod_pos (fun j _ => (hd (x j)).1)
  have hEpos : 0 < E := Finset.prod_pos (fun j _ => (hd (x j)).2.2.1)
  have hEbound : E ≤ 3 ^ L := by
    have he : E ≤ 3 ^ l := by
      simpa [E] using Finset.prod_le_pow_card (Finset.range l) (fun j => e (x j)) 3
        (fun j _ => (hd (x j)).2.2.2.1)
    exact he.trans (Nat.pow_le_pow_right (by omega) hlL)
  have hP : 0 < P := Finset.prod_pos (fun j _ => by exact_mod_cast hxpos j)
  have hPQ : P < Q := by
    apply Finset.prod_lt_prod_of_nonempty₀
      (fun j _ => by exact_mod_cast hxpos j)
      (fun j hj => (hb (x j) (hlarge j (Finset.mem_range.mp hj))).1)
    exact ⟨0, Finset.mem_range.mpr hl⟩
  have hQ : Q ≤ q ^ L * P := by
    have hprod : Q ≤ ∏ j ∈ Finset.range l, q * (x j : ℝ) :=
      Finset.prod_le_prod₀ (fun j _ => by positivity)
        (fun j hj => (hb (x j) (hlarge j (Finset.mem_range.mp hj))).2)
    have heq : (∏ j ∈ Finset.range l, q * (x j : ℝ)) = q ^ l * P := by
      simp [Finset.prod_mul_distrib, P]
    rw [heq] at hprod
    exact hprod.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hq.le hlL) hP.le)
  have hidentity : (D : ℝ) * P = (E : ℝ) * Q := by
    have hi : (∏ j ∈ Finset.range l, a (x j)) * D =
        (∏ j ∈ Finset.range l, b (x j)) * E := by
      simp only [D, E, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun j _ => (hd (x j)).2.2.2.2)
    rw [hshift] at hi
    have hiR : P * (D : ℝ) = Q * (E : ℝ) := by
      dsimp [P, Q]
      exact_mod_cast hi
    simpa only [mul_comm] using hiR
  have hDE : E < D := by
    have he : (0 : ℝ) < E := by exact_mod_cast hEpos
    have hh : (E : ℝ) * P < (D : ℝ) * P := by
      rw [hidentity]
      exact mul_lt_mul_of_pos_left hPQ he
    exact_mod_cast (mul_lt_mul_iff_left₀ hP).mp hh
  have hDle : (D : ℝ) ≤ E * q ^ L := by
    apply (mul_le_mul_iff_left₀ hP).mp
    rw [hidentity]
    nlinarith [mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ E by positivity)]
  have hthree : (0 : ℝ) < 3 ^ L := by positivity
  have hEb : (E : ℝ) ≤ 3 ^ L := by exact_mod_cast hEbound
  have hfrac : (E : ℝ) * (1 / (3 : ℝ) ^ L) ≤ 1 := by
    simpa [div_eq_mul_inv] using (div_le_one hthree).mpr hEb
  have hstrict : (E : ℝ) * q ^ L < E + 1 := by
    have := mul_lt_mul_of_pos_left hql (show (0 : ℝ) < E by exact_mod_cast hEpos)
    nlinarith
  have hgap : (E : ℝ) + 1 ≤ D := by exact_mod_cast hDE
  linarith

private theorem orbit_eq (m l j : ℕ) (hj : j ≤ l) (hc : a^[l] m = m) :
    Set.range (fun k : ℕ => a^[k] (a^[j] m)) = Set.range (fun k : ℕ => a^[k] m) := by
  have hreturn : a^[l - j] (a^[j] m) = m := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj, hc]
  apply Set.Subset.antisymm
  · rintro _ ⟨k, rfl⟩
    exact ⟨k + j, Function.iterate_add_apply _ _ _ _⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨k + (l - j), by dsimp only; rw [Function.iterate_add_apply, hreturn]⟩

end EKGShortCycles

/-- There are only finitely many positive EKG cycles of any bounded length. -/
theorem ekg_short_cycles_finite :
    ∀ L : ℕ, {C : Set ℕ | ∃ m : ℕ, 0 < m ∧
      (∃ l : ℕ, 0 < l ∧ l ≤ L ∧ a^[l] m = m) ∧
      C = Set.range (fun j : ℕ => a^[j] m)}.Finite := by
  intro L
  obtain ⟨q, hq, hql⟩ := EKGShortCycles.choose_ratio L
  obtain ⟨N, _, hb⟩ := EKGShortCycles.eventually_bounds q hq
  apply Set.Finite.subset ((Set.finite_Iio N).image
    (fun m : ℕ => Set.range (fun j : ℕ => a^[j] m)))
  rintro C ⟨m, hm, ⟨l, hl, hlL, hc⟩, rfl⟩
  obtain ⟨j, hj, hsmall⟩ := EKGShortCycles.cycle_hits_small L q hq hql N hb m l hm hl hlL hc
  exact ⟨a^[j] m, hsmall, EKGShortCycles.orbit_eq m l j hj.le hc⟩

