import EKG3.TCoverP3
import EKG3.CorollaryA
import EKG3.PiBoundsP3
import EKG3.BTLargeSieve
import EKG3.SieveWeightFinite

namespace EKG3.P3.Middle
open EKG Real

theorem count_mono {x y : ℝ} (h : x ≤ y) : realPrimeCount x ≤ realPrimeCount y := by
  unfold realPrimeCount
  exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono h)

theorem count_le_piU {x : ℝ} (_hx : 1 < x) : realPrimeCount x ≤ piU x := by
  unfold piU
  split_ifs with h
  · exact le_rfl
  · exact (piBoundsP3_holds.2.2 x (by linarith)).2.2

theorem count_ge_piL (x : ℝ) (_hx : 88789 ≤ x) : piL x ≤ realPrimeCount x := by
  unfold piL
  split_ifs with h
  · exact le_rfl
  · exact (piBoundsP3_holds.2.2 x (by linarith)).2.1

theorem sqrt_count_le {n : ℕ} {x : ℝ}
    (hnx : (n : ℝ) ≤ x) (hx : 1 < sqrt x) :
    (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ piU (sqrt x) := by
  rw [primeCounting_sqrt_nat_eq]
  exact (count_mono (sqrt_le_sqrt hnx)).trans (count_le_piU hx)

theorem bt_nonneg {y : ℝ} (hy : 0 ≤ y) (q : ℕ) (hq : 6 ≤ q) : 0 ≤ bt y q := by
  have hlog : 0 ≤ log ((q : ℝ)+1) := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith)
  have hpi : 0 ≤ piU q :=
    (by unfold realPrimeCount; positivity : (0 : ℝ) ≤ realPrimeCount q).trans
      (count_le_piU (by exact_mod_cast (show 1 < q by omega)))
  unfold bt
  positivity

/-- The pointwise least integer bound for all natural prime windows. This
lets each row supply its own integer sieve witness without asserting
monotonicity of the real P3 upper envelope or of an optimizer. -/
def HasWindowBound (y b : ℕ) : Prop :=
  ∀ x : ℕ, ((Finset.Ioc x (x+y)).filter Nat.Prime).card ≤ b

theorem exists_window_bound (y : ℕ) : ∃ b, HasWindowBound y b := by
  refine ⟨y, fun x => ?_⟩
  exact (Finset.card_filter_le _ _).trans (by simp)

noncomputable def natBT (y : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_window_bound y)

theorem natBT_bounds (x y : ℕ) :
    ((Finset.Ioc x (x+y)).filter Nat.Prime).card ≤ natBT y := by
  classical
  exact Nat.find_spec (exists_window_bound y) x

theorem natBT_le_bt (y q : ℕ) (hy : 1 ≤ y) (hq : 6 ≤ q) :
    (natBT y : ℝ) ≤ bt y q := by
  classical
  have hb : HasWindowBound y ⌊bt y q⌋₊ := by
    intro x
    have h := largeSieveBT ((1/2 : ℝ)+x) y q (by positivity)
      (by exact_mod_cast hy) (by omega)
    have hf (n : ℕ) : ⌊(1/2 : ℝ)+n⌋₊ = n := by
      rw [Nat.floor_add_natCast (by norm_num : (0 : ℝ) ≤ 1/2)]
      norm_num
    have hfxy : ⌊(1/2 : ℝ)+x+y⌋₊ = x+y := by
      rw [add_assoc, ← Nat.cast_add, hf]
    have hcard := primeStructure_prime_Ioc_card x (x+y) (by omega)
    have hmono := Nat.monotone_primeCounting (show x ≤ x+y by omega)
    simp only [realPrimeCount, hfxy, hf, Nat.floor_natCast] at h
    have hden := G_gt_log_add_107 q hq
    have hdpos : 0 < log ((q : ℝ)+1) + 1.07 := by
      have := log_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith : (1 : ℝ) ≤ (q : ℝ)+1)
      linarith
    have hquot : ((y : ℝ)+(q : ℝ)^2) / G q ≤
        ((y : ℝ)+(q : ℝ)^2) / (log ((q : ℝ)+1)+1.07) :=
      div_le_div_of_nonneg_left (by positivity) hdpos hden.le
    have hp := count_le_piU (x := (q : ℝ)) (by exact_mod_cast (show 1 < q by omega))
    simp only [realPrimeCount, Nat.floor_natCast] at hp
    have hr : (((Finset.Ioc x (x+y)).filter Nat.Prime).card : ℝ) ≤ bt y q := by
      rw [hcard, Nat.cast_sub hmono]
      dsimp [bt]
      linarith
    exact Nat.le_floor hr
  have hn : natBT y ≤ ⌊bt y q⌋₊ := Nat.find_min' (exists_window_bound y) hb
  exact (by exact_mod_cast hn : (natBT y : ℝ) ≤ ⌊bt y q⌋₊).trans
    (Nat.floor_le (bt_nonneg (by positivity) q hq))

theorem cover_bootstrap {rows : List CoverRow}
    (hc : CoverChain e0 Kfin rows) :
    ∀ e, 2 ∣ e → e0 ≤ e → e < E1 →
      Nat.primeCounting (Nat.sqrt e)+2+natBT (3*envelope rows e+2) ≤ envelope rows e := by
  intro e _ he0 he1
  obtain ⟨r, hr, hea, heb, hrc, heq⟩ := cover_lookup hc he0 he1
  rw [heq]
  have hp : (Nat.primeCounting (Nat.sqrt e) : ℝ) ≤ r.pU := by
    apply sqrt_count_le (by exact_mod_cast heb.le)
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    have hlarge : 13328000000 ≤ r.eb := by dsimp [e0] at he0; omega
    exact_mod_cast (show 1 < r.eb by omega)
  have hb := hrc.2.2.2.2.2.2.1
  have hbt := natBT_le_bt (3*r.M+2) r.bq (by omega) hb.1
  have hn : (Nat.primeCounting (Nat.sqrt e) : ℝ)+2+natBT (3*r.M+2) ≤ r.M := by
    push_cast at hbt
    linarith only [hp, hb.2, hbt]
  exact_mod_cast hn

theorem bounded_K (hf : FiniteFc)
    {rows : List CoverRow} (hc : CoverChain e0 Kfin rows) :
    ∀ u, frontier canonical u < E1 → earlyEvenCount canonical u ≤ envelope rows (frontier canonical u) := by
  exact boundedCorollaryA_of_finite_bound canonical E1 e0 Kfin (envelope rows) natBT
    (envelope_mono rows) natBT_bounds hf (fun _ _ => envelope_base rows _)
    (cover_bootstrap hc)

end EKG3.P3.Middle
