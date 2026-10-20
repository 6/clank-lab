import EKG.PartAFinite

/-! Eventual numerical discharge for the actual canonical EKG sequence.
The integer `M` is fixed using `delta` before the observation time grows.
Only the proved old count and span bounds enter this module. -/

namespace EKG.PartA

open Real Filter

/-- The finite injection's numerical premises, together with the two
additional bounds used when it is assembled with localization. -/
structure ExcursionParameters (t M : ℕ) (B : ℝ) : Prop where
  frontier_large : 9 ≤ frontier canonical t
  gap_large : 6 * (earlyEvenCount canonical t + 1) <
    nonTickTop canonical t - frontier canonical t
  scale_large : 3 < B
  multiplier_lt : (M : ℝ) < B
  gap_scale : 4 * B * (earlyEvenCount canonical t + 1 : ℕ) ≤
    (nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ)
  cube : (nonTickTop canonical t : ℝ) < B ^ 3
  comparable : (nonTickTop canonical t : ℝ) < 2 * (frontier canonical t : ℝ)
  stride : ∀ r : ℕ, r ^ 2 ≤ nonTickTop canonical t →
    nonTickTop canonical t ≤ frontier canonical t +
      2 * r * (earlyEvenCount canonical t + 1) →
    (nonTickTop canonical t : ℝ) ≤ (2 * r * M : ℕ) * B

/-- Every fixed positive normalized excursion eventually satisfies all
finite-injection premises, with one fixed multiplier. -/
theorem eventually_excursion_parameters (delta : ℝ) (hdelta : 0 < delta) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ᶠ t : ℕ in atTop,
      delta * logRate (frontier canonical t) ≤
        (nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ) →
      ExcursionParameters t M
        (delta / (4 * 793) * Real.sqrt (frontier canonical t)) := by
  let beta : ℝ := delta / (4 * 793)
  have hb : 0 < beta := by dsimp [beta]; positivity
  have hb2 : 0 < beta ^ 2 := sq_pos_of_pos hb
  have hb3 : 0 < beta ^ 3 := pow_pos hb 3
  have hbeta : 4 * beta * 793 = delta := by dsimp [beta]; ring
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / beta ^ 2)
  let M := N + 2
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hMN : (N : ℝ) ≤ M := by dsimp [M]; push_cast; linarith
  have hN' : 1 < (N : ℝ) * beta ^ 2 := (div_lt_iff₀ hb2).mp hN
  have hbM : 1 ≤ beta ^ 2 * M := by
    have h := mul_le_mul_of_nonneg_left hMN hb2.le
    nlinarith only [h, hN']
  let D : ℝ := 4 * 793 ^ 2 + 2 * 793
  have hD : 0 < D := by dsimp [D]; norm_num
  have hf : Tendsto (fun t => (frontier canonical t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)
  have hs : Tendsto (fun t => Real.sqrt (frontier canonical t)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hf
  have hl : Tendsto (fun t => Real.log (frontier canonical t)) atTop atTop :=
    Real.tendsto_log_atTop.comp hf
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_early_count_bound canonical,
    eventually_nonTickTop_log_span canonical,
    hf.eventually (eventually_gt_atTop (9 : ℝ)),
    hl.eventually (eventually_gt_atTop D),
    hs.eventually (eventually_gt_atTop ((M : ℝ) / beta)),
    hs.eventually (eventually_gt_atTop (3 / beta)),
    hs.eventually (eventually_gt_atTop (6 * 793 / delta)),
    hs.eventually (eventually_gt_atTop (2 / beta ^ 3))]
    with t hcount hspan he9 hlog hrootM hroot3 hrootgap hrootcube
  intro hgap
  let e : ℝ := frontier canonical t
  let v : ℝ := nonTickTop canonical t
  let k : ℝ := (earlyEvenCount canonical t + 1 : ℕ)
  let s : ℝ := Real.sqrt e
  let B : ℝ := beta * s
  have he : 0 < e := by dsimp [e]; linarith
  have hspos : 0 < s := Real.sqrt_pos.2 he
  have hsq : s ^ 2 = e := Real.sq_sqrt he.le
  have hlpos : 0 < Real.log e := by dsimp [e]; linarith
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hMreal : 0 ≤ (M : ℝ) := by positivity
  have hkc : k * Real.log e ≤ 793 * s := by
    change k ≤ 793 * (s / Real.log e) at hcount
    rw [← mul_div_assoc] at hcount
    exact (le_div_iff₀ hlpos).mp hcount
  have hgc : delta * e ≤ (v - e) * Real.log e := by
    change delta * (e / Real.log e) ≤ v - e at hgap
    rw [← mul_div_assoc] at hgap
    exact (div_le_iff₀ hlpos).mp hgap
  have hspan' : v - e ≤ D * (e / Real.log e) := hspan
  have hDscale : D * (e / Real.log e) < e := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hlpos).mpr
    have h := mul_lt_mul_of_pos_right hlog he
    dsimp [e] at *
    nlinarith only [h]
  have hv : v < 2 * e := by linarith
  have hMlt : (M : ℝ) < B := by
    have h := (div_lt_iff₀ hb).mp hrootM
    dsimp [B, s, e]
    nlinarith only [h]
  have hthree : 3 < B := by
    have h := (div_lt_iff₀ hb).mp hroot3
    dsimp [B, s, e]
    nlinarith only [h]
  have hrootgap' : 6 * 793 < delta * s := by
    have h := (div_lt_iff₀ hdelta).mp hrootgap
    dsimp [s, e]
    nlinarith only [h]
  have hbig : 6 * 793 * s < delta * e := by
    calc
      6 * 793 * s < (delta * s) * s :=
        mul_lt_mul_of_pos_right hrootgap' hspos
      _ = delta * e := by rw [← hsq]; ring
  have hgapreal : 6 * k < v - e := by
    apply (mul_lt_mul_iff_left₀ hlpos).mp
    nlinarith only [hkc, hgc, hbig]
  have hev : frontier canonical t ≤ nonTickTop canonical t := by
    have hreal : e ≤ v := by linarith
    dsimp [e, v] at hreal
    exact_mod_cast hreal
  have hgapnat : 6 * (earlyEvenCount canonical t + 1) <
      nonTickTop canonical t - frontier canonical t := by
    have hcast : ((6 * (earlyEvenCount canonical t + 1) : ℕ) : ℝ) <
        ((nonTickTop canonical t - frontier canonical t : ℕ) : ℝ) := by
      rw [Nat.cast_sub hev]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgapreal
    exact_mod_cast hcast
  have hscalemul : (4 * B * k) * Real.log e ≤ delta * e := by
    calc
      (4 * B * k) * Real.log e = (4 * beta * s) * (k * Real.log e) := by
        dsimp [B]; ring
      _ ≤ (4 * beta * s) * (793 * s) :=
        mul_le_mul_of_nonneg_left hkc (by positivity)
      _ = (4 * beta * 793) * s ^ 2 := by ring
      _ = delta * e := by rw [hbeta, hsq]
  have hscale : 4 * B * k ≤ v - e :=
    (mul_le_mul_iff_left₀ hlpos).mp (hscalemul.trans hgc)
  have hrootcube' : 2 < beta ^ 3 * s := by
    have h := (div_lt_iff₀ hb3).mp hrootcube
    dsimp [s, e]
    nlinarith only [h]
  have hcube : v < B ^ 3 := by
    have hce : 2 * e < (beta ^ 3 * s) * e :=
      mul_lt_mul_of_pos_right hrootcube' he
    have hident : (beta ^ 3 * s) * e = B ^ 3 := by
      dsimp [B]
      rw [← hsq]
      ring
    rw [hident] at hce
    exact hv.trans hce
  refine ⟨by exact_mod_cast he9.le, hgapnat, hthree, hMlt, hscale,
    hcube, hv, ?_⟩
  intro r hrsq hrspan
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hrspan' : v ≤ e + 2 * (r : ℝ) * k := by
    dsimp [v, e, k]
    exact_mod_cast hrspan
  have hgapr : (v - e) * Real.log e ≤ (2 * (r : ℝ) * k) * Real.log e :=
    mul_le_mul_of_nonneg_right (by linarith) hlpos.le
  have hkr := mul_le_mul_of_nonneg_left hkc (show (0 : ℝ) ≤ 2 * r by positivity)
  have hrscale : delta * e ≤ (r : ℝ) * (2 * 793 * s) := by
    nlinarith only [hgc, hgapr, hkr]
  have hcancel : (2 * beta * s) * (2 * 793 * s) ≤
      (r : ℝ) * (2 * 793 * s) := by
    calc
      (2 * beta * s) * (2 * 793 * s) = delta * e := by
        rw [← hbeta, ← hsq]; ring
      _ ≤ _ := hrscale
  have hrlower : 2 * beta * s ≤ (r : ℝ) :=
    (mul_le_mul_iff_left₀ (show (0 : ℝ) < 2 * 793 * s by positivity)).mp hcancel
  have hfour : 4 * e ≤ (4 * (beta ^ 2 * M)) * e := by
    have h := mul_le_mul_of_nonneg_right hbM he.le
    nlinarith only [h]
  have hstride := mul_le_mul_of_nonneg_right hrlower
    (show (0 : ℝ) ≤ 2 * (M : ℝ) * B by positivity)
  have hident : (4 * (beta ^ 2 * M)) * e =
      (2 * beta * s) * (2 * (M : ℝ) * B) := by
    dsimp [B]
    rw [← hsq]
    ring
  have hfinal : v ≤ (2 * (r : ℝ) * M) * B := by
    calc
      v ≤ 4 * e := by linarith
      _ ≤ (4 * (beta ^ 2 * M)) * e := hfour
      _ = (2 * beta * s) * (2 * (M : ℝ) * B) := hident
      _ ≤ (r : ℝ) * (2 * (M : ℝ) * B) := hstride
      _ = (2 * (r : ℝ) * M) * B := by ring
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfinal

end EKG.PartA
