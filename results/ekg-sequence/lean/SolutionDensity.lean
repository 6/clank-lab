import SolutionEndpoint
import SolutionPNT
import EKG.PrimeStructurePermutation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Density consequences for the one-based canonical EKG sequence.

The finite counting argument uses the permutation property and the branches of
canonical smoothing. The analytic argument uses the proved endpoint estimate and
the proved prime number theorem; no corollary specification is imported.
-/

open EKG.CanonicalEndpoint Filter Topology

namespace EKG.Density

lemma a_inj {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (h : a i = a j) : i = j := by
  have h' := EKG.actualA_injective h
  change i - 1 = j - 1 at h'
  omega

lemma a_surj {m : ℕ} (hm : 0 < m) : ∃ n, 1 ≤ n ∧ a n = m := by
  obtain ⟨n, hn, _⟩ := EKG.actualA_positive_occurs_unique hm
  exact ⟨n+1, by omega, by simpa [a, EKG.canonical] using hn⟩

lemma smooth_nonprime {m : ℕ} (hm : ¬ m.Prime) : EKG.CanonicalEndpoint.smoothValue m ≤ m := by
  simp only [EKG.CanonicalEndpoint.smoothValue, hm, false_and, ↓reduceIte]
  split_ifs with h
  · omega
  · rfl

lemma smooth_prime {m : ℕ} (hm : m.Prime) (h2 : m ≠ 2) : EKG.CanonicalEndpoint.smoothValue m = 2*m := by
  exact ite_eq_left ⟨hm, h2⟩

/-- Smoothing eventually lies strictly above the index and within any positive
relative error of it. -/
lemma b_bounds (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ (n : ℝ) < (b n : ℝ) ∧
      (b n : ℝ) ≤ (1+η)*(n : ℝ) := by
  obtain ⟨N, hN, h⟩ := ekg_sharp_all_index (1/6) (by norm_num)
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1/(2*η)))
  filter_upwards [eventually_ge_atTop N, hl] with n hn hln
  have hn3 : 3 ≤ n := hN.trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  obtain ⟨hlo, hhi⟩ := abs_le.mp (h n hn)
  have heq : (n : ℝ)/(3*Real.log (n : ℝ)) = (n : ℝ)/Real.log (n : ℝ)/3 := by ring
  rw [heq] at hlo hhi
  have hq : (0 : ℝ) < (n : ℝ)/Real.log (n : ℝ) := div_pos hnpos hlog
  have hηlog : (1/2 : ℝ) ≤ η * Real.log (n : ℝ) := by
    have := (div_le_iff₀ (by positivity : 0 < 2*η)).mp hln
    dsimp only [Function.comp_apply] at this
    nlinarith
  have hqupper : (n : ℝ)/Real.log (n : ℝ)/2 ≤ η*(n : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  exact ⟨hn3, by linarith, by linarith⟩

/-- Eventually precisely prime values lie below the diagonal, with no equality. -/
lemma classification : ∃ K : ℕ, 3 ≤ K ∧ ∀ n, K ≤ n →
    ((a n < n ↔ (a n).Prime) ∧ (a n ≠ n) ∧
      ((a n).Prime → b n = 2*a n)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (b_bounds (1/2) (by norm_num))
  refine ⟨max 3 K, le_max_left _ _, ?_⟩
  intro n hn
  obtain ⟨hn3, hnb, hbn⟩ := hK n ((le_max_right _ _).trans hn)
  have hprime : (a n).Prime → b n = 2*a n := by
    intro hp
    change EKG.CanonicalEndpoint.smoothValue (a n) = 2*a n
    apply smooth_prime hp
    intro he
    have hb2 : b n = 2 := by simp [b, he, EKG.CanonicalEndpoint.smoothValue]
    rw [hb2] at hnb
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    norm_num at hnb
    linarith
  have hpbelow : (a n).Prime → a n < n := by
    intro hp
    have he : (b n : ℝ) = 2*(a n : ℝ) := by exact_mod_cast hprime hp
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have : (a n : ℝ) < n := by linarith
    exact_mod_cast this
  have hnonabove : ¬ (a n).Prime → n < a n := by
    intro hp
    have he : (b n : ℝ) ≤ a n := by exact_mod_cast (show b n ≤ a n from smooth_nonprime hp)
    exact_mod_cast hnb.trans_le he
  refine ⟨⟨?_, hpbelow⟩, ?_, hprime⟩
  · intro hlt
    by_contra hp
    have := hnonabove hp
    omega
  · by_cases hp : (a n).Prime
    · exact Nat.ne_of_lt (hpbelow hp)
    · exact (Nat.ne_of_lt (hnonabove hp)).symm

noncomputable def below (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun k => a k < k)).card

noncomputable def above (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun k => k < a k)).card

noncomputable def diagonal (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun k => a k = k)).card

/-- Two-sided counting by prime values. The constant absorbs the initial indices
and the largest value appearing among those indices. -/
lemma count_bounds (η : ℝ) (hη : 0 < η) : ∃ C : ℕ,
    ∀ᶠ N : ℕ in atTop,
      Nat.primeCounting ⌊(N : ℝ)/2⌋₊ ≤ below N + C ∧
      below N ≤ Nat.primeCounting ⌊(1+η)*(N : ℝ)/2⌋₊ + C := by
  classical
  obtain ⟨K, hK3, hclass⟩ := classification
  obtain ⟨L, hL⟩ := eventually_atTop.mp (b_bounds η hη)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (b_bounds (1/2) (by norm_num))
  let T := max K (max L J)
  have hTK : K ≤ T := le_max_left _ _
  have hTL : L ≤ T := (le_max_left L J).trans (le_max_right K (max L J))
  have hTJ : J ≤ T := (le_max_right L J).trans (le_max_right K (max L J))
  let M := (Finset.range T).sup a
  refine ⟨M + T, ?_⟩
  filter_upwards [eventually_ge_atTop T] with N hNT
  let D := (Finset.Icc 1 N).filter (fun k => a k < k)
  have hlow : (Nat.primesLE ⌊(N : ℝ)/2⌋₊) ⊆
      (Nat.primesLE M) ∪ D.image a := by
    intro p hp
    obtain ⟨hpN, hpprime⟩ := Nat.mem_primesLE.mp hp
    by_cases hpM : p ≤ M
    · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨hpM, hpprime⟩)
    obtain ⟨n, hn1, hna⟩ := a_surj hpprime.pos
    have hnT : T ≤ n := by
      by_contra hnT
      have ham : a n ≤ M := Finset.le_sup (f := a) (Finset.mem_range.mpr (by omega))
      omega
    have hcl := hclass n (hTK.trans hnT)
    have hb : b n = 2*p := by rw [hcl.2.2 (hna ▸ hpprime), hna]
    have hnb := (hJ n (hTJ.trans hnT)).2.1
    rw [hb] at hnb
    have hpNr : (p : ℝ) ≤ (N : ℝ)/2 :=
      (Nat.le_floor_iff (by positivity : (0:ℝ) ≤ (N:ℝ)/2)).mp hpN
    have hnN : n ≤ N := by
      have : (n : ℝ) < N := by push_cast at hnb; linarith
      exact_mod_cast this.le
    have hnd : n ∈ D := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, hcl.1.mpr (hna ▸ hpprime)⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hnd, hna⟩)
  have hlowcard := (Finset.card_le_card hlow).trans (Finset.card_union_le _ _)
  rw [Nat.primesLE_card_eq_primeCounting] at hlowcard
  have hMcard : (Nat.primesLE M).card ≤ M := by
    rw [Nat.primesLE_eq_filter_Icc_one]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have himage : (D.image a).card ≤ below N := Finset.card_image_le
  have hlower : Nat.primeCounting ⌊(N : ℝ)/2⌋₊ ≤ below N + (M+T) := by omega
  let H := D.filter (fun k => T ≤ k)
  have hmap : Set.MapsTo a H (Nat.primesLE ⌊(1+η)*(N : ℝ)/2⌋₊) := by
    intro n hn
    obtain ⟨hnd, hnT⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hnlt⟩ := Finset.mem_filter.mp hnd
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
    have hp := (hclass n (hTK.trans hnT)).1.mp hnlt
    have hb := (hclass n (hTK.trans hnT)).2.2 hp
    have hbn := (hL n (hTL.trans hnT)).2.2
    apply Nat.mem_primesLE.mpr
    refine ⟨(Nat.le_floor_iff (by positivity : (0:ℝ) ≤ (1+η)*(N:ℝ)/2)).mpr ?_, hp⟩
    have hnNr : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hbr : (b n : ℝ) = 2*(a n : ℝ) := by exact_mod_cast hb
    have := mul_le_mul_of_nonneg_left hnNr (by linarith : 0 ≤ 1+η)
    linarith
  have hHcard : H.card ≤ Nat.primeCounting ⌊(1+η)*(N : ℝ)/2⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card_of_injOn a hmap
    intro i hi j hj hij
    apply a_inj _ _ hij
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1).1
    · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).1
  have hsmall : (D.filter (fun k => ¬ T ≤ k)).card ≤ T := by
    calc
      _ ≤ (Finset.range T).card := Finset.card_le_card (by
        intro n hn
        have := (Finset.mem_filter.mp hn).2
        exact Finset.mem_range.mpr (by omega))
      _ = T := Finset.card_range T
  have hpartition := Finset.card_filter_add_card_filter_not (s := D) (p := fun k => T ≤ k)
  have hupper : below N ≤ Nat.primeCounting ⌊(1+η)*(N : ℝ)/2⌋₊ + (M+T) := by
    change H.card + (D.filter (fun k => ¬ T ≤ k)).card = below N at hpartition
    omega
  exact ⟨hlower, hupper⟩

noncomputable def scale (N : ℕ) : ℝ := (N : ℝ)/(2*Real.log (N : ℝ))

lemma scale_pos {N : ℕ} (hN : 2 ≤ N) : 0 < scale N := by
  apply div_pos
  · exact_mod_cast (show 0 < N by omega)
  · exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))

lemma scale_top : Tendsto scale atTop atTop := by
  have h := (EKG.CanonicalEndpoint.endpoint_logRate_tendsto.comp
    tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num : (0:ℝ)<2)
  convert h using 1
  funext N
  simp only [scale, Function.comp_apply, EKG.logRate, div_div]
  rw [mul_comm]

lemma const_over_scale (c : ℝ) : Tendsto (fun N => c / scale N) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop scale_top

/-- PNT at a fixed positive multiple of the index, normalized by N/(2 log N). -/
lemma prime_scaled (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (Nat.primeCounting ⌊c*(N:ℝ)⌋₊ : ℝ)/scale N)
      atTop (𝓝 (2*c)) := by
  have ht : Tendsto (fun N : ℕ => c*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => Real.log c / Real.log (N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogtop
  have hlog : Tendsto (fun N : ℕ => Real.log (c*(N:ℝ))/Real.log (N:ℝ))
      atTop (𝓝 1) := by
    have h := hconst.add_const 1
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
    have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hln : Real.log (N:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
    rw [Real.log_mul hc.ne' hNpos.ne', add_div, div_self hln]
  have hmodel : Tendsto (fun N : ℕ => (c*(N:ℝ)/Real.log (c*(N:ℝ)))/scale N)
      atTop (𝓝 (2*c)) := by
    have h := (tendsto_const_nhds (x := 2*c)).div hlog (by norm_num : (1:ℝ) ≠ 0)
    have h' : Tendsto (fun N : ℕ => (2*c)/(Real.log (c*(N:ℝ))/Real.log (N:ℝ)))
        atTop (𝓝 (2*c)) := by
      convert h using 1
      simp
    apply h'.congr'
    filter_upwards [eventually_ge_atTop (2:ℕ), ht.eventually (eventually_gt_atTop (1:ℝ))] with N hN hcN
    have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hln : Real.log (N:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
    have hcln : Real.log (c*(N:ℝ)) ≠ 0 := ne_of_gt (Real.log_pos hcN)
    dsimp [scale]
    field_simp
  have hpnt : Tendsto (fun N : ℕ =>
      (Nat.primeCounting ⌊c*(N:ℝ)⌋₊ : ℝ) / (c*(N:ℝ)/Real.log (c*(N:ℝ))))
      atTop (𝓝 1) := by
    apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp (pi_alt'.comp_tendsto ht)
    filter_upwards [ht.eventually (eventually_gt_atTop (1:ℝ))] with N hN
    exact div_ne_zero (by linarith) (ne_of_gt (Real.log_pos hN))
  have h := hpnt.mul hmodel
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [ht.eventually (eventually_gt_atTop (1:ℝ))] with N hN
  have hz : c*(N:ℝ)/Real.log (c*(N:ℝ)) ≠ 0 :=
    div_ne_zero (by linarith) (ne_of_gt (Real.log_pos hN))
  exact div_mul_div_cancel₀ hz

lemma below_limit : Tendsto (fun N : ℕ => (below N : ℝ)/scale N) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨C, hC⟩ := count_bounds 1 (by norm_num)
    have hp : Tendsto (fun N : ℕ =>
        (Nat.primeCounting ⌊(N:ℝ)/2⌋₊ : ℝ)/scale N - (C:ℝ)/scale N) atTop (𝓝 1) := by
      have h := (prime_scaled (1/2) (by norm_num)).sub (const_over_scale C)
      norm_num at h
      simpa only [one_div, inv_mul_eq_div] using h
    filter_upwards [hC, (tendsto_order.mp hp).1 l hl, eventually_ge_atTop (2:ℕ)] with N hN hlN hN2
    have hcast : (Nat.primeCounting ⌊(N:ℝ)/2⌋₊ : ℝ) ≤ (below N:ℝ)+(C:ℝ) := by
      exact_mod_cast hN.1
    have hdiv := (div_le_div_of_nonneg_right hcast (scale_pos hN2).le)
    rw [add_div] at hdiv
    linarith
  · intro u hu
    let η := (u-1)/2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨C, hC⟩ := count_bounds η hη
    have hp : Tendsto (fun N : ℕ =>
        (Nat.primeCounting ⌊(1+η)*(N:ℝ)/2⌋₊ : ℝ)/scale N + (C:ℝ)/scale N)
        atTop (𝓝 (1+η)) := by
      have h := (prime_scaled ((1+η)/2) (by positivity)).add (const_over_scale C)
      have he : 2*((1+η)/2)+(0:ℝ) = 1+η := by ring
      rw [he] at h
      simpa only [div_mul_eq_mul_div] using h
    have hηu : 1+η < u := by dsimp [η]; linarith
    filter_upwards [hC, (tendsto_order.mp hp).2 u hηu, eventually_ge_atTop (2:ℕ)] with N hN huN hN2
    have hcast : (below N:ℝ) ≤ (Nat.primeCounting ⌊(1+η)*(N:ℝ)/2⌋₊ : ℝ)+(C:ℝ) := by
      exact_mod_cast hN.2
    have hdiv := (div_le_div_of_nonneg_right hcast (scale_pos hN2).le)
    rw [add_div] at hdiv
    linarith

lemma diagonal_bounded : ∃ C : ℕ, ∀ N, diagonal N ≤ C := by
  classical
  obtain ⟨K, _, hK⟩ := classification
  refine ⟨K, ?_⟩
  intro N
  calc
    _ ≤ (Finset.range K).card := Finset.card_le_card (by
      intro n hn
      obtain ⟨_, he⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_range.mpr (by
        by_contra h
        exact (hK n (by omega)).2.1 he))
    _ = K := Finset.card_range K

lemma partition_count (N : ℕ) : above N + below N + diagonal N = N := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 N) (p := fun k => k < a k)
  have hs : ((Finset.Icc 1 N).filter (fun k => ¬ k < a k)) =
      ((Finset.Icc 1 N).filter (fun k => a k < k)) ∪
      ((Finset.Icc 1 N).filter (fun k => a k = k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hk, hle⟩
      rcases lt_or_eq_of_le (Nat.le_of_not_gt hle) with hl | he
      · exact Or.inl ⟨hk, hl⟩
      · exact Or.inr ⟨hk, he⟩
    · rintro (⟨hk, hl⟩ | ⟨hk, he⟩)
      · exact ⟨hk, by omega⟩
      · exact ⟨hk, by omega⟩
  rw [hs, Finset.card_union_of_disjoint] at h
  · simpa [above, below, diagonal, Nat.add_assoc] using h
  · apply Finset.disjoint_left.mpr
    intro k hk hl
    have := (Finset.mem_filter.mp hk).2
    have := (Finset.mem_filter.mp hl).2
    omega

lemma scale_over_N : Tendsto (fun N : ℕ => scale N / (N:ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (1:ℝ)/(2*Real.log (N:ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  dsimp [scale]
  field_simp

lemma below_density_zero : Tendsto (fun N : ℕ => (below N:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
  have h := below_limit.mul scale_over_N
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  exact div_mul_div_cancel₀ (scale_pos hN).ne'

lemma diagonal_density_zero : Tendsto (fun N : ℕ => (diagonal N:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := diagonal_bounded
  apply squeeze_zero (g := fun N : ℕ => (C:ℝ)/(N:ℝ)) (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun N => div_le_div_of_nonneg_right (by exact_mod_cast hC N) (Nat.cast_nonneg _))
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

lemma above_limit : Tendsto (fun N : ℕ => (above N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1:ℝ))).sub below_density_zero).sub diagonal_density_zero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hp : (above N:ℝ)+(below N:ℝ)+(diagonal N:ℝ) = (N:ℝ) := by
    exact_mod_cast partition_count N
  apply (eq_div_iff hn).mpr
  field_simp
  linarith

end EKG.Density

theorem ekg_below_diagonal_count :
    Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun k => a k < k)).card : ℕ) : ℝ) /
        ((N : ℝ) / (2 * Real.log (N : ℝ))))
    atTop (𝓝 1) := EKG.Density.below_limit

theorem ekg_ordowski_density :
    Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun k => k < a k)).card : ℕ) : ℝ) / (N : ℝ))
    atTop (𝓝 1) := EKG.Density.above_limit

