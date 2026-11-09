import ABC.S4.R3AuxAlg
import ABC.S4.R3AuxT
import ABC.S4.R3AuxSh

/-! R3 auxiliaries: assembly of the normal form (four cubic and five quartic shears). -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R3Aux

open ABC.S4

/-! ### `O(‖w‖^k)` bounds -/

theorem Bound.mono_r {F : C2 → ℂ → ℂ} {r r' s C : ℝ} {k : ℕ} (h : Bound F r s C k)
    (hr : r' ≤ r) : Bound F r' s C k :=
  fun w hw t ht => h w (show ‖w‖ < r from lt_of_lt_of_le hw hr) t ht

theorem Bound.congr {F G : C2 → ℂ → ℂ} {r s C : ℝ} {k : ℕ} (h : Bound F r s C k)
    (he : ∀ w ∈ polydisc r, ∀ t ∈ strip s, F w t = G w t) : Bound G r s C k :=
  fun w hw t ht => (he w hw t ht) ▸ h w hw t ht

theorem Bound.add {F G : C2 → ℂ → ℂ} {r s C D : ℝ} {k : ℕ} (hF : Bound F r s C k)
    (hG : Bound G r s D k) : Bound (fun w t => F w t + G w t) r s (C + D) k :=
  fun w hw t ht => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add (hF w hw t ht) (hG w hw t ht))

theorem Bound.lower {F : C2 → ℂ → ℂ} {r s C : ℝ} {j k : ℕ} (h : Bound F r s C k)
    (hr1 : r ≤ 1) (hjk : j ≤ k) : Bound F r s (max C 0) j := by
  intro w hw t ht
  have hw1 : ‖w‖ ≤ 1 := le_trans (le_of_lt hw) hr1
  calc ‖F w t‖ ≤ C * ‖w‖ ^ k := h w hw t ht
    _ ≤ max C 0 * ‖w‖ ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ‖w‖ ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) hw1 hjk) (le_max_right _ _)

theorem norm_lin_le {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2) (w : C2) :
    ‖lin u w‖ ≤ 4 * ‖w‖ := by
  have h0 := norm_le_pi_norm w 0
  have h1 := norm_le_pi_norm w 1
  unfold lin
  calc ‖(u 0 : ℂ) * w 0 + (u 1 : ℂ) * w 1‖ ≤ |u 0| * ‖w 0‖ + |u 1| * ‖w 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ 2 * ‖w‖ + 2 * ‖w‖ := by gcongr
    _ = 4 * ‖w‖ := by ring

theorem norm_rot_le {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2) (w : C2) :
    ‖w 0 * u 1 - w 1 * u 0‖ ≤ 4 * ‖w‖ := by
  have h0 := norm_le_pi_norm w 0
  have h1 := norm_le_pi_norm w 1
  calc ‖w 0 * u 1 - w 1 * u 0‖ ≤ ‖w 0‖ * |u 1| + ‖w 1‖ * |u 0| := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ ‖w‖ * 2 + ‖w‖ * 2 := by gcongr
    _ = 4 * ‖w‖ := by ring

theorem shX_bound {k : ℕ} (hk : 1 ≤ k) {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2)
    {c : ℂ → ℂ} {ν s B r : ℝ} (hcB : ∀ t ∈ strip s, ‖c t‖ ≤ B ∧ ‖deriv c t‖ ≤ B) :
    Bound (shX k u c ν) r s ((|ν| * k * B + B) * 4 ^ k) k := by
  intro w _ t ht
  obtain ⟨hc, hd⟩ := hcB t ht
  have hB : 0 ≤ B := (norm_nonneg _).trans hc
  have hl := norm_lin_le hu0 hu1 w
  have hr := norm_rot_le hu0 hu1 w
  have hk' : k = (k - 1) + 1 := by omega
  unfold shX
  calc ‖(ν : ℂ) * k * c t * lin u w ^ (k - 1) * (w 0 * u 1 - w 1 * u 0) - deriv c t * lin u w ^ k‖
      ≤ |ν| * k * B * (4 * ‖w‖) ^ (k - 1) * (4 * ‖w‖) + B * (4 * ‖w‖) ^ k := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
            Complex.norm_natCast, Real.norm_eq_abs]
          gcongr
        · rw [norm_mul, norm_pow]
          gcongr
    _ = (|ν| * k * B + B) * 4 ^ k * ‖w‖ ^ k := by
        conv_rhs => rw [hk']
        conv_lhs => rw [hk']
        simp only [Nat.add_sub_cancel]
        ring

theorem norm_C2_mk_le (x y : ℝ) : ‖(![(x : ℂ), (y : ℂ)] : C2)‖ ≤ max |x| |y| := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg x))).2 fun i => ?_
  fin_cases i <;> simp

theorem norm_C2_mk_lt {x y r : ℝ} (hx : |x| < r) (hy : |y| < r) :
    (![(x : ℂ), (y : ℂ)] : C2) ∈ polydisc r :=
  lt_of_le_of_lt (norm_C2_mk_le x y) (max_lt hx hy)

theorem poly4_expand (b : ℕ → ℕ → ℂ) (w : C2) :
    poly4 b w = b 0 0 + b 0 1 * w 1 + b 1 0 * w 0 + b 0 2 * w 1 ^ 2 + b 1 1 * w 0 * w 1 +
      b 2 0 * w 0 ^ 2 + (b 3 0 * w 0 ^ 3 + b 2 1 * w 0 ^ 2 * w 1 + b 1 2 * w 0 * w 1 ^ 2 +
      b 0 3 * w 1 ^ 3) + (b 4 0 * w 0 ^ 4 + b 3 1 * w 0 ^ 3 * w 1 + b 2 2 * w 0 ^ 2 * w 1 ^ 2 +
      b 1 3 * w 0 * w 1 ^ 3 + b 0 4 * w 1 ^ 4) := by
  simp [poly4, Finset.sum_range_succ]
  ring

/-! ### Conjugacies and Hamiltonians on smaller polydiscs -/

theorem IsConj.id' {K : C2 → ℂ → ℂ} {r R s : ℝ} (hr : r ≤ R) :
    IsConj K K (fun _ w => w) r R s where
  holo := differentiableOn_snd
  maps := fun _ _ _ hw => lt_of_lt_of_le hw hr
  real := fun x _ _ => ⟨x, rfl⟩
  per := fun _ _ => rfl
  zero := fun _ => rfl
  lin := fun _ => hasFDerivAt_id 0
  sol := fun _ _ _ h _ => h

theorem IsConj.mono_r {K' K : C2 → ℂ → ℂ} {Ψ : ℂ → C2 → C2} {r r' R s : ℝ}
    (h : IsConj K' K Ψ r R s) (hr : r' ≤ r) : IsConj K' K Ψ r' R s where
  holo := h.holo.mono (prod_mono subset_rfl fun w (hw : ‖w‖ < r') => lt_of_lt_of_le hw hr)
  maps := fun t ht w (hw : ‖w‖ < r') => h.maps t ht w (lt_of_lt_of_le hw hr)
  real := fun x t hx => h.real x t (lt_of_lt_of_le hx hr)
  per := h.per
  zero := h.zero
  lin := h.lin
  sol := fun γ a b hγ hin => h.sol γ a b hγ fun t ht => lt_of_lt_of_le (hin t ht) hr

theorem IsTPHam.mono_r {K : C2 → ℂ → ℂ} {r r' s : ℝ} (h : IsTPHam K r s) (hr : r' ≤ r) :
    IsTPHam K r' s where
  holo := h.holo.mono (prod_mono (fun w (hw : ‖w‖ < r') => lt_of_lt_of_le hw hr) subset_rfl)
  real := fun x t hx => h.real x t (lt_of_lt_of_le hx hr)
  per := h.per

/-! ### The shear chain -/

/-- after some shears: `K` on `polydisc r`, conjugated to `H` by `Ψ`, with
`K = ν/2 q₂ + T + O(‖w‖^(k+1))` and `K = ν/2 q₂ + O(‖w‖³)` -/
structure Inv (H : C2 → ℂ → ℂ) (ρ s ν : ℝ) (k : ℕ) (K : C2 → ℂ → ℂ) (r : ℝ) (Ψ : ℂ → C2 → C2)
    (T : C2 → ℂ → ℂ) : Prop where
  pos : 0 < r
  le1 : r ≤ 1
  ham : IsTPHam K r s
  cj : IsConj K H Ψ r ρ s
  cubic : ∃ A, Bound (fun w t => K w t - ν / 2 * q2 w) r s A 3
  rest : ∃ E, Bound (fun w t => K w t - ν / 2 * q2 w - T w t) r s E (k + 1)

theorem chain_step {H : C2 → ℂ → ℂ} {ρ s ν : ℝ} {k : ℕ} (hk : 3 ≤ k) (hs : 0 < s)
    {K : C2 → ℂ → ℂ} {r : ℝ} {Ψ : ℂ → C2 → C2} {T : C2 → ℂ → ℂ}
    (hI : Inv H ρ s ν k K r Ψ T) {u : Fin 2 → ℝ} (hu0 : |u 0| ≤ 2) (hu1 : |u 1| ≤ 2)
    {c : ℂ → ℂ} (hc : CoefFn c s) (hcd : DHolPer c s) :
    ∃ r', Inv H ρ s ν k (shearK k u c K) r' (fun t w => Ψ t (shear k u c t w))
      (fun w t => T w t + shX k u c ν w t) := by
  obtain ⟨hr, hr1, hK, hΨ, ⟨A, hA⟩, ⟨E, hE⟩⟩ := hI
  obtain ⟨B1, hB1⟩ := hc.bdd
  obtain ⟨B2, hB2⟩ := hcd.dbdd
  have hcB : ∀ t ∈ strip s, ‖c t‖ ≤ max B1 B2 ∧ ‖deriv c t‖ ≤ max B1 B2 := fun t ht =>
    ⟨(hB1 t ht).trans (le_max_left _ _), (hB2 t ht).trans (le_max_right _ _)⟩
  obtain ⟨r', hr', hr'r, hK', hconj, C, hC⟩ :=
    shear_step hk hu0 hu1 hr hr1 hs hc hcB hK hA
  have hr'1 : r' ≤ 1 := hr'r.trans hr1
  have hX := shX_bound (k := k) (ν := ν) (r := r') (by omega) hu0 hu1 hcB
  refine ⟨r', hr', hr'1, hK', hΨ.comp hconj hs, ?_, ?_⟩
  · refine ⟨_, Bound.congr (Bound.add (Bound.add (Bound.lower hC hr'1 (by omega : 3 ≤ k + 1))
      (Bound.lower (Bound.mono_r hA hr'r) hr'1 le_rfl)) (Bound.lower hX hr'1 hk)) ?_⟩
    intro w _ t _
    ring
  · refine ⟨_, Bound.congr (Bound.add hC (Bound.mono_r hE hr'r)) ?_⟩
    intro w _ t _
    ring

/-! ### Extracting the cubic or quartic part -/

theorem norm_add4_le (x1 x2 x3 x4 : ℂ) : ‖x1 + x2 + x3 + x4‖ ≤ ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ :=
  (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)

theorem norm_add5_le (x1 x2 x3 x4 x5 : ℂ) :
    ‖x1 + x2 + x3 + x4 + x5‖ ≤ ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ + ‖x5‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_add4_le _ _ _ _) le_rfl)

theorem mono_term_le {c : ℂ} {B : ℝ} (hc : ‖c‖ ≤ B) (w : C2) {m n k : ℕ} (hmn : m + n = k) :
    ‖c * w 0 ^ m * w 1 ^ n‖ ≤ B * ‖w‖ ^ k := by
  have h0 := norm_le_pi_norm w 0
  have h1 := norm_le_pi_norm w 1
  calc ‖c * w 0 ^ m * w 1 ^ n‖ = ‖c‖ * (‖w 0‖ ^ m * ‖w 1‖ ^ n) := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, mul_assoc]
    _ ≤ B * (‖w‖ ^ m * ‖w‖ ^ n) :=
        mul_le_mul hc (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h0 m)
          (pow_le_pow_left₀ (norm_nonneg _) h1 n) (by positivity) (by positivity))
          (by positivity) ((norm_nonneg _).trans hc)
    _ = B * ‖w‖ ^ k := by rw [← pow_add, hmn]

theorem Q4_bound {a : ℕ → ℕ → ℂ → ℂ} {s r : ℝ} (ha : ∀ m n, HolPer (a m n) s) :
    ∃ D, Bound (Q4 a) r s D 4 := by
  have := fun m n => (ha m n).bdd
  choose B hB using this
  refine ⟨B 4 0 + B 3 1 + B 2 2 + B 1 3 + B 0 4, fun w _ t ht => ?_⟩
  have hQ : Q4 a w t = a 4 0 t * w 0 ^ 4 * w 1 ^ 0 + a 3 1 t * w 0 ^ 3 * w 1 ^ 1 +
      a 2 2 t * w 0 ^ 2 * w 1 ^ 2 + a 1 3 t * w 0 ^ 1 * w 1 ^ 3 + a 0 4 t * w 0 ^ 0 * w 1 ^ 4 := by
    simp [Q4]
  rw [hQ]
  refine (norm_add5_le _ _ _ _ _).trans ?_
  have := add_le_add (add_le_add (add_le_add (add_le_add
    (mono_term_le (hB 4 0 t ht) w (rfl : 4 + 0 = 4)) (mono_term_le (hB 3 1 t ht) w (rfl : 3 + 1 = 4)))
    (mono_term_le (hB 2 2 t ht) w (rfl : 2 + 2 = 4))) (mono_term_le (hB 1 3 t ht) w (rfl : 1 + 3 = 4)))
    (mono_term_le (hB 0 4 t ht) w (rfl : 0 + 4 = 4))
  exact this.trans_eq (by ring)

theorem extract_stage {G : C2 → ℂ → ℂ} {R s A : ℝ} {j : ℕ} (hj : j ≤ 5) (hR : 0 < R)
    (hR1 : R ≤ 1) (hs : 0 < s) (hG : IsTPHam G R s) (hb : Bound G R s A j) :
    ∃ a : ℕ → ℕ → ℂ → ℂ, (∀ m n, CoefFn (a m n) s) ∧ ∃ r > 0, r ≤ R ∧
      (∃ E, Bound (fun w t => G w t - poly4 (fun m n => a m n t) w) r s E 5) ∧
      ∀ t ∈ strip s, ∀ m n, m + n < j → m + n ≤ 4 → a m n t = 0 := by
  have hM : ∀ w ∈ polydisc R, ∀ t ∈ strip s, ‖G w t‖ ≤ max A 0 := by
    intro w hw t ht
    have hw1 : ‖w‖ ≤ 1 := le_trans (le_of_lt hw) hR1
    calc ‖G w t‖ ≤ max A 0 * ‖w‖ ^ j := Bound.lower hb hR1 le_rfl w hw t ht
      _ ≤ max A 0 * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hw1) (le_max_right _ _)
      _ = max A 0 := mul_one _
  obtain ⟨a, ha, r₀, hr₀, C₀, hC₀⟩ := extract hR hs hG hM
  refine ⟨a, ha, min r₀ R, lt_min hr₀ hR, min_le_right _ _,
    ⟨C₀, Bound.mono_r hC₀ (min_le_left _ _)⟩, fun t ht => ?_⟩
  have hr1 : min r₀ R ≤ 1 := (min_le_right _ _).trans hR1
  have hb' := Bound.lower (Bound.mono_r hb (min_le_right r₀ R)) hr1 (le_refl j)
  have hC' := Bound.lower (Bound.mono_r hC₀ (min_le_left r₀ R)) hr1 hj
  refine poly4_vanish (C := max A 0 + max C₀ 0) (lt_min hr₀ hR) fun x y hx hy => ?_
  have hw := norm_C2_mk_lt hx hy
  set w : C2 := ![(x : ℂ), (y : ℂ)]
  have e : poly4 (fun m n => a m n t) w = G w t - (G w t - poly4 (fun m n => a m n t) w) := by
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := hb' w hw t ht
  have h2 := hC' w hw t ht
  have h3 : ‖w‖ ^ j ≤ max |x| |y| ^ j := pow_le_pow_left₀ (norm_nonneg _) (norm_C2_mk_le x y) j
  calc ‖G w t‖ + ‖G w t - poly4 (fun m n => a m n t) w‖
      ≤ max A 0 * ‖w‖ ^ j + max C₀ 0 * ‖w‖ ^ j := add_le_add h1 h2
    _ = (max A 0 + max C₀ 0) * ‖w‖ ^ j := by ring
    _ ≤ (max A 0 + max C₀ 0) * max |x| |y| ^ j :=
      mul_le_mul_of_nonneg_left h3 (add_nonneg (le_max_right _ _) (le_max_right _ _))

theorem stage3 {G : C2 → ℂ → ℂ} {R s A : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hs : 0 < s)
    (hG : IsTPHam G R s) (hb : Bound G R s A 3) :
    ∃ a : ℕ → ℕ → ℂ → ℂ, (∀ m n, CoefFn (a m n) s) ∧ ∃ r > 0, r ≤ R ∧
      ∃ E, Bound (fun w t => G w t - P3 a w t) r s E 4 := by
  obtain ⟨a, ha, r, hr, hrR, ⟨E, hE⟩, hv⟩ := extract_stage (by norm_num) hR hR1 hs hG hb
  obtain ⟨D, hD⟩ := Q4_bound (r := r) fun m n => (ha m n).toHolPer
  refine ⟨a, ha, r, hr, hrR, _, Bound.congr (Bound.add
    (Bound.lower hE (hrR.trans hR1) (by norm_num : 4 ≤ 5)) hD) fun w _ t ht => ?_⟩
  rw [poly4_expand]
  simp only [hv t ht 0 0 (by norm_num) (by norm_num), hv t ht 0 1 (by norm_num) (by norm_num),
    hv t ht 1 0 (by norm_num) (by norm_num), hv t ht 0 2 (by norm_num) (by norm_num),
    hv t ht 1 1 (by norm_num) (by norm_num), hv t ht 2 0 (by norm_num) (by norm_num), P3, Q4]
  ring

theorem stage4 {G : C2 → ℂ → ℂ} {R s A : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (hs : 0 < s)
    (hG : IsTPHam G R s) (hb : Bound G R s A 4) :
    ∃ a : ℕ → ℕ → ℂ → ℂ, (∀ m n, CoefFn (a m n) s) ∧ ∃ r > 0, r ≤ R ∧
      ∃ E, Bound (fun w t => G w t - Q4 a w t) r s E 5 := by
  obtain ⟨a, ha, r, hr, hrR, ⟨E, hE⟩, hv⟩ := extract_stage (by norm_num) hR hR1 hs hG hb
  refine ⟨a, ha, r, hr, hrR, _, Bound.congr hE fun w _ t ht => ?_⟩
  rw [poly4_expand]
  simp only [hv t ht 0 0 (by norm_num) (by norm_num), hv t ht 0 1 (by norm_num) (by norm_num),
    hv t ht 1 0 (by norm_num) (by norm_num), hv t ht 0 2 (by norm_num) (by norm_num),
    hv t ht 1 1 (by norm_num) (by norm_num), hv t ht 2 0 (by norm_num) (by norm_num),
    hv t ht 3 0 (by norm_num) (by norm_num), hv t ht 2 1 (by norm_num) (by norm_num),
    hv t ht 1 2 (by norm_num) (by norm_num), hv t ht 0 3 (by norm_num) (by norm_num), Q4]
  ring

/-- subtracting `ν/2 q₂` keeps a time-periodic Hamiltonian -/
theorem IsTPHam.sub_quad {K : C2 → ℂ → ℂ} {r s : ℝ} (ν : ℝ) (hK : IsTPHam K r s) :
    IsTPHam (fun w t => K w t - ν / 2 * q2 w) r s where
  holo := by
    refine hK.holo.sub ?_
    have : Differentiable ℂ (fun q : C2 × ℂ => (ν : ℂ) / 2 * q2 q.1) := by
      unfold q2; fun_prop
    exact this.differentiableOn
  real := fun x t hx => by
    have e : (ν : ℂ) / 2 * q2 (ofR x) = ((ν / 2 * (x 0 ^ 2 + x 1 ^ 2) : ℝ) : ℂ) := by
      simp [q2, ofR]
    rw [e, Complex.sub_im, hK.real x t hx, Complex.ofReal_im, sub_zero]
  per := fun w t => by rw [hK.per]

theorem abs_u_le {u : Fin 2 → ℝ} (h : u = ![1, 0] ∨ u = ![0, 1] ∨ u = ![1, 1] ∨ u = ![1, -1] ∨
    u = ![1, 2]) : |u 0| ≤ 2 ∧ |u 1| ≤ 2 := by
  rcases h with h | h | h | h | h <;> subst h <;> norm_num

/-! ### The normal form -/

theorem R3_main {H₂ : C2 → ℂ → ℂ} {ρ s ν C : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hH : IsTPHam H₂ ρ s)
    (hq : Bound (fun w t => H₂ w t - ν / 2 * (w 0 ^ 2 + w 1 ^ 2)) ρ s C 3) (hnr : NonRes4 ν) :
    ∃ (ρ' s' C' b : ℝ) (R : C2 → ℂ → ℂ) (Ψ : ℂ → C2 → C2), 0 < ρ' ∧ 0 < s' ∧
      IsTPHam (Kbnf ν b R) ρ' s' ∧ Bound R ρ' s' C' 5 ∧
      DifferentiableOn ℂ (fun q : ℂ × C2 => Ψ q.1 q.2) (strip s' ×ˢ polydisc ρ') ∧
      (∀ x : E 2, ‖ofR x‖ < ρ' → ∀ i, (Ψ 0 (ofR x) i).im = 0) ∧
      (∀ t w, Ψ (t + 2 * π) w = Ψ t w) ∧ (∀ t, Ψ t 0 = 0) ∧
      (∀ t, fderiv ℂ (Ψ t) 0 = ContinuousLinearMap.id ℂ C2) ∧
      ∀ γ (t₀ t₁ : ℝ), Solves (Kbnf ν b R) γ t₀ t₁ → (∀ t ∈ Icc t₀ t₁, γ t ∈ polydisc ρ') →
        Solves H₂ (fun t => Ψ t (γ t)) t₀ t₁ := by
  -- the cubic part of `H₂`
  have hR0 : 0 < min ρ 1 := lt_min hρ one_pos
  have hq' : Bound (fun w t => H₂ w t - ν / 2 * q2 w) (min ρ 1) s C 3 :=
    Bound.mono_r hq (min_le_left _ _)
  obtain ⟨a, ha, r₀, hr₀, hr₀R, E₀, hE₀⟩ :=
    stage3 hR0 (min_le_right _ _) hs (IsTPHam.sub_quad ν (IsTPHam.mono_r hH (min_le_left _ _))) hq'
  have hr₀ρ : r₀ ≤ ρ := hr₀R.trans (min_le_left _ _)
  have hr₀1 : r₀ ≤ 1 := hr₀R.trans (min_le_right _ _)
  have I0 : Inv H₂ ρ s ν 3 H₂ r₀ (fun _ w => w) (P3 a) :=
    ⟨hr₀, hr₀1, IsTPHam.mono_r hH hr₀ρ, IsConj.id' hr₀ρ, ⟨C, Bound.mono_r hq' hr₀R⟩,
      ⟨E₀, Bound.congr hE₀ fun w _ t _ => by ring⟩⟩
  -- four cubic shears
  obtain ⟨⟨c0C, c0D⟩, ⟨c1C, c1D⟩, ⟨c2C, c2D⟩, ⟨c3C, c3D⟩⟩ := cc_coef hs hnr ha
  have u0 := abs_u_le (u := uc0) (by simp [uc0])
  have u1 := abs_u_le (u := uc1) (by simp [uc1])
  have u2 := abs_u_le (u := uc2) (by simp [uc2])
  have u3 := abs_u_le (u := uc3) (by simp [uc3])
  have u4 := abs_u_le (u := uq4) (by simp [uq4])
  obtain ⟨r₁, I1⟩ := chain_step le_rfl hs I0 u0.1 u0.2 c0C c0D
  obtain ⟨r₂, I2⟩ := chain_step le_rfl hs I1 u1.1 u1.2 c1C c1D
  obtain ⟨r₃, I3⟩ := chain_step le_rfl hs I2 u2.1 u2.2 c2C c2D
  obtain ⟨r₄, I4⟩ := chain_step le_rfl hs I3 u3.1 u3.2 c3C c3D
  generalize hK4 : shearK 3 uc3 (cc3 ν a) (shearK 3 uc2 (cc2 ν a) (shearK 3 uc1 (cc1 ν a)
    (shearK 3 uc0 (cc0 ν a) H₂))) = K₄ at I4
  obtain ⟨hr₄, hr₄1, hK₄, hΨ₄, -, E₄, hE₄⟩ := I4
  -- `K₄ = ν/2 q₂ + O(‖w‖⁴)`
  have hb₄ : Bound (fun w t => K₄ w t - ν / 2 * q2 w) r₄ s E₄ 4 := by
    refine Bound.congr hE₄ fun w _ t ht => ?_
    have := cubic_ident hs hnr (fun m n => (ha m n).toHolPer) ht w
    linear_combination -this
  -- the quartic part of `K₄`
  obtain ⟨a', ha', r₅, hr₅, hr₅R, E₅, hE₅⟩ := stage4 hr₄ hr₄1 hs (IsTPHam.sub_quad ν hK₄) hb₄
  have hr₅1 : r₅ ≤ 1 := hr₅R.trans hr₄1
  have I5 : Inv H₂ ρ s ν 4 K₄ r₅ _ (Q4 a') :=
    ⟨hr₅, hr₅1, IsTPHam.mono_r hK₄ hr₅R, hΨ₄.mono_r hr₅R,
      ⟨_, Bound.lower (Bound.mono_r hb₄ hr₅R) hr₅1 (by norm_num : 3 ≤ 4)⟩,
      ⟨E₅, Bound.congr hE₅ fun w _ t _ => by ring⟩⟩
  -- five quartic shears
  obtain ⟨⟨d0C, d0D⟩, ⟨d1C, d1D⟩, ⟨d2C, d2D⟩, ⟨d3C, d3D⟩, ⟨d4C, d4D⟩⟩ := cq_coef hs hnr ha'
  obtain ⟨r₆, I6⟩ := chain_step (by norm_num) hs I5 u0.1 u0.2 d0C d0D
  obtain ⟨r₇, I7⟩ := chain_step (by norm_num) hs I6 u1.1 u1.2 d1C d1D
  obtain ⟨r₈, I8⟩ := chain_step (by norm_num) hs I7 u2.1 u2.2 d2C d2D
  obtain ⟨r₉, I9⟩ := chain_step (by norm_num) hs I8 u3.1 u3.2 d3C d3D
  obtain ⟨r₁₀, I10⟩ := chain_step (by norm_num) hs I9 u4.1 u4.2 d4C d4D
  generalize hK : shearK 4 uq4 (cq4 ν a') (shearK 4 uc3 (cq3 ν a') (shearK 4 uc2 (cq2 ν a')
    (shearK 4 uc1 (cq1 ν a') (shearK 4 uc0 (cq0 ν a') K₄)))) = K at I10
  obtain ⟨hr, -, hK', hΨ, -, E, hE⟩ := I10
  -- the twist coefficient and the remainder
  set b : ℝ := 4 * (avg (pq2 a')).re with hb_def
  have hb4 : (b : ℂ) / 4 = avg (pq2 a') := by
    have h := avg_pq2_real ha'
    rw [hb_def]
    push_cast
    rw [mul_div_cancel_left₀ _ (by norm_num : (4 : ℂ) ≠ 0)]
    exact Complex.ext rfl (by simp [h])
  set R : C2 → ℂ → ℂ := fun w t => K w t - ν / 2 * (w 0 ^ 2 + w 1 ^ 2) -
    b / 4 * (w 0 ^ 2 + w 1 ^ 2) ^ 2 with hR_def
  have hKR : Kbnf ν b R = K := by
    funext w t
    simp only [Kbnf, hR_def]
    ring
  refine ⟨r₁₀, s, E, b, R, _, hr, hs, hKR ▸ hK', ?_, hΨ.holo, ?_, hΨ.per, hΨ.zero,
    fun t => (hΨ.lin t).fderiv, fun γ a₁ b₁ hγ hin => hΨ.sol γ a₁ b₁ (hKR ▸ hγ) hin⟩
  · refine Bound.congr hE fun w _ t ht => ?_
    have := quartic_ident hs hnr (fun m n => (ha' m n).toHolPer) ht w
    simp only [hR_def, q2] at this ⊢
    rw [hb4]
    linear_combination -this
  · intro x hx i
    obtain ⟨y, hy⟩ := hΨ.real x 0 hx
    rw [Complex.ofReal_zero] at hy
    rw [hy]
    simp [ofR]

end ABC.S4.R3Aux
