import StanleySnf.Core

/-!
# Lemma B: the lattice spanned by the `η_μ`

`u_r(i) = ∑_μ W r μ * η_μ(i)`.
-/

open Polynomial

namespace StanleySnf

namespace LB

/-- `H_s` over an arbitrary commutative ring. -/
noncomputable def HMR (R : Type*) [CommRing R] (s : Multiset ℕ) : R[X] :=
  (s.map fun m => ((1 : R[X]) + X) ^ m - 1).prod

theorem HM_eq (s : Multiset ℕ) : HM s = HMR ℤ s := rfl

theorem HMR_map (s : Multiset ℕ) : (HMR ℤ s).map (Int.castRingHom (ZMod 2)) = HMR (ZMod 2) s := by
  induction s using Multiset.induction_on with
  | empty => simp [HMR]
  | cons a s ih =>
    simp only [HMR, Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul] at ih ⊢
    rw [ih]; simp

theorem natDegree_gen_le (R : Type*) [CommRing R] (m : ℕ) :
    (((1 : R[X]) + X) ^ m - 1).natDegree ≤ m := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine (natDegree_pow_le).trans ?_
  have : ((1 : R[X]) + X).natDegree ≤ 1 := by
    rw [add_comm]; exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
  calc m * ((1 : R[X]) + X).natDegree ≤ m * 1 := Nat.mul_le_mul_left _ this
    _ = m := mul_one m

theorem natDegree_HMR_le (R : Type*) [CommRing R] (s : Multiset ℕ) :
    (HMR R s).natDegree ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [HMR]
  | cons a s ih =>
    simp only [HMR, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons] at ih ⊢
    exact (natDegree_mul_le).trans (Nat.add_le_add (natDegree_gen_le R a) ih)

/-- `(1+X)^m - 1 = X * g_m` with `g_m(0) = m`. -/
theorem gen_eq (m : ℕ) :
    ((1 : ℤ[X]) + X) ^ m - 1 = X * ∑ j ∈ Finset.range m, ((1 : ℤ[X]) + X) ^ j := by
  have := geom_sum_mul ((1 : ℤ[X]) + X) m
  rw [← this]; ring

theorem HM_factor (s : Multiset ℕ) :
    HM s = X ^ Multiset.card s *
      (s.map fun m => ∑ j ∈ Finset.range m, ((1 : ℤ[X]) + X) ^ j).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [HM]
  | cons a s ih =>
    have h : HM (a ::ₘ s) = (((1 : ℤ[X]) + X) ^ a - 1) * HM s := by
      simp [HM]
    rw [h, ih, gen_eq]
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ]
    ring

theorem HM_coeff_lt (s : Multiset ℕ) {k : ℕ} (hk : k < Multiset.card s) : (HM s).coeff k = 0 := by
  rw [HM_factor, coeff_X_pow_mul', if_neg (by omega)]

theorem HM_coeff_card (s : Multiset ℕ) : (HM s).coeff (Multiset.card s) = (s.prod : ℤ) := by
  rw [HM_factor, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero,
    eval_multiset_prod]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, ih, Multiset.prod_cons]
    simp [eval_finsetSum]


/-! ## The mod-2 transform `T_m f = (1+y)^m f(y/(1+y))`

Over `ZMod 2` it is `(reflect m (f.comp (X+1))).comp (X+1)`. -/

/-- `T_m` over `ZMod 2`. -/
noncomputable def T (m : ℕ) (f : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (reflect m (f.comp (X + 1))).comp (X + 1)

theorem two_eq_zero2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero

theorem X_add_one_add_one : (X + 1 + 1 : (ZMod 2)[X]) = X := by
  rw [add_assoc, one_add_one_eq_two, two_eq_zero2, add_zero]

theorem natDegree_X_add_one_le : (X + 1 : (ZMod 2)[X]).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))

theorem natDegree_comp_le' {f : (ZMod 2)[X]} {a : ℕ} (hf : f.natDegree ≤ a) :
    (f.comp (X + 1)).natDegree ≤ a := by
  refine natDegree_comp_le.trans ?_
  calc f.natDegree * (X + 1 : (ZMod 2)[X]).natDegree ≤ a * 1 :=
        Nat.mul_le_mul hf natDegree_X_add_one_le
    _ = a := mul_one a

theorem T_mul {f g : (ZMod 2)[X]} {a b : ℕ} (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) :
    T (a + b) (f * g) = T a f * T b g := by
  unfold T
  rw [mul_comp, reflect_mul _ _ (natDegree_comp_le' hf) (natDegree_comp_le' hg), mul_comp]

theorem T_add (m : ℕ) (f g : (ZMod 2)[X]) : T m (f + g) = T m f + T m g := by
  unfold T; rw [add_comp, reflect_add, add_comp]

theorem T_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → (ZMod 2)[X]) :
    T m (∑ i ∈ s, f i) = ∑ i ∈ s, T m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [T]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, T_add, ih]

theorem reflect_X_add_one_pow (k : ℕ) : reflect k ((X + 1 : (ZMod 2)[X]) ^ k) = (X + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, reflect_mul _ _ (natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left k natDegree_X_add_one_le)) natDegree_X_add_one_le, ih]
    congr 1
    rw [reflect_add, reflect_one, show (X : (ZMod 2)[X]) = X ^ 1 by simp, reflect_monomial]
    simp [add_comm]

theorem T_monomial (m k : ℕ) (hk : k ≤ m) (c : ZMod 2) :
    T m (C c * X ^ k) = C c * X ^ k * (1 + X) ^ (m - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
  unfold T
  rw [mul_comp, C_comp, X_pow_comp, reflect_C_mul, ← mul_one ((X + 1 : (ZMod 2)[X]) ^ k),
    reflect_mul _ _ (natDegree_pow_le.trans (by
      simpa using Nat.mul_le_mul_left k natDegree_X_add_one_le)) (by simp),
    reflect_X_add_one_pow, reflect_one, mul_comp, mul_comp, X_pow_comp, pow_comp, add_comp,
    X_comp, one_comp, X_add_one_add_one, C_comp, Nat.add_sub_cancel_left, add_comm (X : (ZMod 2)[X]) 1]
  ring

theorem T_gen (m : ℕ) : T m (((1 : (ZMod 2)[X]) + X) ^ m - 1) = (1 + X) ^ m - 1 := by
  unfold T
  rw [sub_comp, one_comp, pow_comp, add_comp, one_comp, X_comp,
    show (1 : (ZMod 2)[X]) + (X + 1) = X + 1 + 1 by ring, X_add_one_add_one, reflect_sub,
    reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, reflect_one, sub_comp, one_comp,
    X_pow_comp]
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm, add_comm (1 : (ZMod 2)[X]) X]

theorem T_HMR (s : Multiset ℕ) : T s.sum (HMR (ZMod 2) s) = HMR (ZMod 2) s := by
  induction s using Multiset.induction_on with
  | empty => simp [T, HMR]
  | cons a s ih =>
    have h : HMR (ZMod 2) (a ::ₘ s) = (((1 : (ZMod 2)[X]) + X) ^ a - 1) * HMR (ZMod 2) s := by
      simp [HMR]
    rw [h, Multiset.sum_cons, T_mul (natDegree_gen_le _ a) (natDegree_HMR_le _ s), T_gen, ih]


/-! ## The two congruences on `ℤ^n` -/

variable {n : ℕ}

theorem card_ne_zero (μ : n.Partition) (hn : 0 < n) : Multiset.card μ.parts ≠ 0 := by
  intro h
  have := μ.parts_sum
  rw [Multiset.card_eq_zero.mp h, Multiset.sum_zero] at this
  omega

theorem HM_sum (μ : n.Partition) (hn : 0 < n) :
    HM μ.parts = ∑ i : Fin n, C (eta μ i) * X ^ ((i : ℕ) + 1) := by
  have hdeg : (HM μ.parts).natDegree < n + 1 := by
    have := natDegree_HMR_le ℤ μ.parts
    rw [μ.parts_sum] at this
    rw [HM_eq]; omega
  rw [Fin.sum_univ_eq_sum_range (fun i => C (eta μ i) * X ^ (i + 1)) n]
  conv_lhs => rw [as_sum_range' _ _ hdeg, Finset.sum_range_succ',
    HM_coeff_lt _ (Nat.pos_of_ne_zero (card_ne_zero μ hn))]
  simp only [eta, ← C_mul_X_pow_eq_monomial, C_0, zero_mul, add_zero]

/-- `P_i = y^{i+1} ((1+y)^{N-i} - 1)` over `ZMod 2`. -/
noncomputable def Pc (n i : ℕ) : (ZMod 2)[X] := X ^ (i + 1) * (((1 : (ZMod 2)[X]) + X) ^ (n - 1 - i) - 1)

/-- The mod-2 palindromy defect `T(v) - v` of `v`. -/
noncomputable def D (v : Fin n → ℤ) : (ZMod 2)[X] := ∑ i : Fin n, C ((v i : ℤ) : ZMod 2) * Pc n i

theorem D_add (v w : Fin n → ℤ) : D (v + w) = D v + D w := by
  simp [D, add_mul, Finset.sum_add_distrib]

theorem D_smul (c : ℤ) (v : Fin n → ℤ) : D (c • v) = C (c : ZMod 2) * D v := by
  simp [D, Finset.mul_sum, mul_assoc]

theorem D_zero : D (0 : Fin n → ℤ) = 0 := by simp [D]

/-- The lattice cut out by (c1) `n ∣ v 0` and (c2) `D v = 0`. -/
def Lat (n : ℕ) (hn : 0 < n) : Submodule ℤ (Fin n → ℤ) where
  carrier := {v | (n : ℤ) ∣ v ⟨0, hn⟩ ∧ D v = 0}
  add_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    exact ⟨by simpa using dvd_add hv1 hw1, by rw [D_add, hv2, hw2, add_zero]⟩
  zero_mem' := ⟨by simp, D_zero⟩
  smul_mem' := by
    rintro c v ⟨hv1, hv2⟩
    exact ⟨by simpa using dvd_mul_of_dvd_right hv1 c, by rw [D_smul, hv2, mul_zero]⟩

/-- The vector `η_μ`. -/
noncomputable def ev (μ : n.Partition) : Fin n → ℤ := fun i => eta μ i

theorem ev_c1 (μ : n.Partition) (hn : 0 < n) : (n : ℤ) ∣ eta μ 0 := by
  have hc := card_ne_zero μ hn
  by_cases h1 : Multiset.card μ.parts = 1
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h1
    have hs := μ.parts_sum
    rw [ha, Multiset.sum_singleton] at hs
    show (n : ℤ) ∣ (HM μ.parts).coeff (0 + 1)
    rw [zero_add, ← h1, HM_coeff_card, ha, Multiset.prod_singleton, hs]
  · simp only [eta, zero_add]
    rw [HM_coeff_lt _ (by omega)]
    exact dvd_zero _

theorem HM2_sum (μ : n.Partition) (hn : 0 < n) :
    HMR (ZMod 2) μ.parts = ∑ i : Fin n, C ((eta μ i : ℤ) : ZMod 2) * X ^ ((i : ℕ) + 1) := by
  rw [← HMR_map, ← HM_eq, HM_sum μ hn, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, eq_intCast]

theorem ev_c2 (μ : n.Partition) (hn : 0 < n) : D (ev μ) = 0 := by
  have hT := T_HMR μ.parts
  rw [μ.parts_sum, HM2_sum μ hn, T_sum] at hT
  rw [D, ← sub_eq_zero.mpr hT, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [T_monomial _ _ (by omega), Pc, show n - 1 - (i : ℕ) = n - ((i : ℕ) + 1) by omega, ev]
  ring

theorem ev_mem (μ : n.Partition) (hn : 0 < n) : ev μ ∈ Lat n hn :=
  ⟨ev_c1 μ hn, ev_c2 μ hn⟩

theorem Pc_coeff_self (r : ℕ) : (Pc n r).coeff (r + 2) = ((n - 1 - r : ℕ) : ZMod 2) := by
  rw [Pc, coeff_X_pow_mul', if_pos (by omega), show r + 2 - (r + 1) = 1 by omega, coeff_sub,
    coeff_one_add_X_pow, coeff_one]
  simp

theorem Pc_coeff_gt (r i : ℕ) (h : r < i) : (Pc n i).coeff (r + 2) = 0 := by
  rw [Pc, coeff_X_pow_mul']
  split_ifs with h'
  · rw [show r + 2 - (i + 1) = 0 by omega, coeff_sub, coeff_one_add_X_pow, coeff_one]
    simp
  · rfl

theorem Lat_dvd (hn : 0 < n) {v : Fin n → ℤ} (hv : v ∈ Lat n hn) (r : Fin n)
    (h0 : ∀ i : Fin n, i < r → v i = 0) : (aa n r : ℤ) ∣ v r := by
  obtain ⟨hv1, hv2⟩ := hv
  unfold aa
  split_ifs with hr hpar
  · have : r = ⟨0, hn⟩ := Fin.ext hr
    rw [this]; exact hv1
  · have hc := congrArg (fun p => p.coeff ((r : ℕ) + 2)) hv2
    simp only [D, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc
    rw [Finset.sum_eq_single r] at hc
    · rw [Pc_coeff_self, (ZMod.natCast_eq_one_iff_odd).mpr ⟨(n - 1 - r) / 2, by omega⟩,
        mul_one] at hc
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hc
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hlt | hgt
      · rw [h0 b hlt]; simp
      · rw [Pc_coeff_gt _ _ hgt, mul_zero]
    · simp
  · exact_mod_cast one_dvd _


/-! ## The vectors `u_r` -/

/-- A partition from a multiset, defaulting to `(n)` when the multiset is not one. -/
def mkP (n : ℕ) (s : Multiset ℕ) : n.Partition :=
  if h : (∀ i ∈ s, 0 < i) ∧ s.sum = n then ⟨s, fun hi => h.1 _ hi, h.2⟩
  else Nat.Partition.indiscrete n

theorem mkP_parts {s : Multiset ℕ} (h1 : ∀ i ∈ s, 0 < i) (h2 : s.sum = n) :
    (mkP n s).parts = s := by
  rw [mkP, dif_pos ⟨h1, h2⟩]

/-- `(n-r, 1^r)`. -/
def hookS (n r : ℕ) : Multiset ℕ := (n - r) ::ₘ Multiset.replicate r 1

/-- `(n-r-1, 2, 1^{r-1})`. -/
def twoS (n r : ℕ) : Multiset ℕ := (n - r - 1) ::ₘ 2 ::ₘ Multiset.replicate (r - 1) 1

theorem hookS_parts {r : ℕ} (hr : r < n) : (mkP n (hookS n r)).parts = hookS n r := by
  refine mkP_parts (fun i hi => ?_) ?_
  · rcases Multiset.mem_cons.mp hi with h | h
    · omega
    · rw [Multiset.eq_of_mem_replicate h]; exact one_pos
  · simp [hookS]; omega

theorem twoS_parts {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ n) :
    (mkP n (twoS n r)).parts = twoS n r := by
  refine mkP_parts (fun i hi => ?_) ?_
  · rcases Multiset.mem_cons.mp hi with h | h
    · omega
    · rcases Multiset.mem_cons.mp h with h | h
      · omega
      · rw [Multiset.eq_of_mem_replicate h]; exact one_pos
  · simp [twoS]; omega

theorem card_hookS (n r : ℕ) : Multiset.card (hookS n r) = r + 1 := by
  simp [hookS]

theorem card_twoS {r : ℕ} (hr1 : 1 ≤ r) : Multiset.card (twoS n r) = r + 1 := by
  simp [twoS]; omega

theorem prod_hookS (n r : ℕ) : (hookS n r).prod = n - r := by
  simp [hookS]

theorem prod_twoS (n r : ℕ) : (twoS n r).prod = (n - r - 1) * 2 := by
  simp [twoS]

/-- `r` is in the middle range `1 ≤ r ≤ n - 2`. -/
def mid (n r : ℕ) : Prop := 1 ≤ r ∧ r + 2 ≤ n

instance (n r : ℕ) : Decidable (mid n r) := by unfold mid; infer_instance

/-- The first partition used for `u_r`. -/
def Ap (n r : ℕ) : n.Partition := mkP n (hookS n r)

/-- The second partition used for `u_r`. -/
def Bp (n r : ℕ) : n.Partition := if mid n r then mkP n (twoS n r) else Ap n r

/-- Bezout coefficients for `gcd(m, 2(m-1))`, `m = n - r`. -/
def xc (n r : ℕ) : ℤ :=
  if mid n r then (if (n - r) % 2 = 0 then 2 else 1 - 2 * (((n - r) / 2 : ℕ) : ℤ)) else 1

/-- Bezout coefficients for `gcd(m, 2(m-1))`, `m = n - r`. -/
def yc (n r : ℕ) : ℤ :=
  if mid n r then (if (n - r) % 2 = 0 then -1 else (((n - r) / 2 : ℕ) : ℤ)) else 0

/-- The matrix `W`: `u_r = xc r η_{A r} + yc r η_{B r}`. -/
noncomputable def Wm (n : ℕ) : Matrix (Fin n) n.Partition ℤ := fun r μ =>
  (if μ = Ap n r then xc n r else 0) + (if μ = Bp n r then yc n r else 0)

theorem Wm_sum (r : Fin n) (f : n.Partition → ℤ) :
    ∑ μ, Wm n r μ * f μ = xc n r * f (Ap n r) + yc n r * f (Bp n r) := by
  simp only [Wm, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem card_Ap {r : ℕ} (hr : r < n) : Multiset.card (Ap n r).parts = r + 1 := by
  rw [Ap, hookS_parts hr, card_hookS]

theorem card_Bp {r : ℕ} (hr : r < n) : Multiset.card (Bp n r).parts = r + 1 := by
  unfold Bp
  split_ifs with h
  · rw [twoS_parts h.1 h.2, card_twoS h.1]
  · exact card_Ap hr

theorem Wm_card (r : Fin n) (μ : n.Partition) (h : Wm n r μ ≠ 0) :
    Multiset.card μ.parts = (r : ℕ) + 1 := by
  unfold Wm at h
  by_cases hA : μ = Ap n r
  · rw [hA]; exact card_Ap r.2
  by_cases hB : μ = Bp n r
  · rw [hB]; exact card_Bp r.2
  simp [hA, hB] at h

theorem eta_low (μ : n.Partition) {r i : ℕ} (hμ : Multiset.card μ.parts = r + 1) (hi : i < r) :
    eta μ i = 0 :=
  HM_coeff_lt _ (by omega)

theorem eta_lead (μ : n.Partition) {r : ℕ} (hμ : Multiset.card μ.parts = r + 1) :
    eta μ r = (μ.parts.prod : ℤ) := by
  rw [eta, ← hμ, HM_coeff_card]

theorem bezout (m : ℕ) (hm : 2 ≤ m) :
    (if m % 2 = 0 then 2 else 1 - 2 * ((m / 2 : ℕ) : ℤ)) * (m : ℤ) +
      (if m % 2 = 0 then -1 else ((m / 2 : ℕ) : ℤ)) * (((m - 1) * 2 : ℕ) : ℤ) =
      if m % 2 = 0 then 2 else 1 := by
  split_ifs with h
  · push_cast [show 1 ≤ m by omega]; ring
  · obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
    rw [show (2 * t + 1) / 2 = t by omega, show 2 * t + 1 - 1 = 2 * t by omega]
    push_cast; ring

theorem u_lead (r : Fin n) : ∑ μ, Wm n r μ * eta μ r = aa n r := by
  rw [Wm_sum, eta_lead _ (card_Ap r.2), eta_lead _ (card_Bp r.2), Ap, hookS_parts r.2,
    prod_hookS]
  unfold Bp xc yc
  by_cases h : mid n r
  · simp only [if_pos h]
    rw [twoS_parts h.1 h.2, prod_twoS, show n - r - 1 = n - r - 1 from rfl]
    have hb := bezout (n - r) (by have := h.2; omega)
    rw [show n - (r : ℕ) - 1 = n - r - 1 from rfl] at hb
    rw [Nat.cast_sub (by omega : (r : ℕ) ≤ n)] at hb ⊢
    rw [hb, aa, if_neg (show ¬(r : ℕ) = 0 by have := h.1; omega)]
    have := r.2
    split_ifs <;> (try simp) <;> omega
  · simp only [if_neg h, one_mul, zero_mul, add_zero]
    unfold mid at h
    rw [aa]
    split_ifs with h0 hp
    · rw [h0]; simp
    · omega
    · push_cast [r.2.le]; omega

theorem u_low (r i : Fin n) (hi : i < r) : ∑ μ, Wm n r μ * eta μ i = 0 := by
  rw [Wm_sum, eta_low _ (card_Ap r.2) hi, eta_low _ (card_Bp r.2) hi]; ring

theorem aa_ne_zero (hn : 0 < n) (r : ℕ) : (aa n r : ℤ) ≠ 0 := by
  unfold aa; split_ifs <;> omega

/-! ## Elimination and independence -/

theorem elim (hn : 0 < n) (u : Fin n → Fin n → ℤ) (hu : ∀ r, u r ∈ Lat n hn)
    (hlow : ∀ r i : Fin n, i < r → u r i = 0) (hlead : ∀ r : Fin n, u r r = aa n r) :
    ∀ m : ℕ, ∀ v ∈ Lat n hn, (∀ i : Fin n, (i : ℕ) + m < n → v i = 0) →
      ∃ d : Fin n → ℤ, v = ∑ r, d r • u r := by
  intro m
  induction m with
  | zero =>
    intro v _ hv
    exact ⟨0, funext fun i => by simp [hv i (by omega)]⟩
  | succ m ih =>
    intro v hvL hv
    by_cases hm : n ≤ m
    · exact ih v hvL fun i hi => by omega
    set r : Fin n := ⟨n - 1 - m, by omega⟩ with hr
    have hrv : (r : ℕ) = n - 1 - m := rfl
    obtain ⟨k, hk⟩ := Lat_dvd hn hvL r fun i hi => hv i (by
      have : (i : ℕ) < r := hi
      omega)
    obtain ⟨d, hd⟩ := ih (v - k • u r) (Submodule.sub_mem _ hvL (Submodule.smul_mem _ _ (hu r)))
      (fun i hi => by
        rcases lt_or_eq_of_le (show (i : ℕ) ≤ r by omega) with h | h
        · simp [hv i (by omega), hlow r i h]
        · have : i = r := Fin.ext h
          subst this
          simp [hk, hlead, mul_comm])
    refine ⟨fun s => d s + if s = r then k else 0, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ← hd]
    abel

theorem indep (u : Fin n → Fin n → ℤ) (hlow : ∀ r i : Fin n, i < r → u r i = 0)
    (hlead : ∀ r : Fin n, u r r ≠ 0) (c : Fin n → ℤ) (hc : ∀ i, ∑ r, c r * u r i = 0) :
    ∀ r, c r = 0 := by
  suffices ∀ k : ℕ, ∀ r : Fin n, (r : ℕ) = k → c r = 0 from fun r => this r r rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r hr
    have h := hc r
    rw [Finset.sum_eq_single r] at h
    · exact (mul_eq_zero.mp h).resolve_right (hlead r)
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hlt | hgt
      · rw [ih b (by rw [← hr]; exact hlt) b rfl, zero_mul]
      · rw [hlow b r hgt, mul_zero]
    · simp

end LB


open LB in
theorem lemmaB {n : ℕ} (hn : 0 < n) :
    ∃ (W : Matrix (Fin n) n.Partition ℤ) (X : Matrix n.Partition (Fin n) ℤ),
      (∀ r μ, W r μ ≠ 0 → μ.parts.card = (r : ℕ) + 1) ∧
      (∀ r i : Fin n, i < r → ∑ μ, W r μ * eta μ i = 0) ∧
      (∀ r : Fin n, ∑ μ, W r μ * eta μ r = aa n r ∨ ∑ μ, W r μ * eta μ r = -(aa n r : ℤ)) ∧
      (∀ μ (i : Fin n), eta μ i = ∑ r, X μ r * ∑ ν, W r ν * eta ν i) ∧
      W * X = 1 := by
  set u : Fin n → Fin n → ℤ := fun r i => ∑ μ, Wm n r μ * eta μ i with hu
  have huL : ∀ r, u r ∈ Lat n hn := fun r => by
    have : u r = ∑ μ, Wm n r μ • ev μ := funext fun i => by simp [hu, ev]
    rw [this]
    exact Submodule.sum_mem _ fun μ _ => Submodule.smul_mem _ _ (ev_mem μ hn)
  have hlow : ∀ r i : Fin n, i < r → u r i = 0 := u_low
  have hlead : ∀ r : Fin n, u r r = aa n r := u_lead
  have hX : ∀ μ : n.Partition, ∃ d : Fin n → ℤ, ev μ = ∑ r, d r • u r := fun μ =>
    elim hn u huL hlow hlead n (ev μ) (ev_mem μ hn) fun i hi => by omega
  choose Xm hXm using hX
  have h4 : ∀ μ (i : Fin n), eta μ i = ∑ r, Xm μ r * u r i := fun μ i => by
    have := congrFun (hXm μ) i
    simp [ev] at this; exact this
  refine ⟨Wm n, fun μ r => Xm μ r, Wm_card, u_low, fun r => Or.inl (u_lead r), h4, ?_⟩
  ext r s
  have key := indep u hlow (fun r => by rw [hlead]; exact aa_ne_zero hn r)
    (fun s => (Wm n * Matrix.of fun μ r => Xm μ r) r s - (1 : Matrix (Fin n) (Fin n) ℤ) r s)
    (fun i => by
      simp only [sub_mul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply,
        Finset.sum_mul, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, ← h4]
      simp [hu])
    s
  exact sub_eq_zero.mp key

end StanleySnf
