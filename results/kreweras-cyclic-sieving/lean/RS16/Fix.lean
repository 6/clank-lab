import RS16.Chains

/-!
# Fixed points of the Bessis–Reiner action (the paper, Step 2)

* On delta sequences `φ` acts on `(w₁, …, w_s)` by the twisted rotation `ρ`, and `w₀` is
  determined by the rest, so `Fix(φ^p) = Fix(ρ^p)` (`phi_iter_fixed_iff`).
* `ext w : ℤ → G` extends `w` by `ext w (i + s) = c⁻¹ (ext w i) c`; then `ρ` is the shift by one
  (`ext_rho_iter`).
* With `s = ν m₁`, `p = h₁ m₁` and `gcd(h₁, ν) = 1`, the `ρ^p`-fixed `w` are exactly the
  `w = wB B` built from a first block `B ∈ C^{m₁}`, `C = C_G(c^{h₁})`, by
  `w_{j m₁ + r} = c^{e_j} B_r c^{-e_j}` (`fixed_iff_wB`).
-/

open scoped Classical

set_option linter.unusedSectionVars false

namespace RS16

variable {G : Type*} [Group G]

/-! ## φ and ρ on delta sequences -/

section Delta

variable (c : G)

lemma rho_zero {n : ℕ} (w : Fin (n + 1) → G) : rho c w 0 = c * w (Fin.last n) * c⁻¹ := by
  simp [rho, Fin.last]

lemma rho_succ {n : ℕ} (w : Fin (n + 1) → G) (i : Fin n) : rho c w i.succ = w i.castSucc := by
  simp only [rho, Fin.val_succ, Nat.add_one_ne_zero, ite_false]
  congr

lemma rho_prod {n : ℕ} (w : Fin (n + 1) → G) :
    (List.ofFn (rho c w)).prod * w (Fin.last n) =
      c * w (Fin.last n) * c⁻¹ * (List.ofFn w).prod := by
  rw [List.ofFn_succ, List.prod_cons, rho_zero]
  conv_rhs => rw [List.ofFn_succ', List.prod_concat]
  simp only [rho_succ, mul_assoc]

lemma rho_sum {ℓ : G → ℕ} (hl : LenHyp ℓ) {n : ℕ} (w : Fin (n + 1) → G) :
    ∑ i, ℓ (rho c w i) = ∑ i, ℓ (w i) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [rho_zero, rho_succ, hl.conj]
  ring

lemma delta_fst {ℓ : G → ℕ} {s : ℕ} {x : G × (Fin s → G)} (hx : IsDelta ℓ c x) :
    x.1 = c * (List.ofFn x.2).prod⁻¹ := by
  rw [← hx.1]; group

lemma phi_snd {s : ℕ} (hs : 0 < s) (x : G × (Fin s → G)) : (phi c x).2 = rho c x.2 := by
  simp [phi, hs]

lemma rho_zero' {n : ℕ} (w : Fin (n + 1) → G) (h : 0 < n + 1) :
    rho c w ⟨0, h⟩ = c * w (Fin.last n) * c⁻¹ := by
  simp [rho, Fin.last]

lemma phi_delta {ℓ : G → ℕ} (hl : LenHyp ℓ) {s : ℕ} {x : G × (Fin s → G)}
    (hx : IsDelta ℓ c x) : IsDelta ℓ c (phi c x) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simpa [phi] using hx
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  obtain ⟨x0, w⟩ := x
  obtain ⟨hp, hlen⟩ := hx
  simp only [phi, Nat.add_one_pos, dite_true, rho_zero']
  constructor
  · simp only
    have := rho_prod c w
    have hp' : x0 * (List.ofFn w).prod = c := hp
    have hw : (List.ofFn (rho c w)).prod = c * w (Fin.last n) * c⁻¹ * (List.ofFn w).prod *
        (w (Fin.last n))⁻¹ := by rw [← this]; group
    rw [hw, ← hp']
    group
  · simp only
    rw [hl.conj, rho_sum c hl]
    exact hlen

lemma phi_iter_snd {s : ℕ} (hs : 0 < s) (k : ℕ) (x : G × (Fin s → G)) :
    ((phi c)^[k] x).2 = (rho c)^[k] x.2 := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, phi_snd c hs]

lemma phi_iter_delta {ℓ : G → ℕ} (hl : LenHyp ℓ) {s : ℕ} (k : ℕ) {x : G × (Fin s → G)}
    (hx : IsDelta ℓ c x) : IsDelta ℓ c ((phi c)^[k] x) := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (phi_delta c hl hx)

lemma phi_iter_fixed_iff {ℓ : G → ℕ} (hl : LenHyp ℓ) {s : ℕ} (hs : 0 < s) (k : ℕ)
    {x : G × (Fin s → G)} (hx : IsDelta ℓ c x) :
    (phi c)^[k] x = x ↔ (rho c)^[k] x.2 = x.2 := by
  constructor
  · intro h; rw [← phi_iter_snd c hs, h]
  · intro h
    have h2 : ((phi c)^[k] x).2 = x.2 := by rw [phi_iter_snd c hs, h]
    have h1 : ((phi c)^[k] x).1 = x.1 := by
      rw [delta_fst c (phi_iter_delta c hl k hx), delta_fst c hx, h2]
    exact Prod.ext h1 h2

end Delta

/-! ## The twisted extension -/

section Ext

variable (c : G) {s : ℕ}

lemma emod_toNat_lt (hs : 0 < s) (i : ℤ) : (i % s).toNat < s := by
  have h1 := Int.emod_nonneg i (by omega : (s : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos i (by omega : (0 : ℤ) < s)
  omega

/-- `ext w i = c^{-(i / s)} w_{i mod s} c^{i / s}` -/
def ext (hs : 0 < s) (w : Fin s → G) (i : ℤ) : G :=
  c ^ (-(i / s)) * w ⟨(i % s).toNat, emod_toNat_lt hs i⟩ * c ^ (i / s)

lemma ext_eq (hs : 0 < s) (w : Fin s → G) (q : ℤ) (r : Fin s) :
    ext c hs w (r + q * s) = c ^ (-q) * w r * c ^ q := by
  have hs' : (s : ℤ) ≠ 0 := by omega
  have hd : ((r : ℤ) + q * s) / s = q := by
    rw [Int.add_mul_ediv_right _ _ hs', Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]
  have hm : ((r : ℤ) + q * s) % s = r := by
    rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
  unfold ext
  rw [hd]
  congr 3
  ext; simp [hm]

lemma ext_fin (hs : 0 < s) (w : Fin s → G) (r : Fin s) : ext c hs w r = w r := by
  have := ext_eq c hs w 0 r
  simpa using this

lemma ext_decomp (hs : 0 < s) (i : ℤ) : ∃ (r : Fin s) (q : ℤ), i = r + q * s :=
  ⟨⟨(i % s).toNat, emod_toNat_lt hs i⟩, i / s, by
    have h1 := Int.emod_nonneg i (by omega : (s : ℤ) ≠ 0)
    have := Int.emod_add_ediv_mul i s
    simp only [Int.toNat_of_nonneg h1]
    linarith⟩

lemma ext_add_mul (hs : 0 < s) (w : Fin s → G) (i z : ℤ) :
    ext c hs w (i + z * s) = c ^ (-z) * ext c hs w i * c ^ z := by
  obtain ⟨r, q, rfl⟩ := ext_decomp hs i
  rw [show (r : ℤ) + q * s + z * s = r + (q + z) * s by ring, ext_eq, ext_eq]
  rw [zpow_add, neg_add, zpow_add]
  group

lemma ext_rho (hs : 0 < s) (w : Fin s → G) (i : ℤ) : ext c hs (rho c w) i = ext c hs w (i - 1) := by
  obtain ⟨r, q, rfl⟩ := ext_decomp hs i
  rw [ext_eq]
  by_cases hr : r.val = 0
  · have hw : rho c w r = c * w ⟨s - 1, by omega⟩ * c⁻¹ := by simp [rho, hr]
    have : (r : ℤ) + q * s - 1 = ((⟨s - 1, by omega⟩ : Fin s) : ℕ) + (q - 1) * s := by
      simp only [hr, CharP.cast_eq_zero]
      push_cast [Nat.cast_sub (by omega : 1 ≤ s)]
      ring
    rw [this, ext_eq, hw]
    simp only [zpow_sub, zpow_one, neg_sub]
    group
  · have hw : rho c w r = w ⟨r.val - 1, by omega⟩ := by simp [rho, hr]
    have : (r : ℤ) + q * s - 1 = ((⟨r.val - 1, by omega⟩ : Fin s) : ℕ) + q * s := by
      simp only
      push_cast [Nat.cast_sub (by omega : 1 ≤ r.val)]
      ring
    rw [this, ext_eq, hw]

lemma ext_rho_iter (hs : 0 < s) (k : ℕ) (w : Fin s → G) (i : ℤ) :
    ext c hs ((rho c)^[k] w) i = ext c hs w (i - k) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, ext_rho]
    push_cast; ring_nf

lemma ext_inj (hs : 0 < s) {w w' : Fin s → G} (h : ∀ r : Fin s, ext c hs w r = ext c hs w' r) : w = w' := by
  funext r; rw [← ext_fin c hs w r, ← ext_fin c hs w' r, h]

lemma rho_fixed_iff (hs : 0 < s) (p : ℕ) (w : Fin s → G) :
    (rho c)^[p] w = w ↔ ∀ i, ext c hs w (i + p) = ext c hs w i := by
  constructor
  · intro h i
    have := ext_rho_iter c hs p w (i + p)
    rw [h, add_sub_cancel_right] at this
    exact this
  · intro h
    apply ext_inj c hs
    intro r
    rw [ext_rho_iter, ← h (r - p), sub_add_cancel]

/-- `φ^{s h}` is the identity on delta sequences when `c^h = 1`. -/
lemma rho_iter_sh (hs : 0 < s) {h : ℕ} (hch : c ^ h = 1) (w : Fin s → G) : (rho c)^[s * h] w = w := by
  apply ext_inj c hs
  intro r
  rw [ext_rho_iter, show (r : ℤ) - ((s * h : ℕ) : ℤ) = r + (-(h : ℤ)) * s by push_cast; ring,
    ext_add_mul]
  simp [zpow_natCast, hch]

end Ext

/-! ## Blocks -/

section Blocks

variable (c : G)

lemma pos_of_fin_mul {m1 ν : ℕ} (i : Fin (ν * m1)) : 0 < m1 :=
  Nat.pos_of_ne_zero fun h => by have := i.isLt; simp [h] at this

/-- `w_{j m₁ + r} = c^{e_j} B_r c^{-e_j}` -/
def wB {m1 : ℕ} (ν : ℕ) (e : ℕ → ℕ) (B : Fin m1 → G) : Fin (ν * m1) → G := fun i =>
  c ^ e (i / m1) * B ⟨i % m1, Nat.mod_lt _ (pos_of_fin_mul i)⟩ * (c ^ e (i / m1))⁻¹

/-- conjugation by `c^α` on `C_G(c^{h₁})` depends on `α` modulo `h₁` -/
lemma conj_congr {h1 : ℕ} {g : G} (hg : Commute g (c ^ h1)) {α β : ℤ} (h : (h1 : ℤ) ∣ α - β) :
    c ^ α * g * c ^ (-α) = c ^ β * g * c ^ (-β) := by
  obtain ⟨t, ht⟩ := h
  have hα : α = β + h1 * t := by linarith
  set a := (c ^ (h1 : ℤ)) ^ t
  have hc : Commute g a := by
    simp only [a]; rw [zpow_natCast]; exact hg.zpow_right t
  have e1 : c ^ α = c ^ β * a := by rw [hα, zpow_add, zpow_mul]
  have e2 : c ^ (-α) = a⁻¹ * c ^ (-β) := by rw [zpow_neg, e1, mul_inv_rev, zpow_neg]
  have e3 : a * g * a⁻¹ = g := by rw [← hc.eq, mul_inv_cancel_right]
  rw [e1, e2]
  calc c ^ β * a * g * (a⁻¹ * c ^ (-β)) = c ^ β * (a * g * a⁻¹) * c ^ (-β) := by group
    _ = c ^ β * g * c ^ (-β) := by rw [e3]

lemma decomp_m1 {m1 : ℕ} (hm1 : 0 < m1) (i : ℤ) : ∃ (r : Fin m1) (J : ℤ), i = r + J * m1 :=
  ⟨⟨(i % m1).toNat, emod_toNat_lt hm1 i⟩, i / m1, by
    have h1 := Int.emod_nonneg i (by omega : (m1 : ℤ) ≠ 0)
    have := Int.emod_add_ediv_mul i m1
    simp only [Int.toNat_of_nonneg h1]
    linarith⟩

variable {m1 ν h1 : ℕ} {x y : ℤ} (hxy : x * ν + y * h1 = 1)
  (hcop : IsCoprime (h1 : ℤ) (ν : ℤ)) {e : ℕ → ℕ} (he : ∀ j, j < ν → (h1 : ℤ) ∣ ν * e j + j)
include hxy hcop he

lemma exp_dvd {j : ℕ} (hj : j < ν) : (h1 : ℤ) ∣ (e j : ℤ) - (-x * j) := by
  apply hcop.dvd_of_dvd_mul_left
  have h := he j hj
  have : (ν : ℤ) * ((e j : ℤ) - (-x * j)) = (ν * e j + j) - j * y * h1 := by
    linear_combination (j : ℤ) * hxy
  rw [this]
  exact dvd_sub h (Dvd.intro_left _ rfl)

lemma wB_block {B : Fin m1 → G} (hB : ∀ r, Commute (B r) (c ^ h1)) {j : ℕ} (hj : j < ν)
    (r : Fin m1) : c ^ e j * B r * (c ^ e j)⁻¹ = c ^ (-x * j) * B r * c ^ (-(-x * j)) := by
  rw [← zpow_natCast, ← zpow_neg]
  exact conj_congr c (hB r) (exp_dvd hxy hcop he hj)

lemma ext_wB (hν : 0 < ν) (hm1 : 0 < m1) (B : Fin m1 → G) (hB : ∀ r, Commute (B r) (c ^ h1))
    (r : Fin m1) (J : ℤ) :
    ext c (Nat.mul_pos hν hm1) (wB c ν e B) (r + J * m1) = c ^ (-x * J) * B r * c ^ (x * J) := by
  obtain ⟨j, q, hJ⟩ : ∃ (j : Fin ν) (q : ℤ), J = j + q * ν := by
    exact decomp_m1 hν J
  have hlt : r.val + j.val * m1 < ν * m1 := by
    have := r.isLt; have := j.isLt; nlinarith
  have hi : (r : ℤ) + J * m1 = ((⟨r.val + j.val * m1, hlt⟩ : Fin (ν * m1)) : ℕ) + q * (ν * m1 : ℕ) := by
    rw [hJ]; push_cast; ring
  rw [hi, ext_eq]
  have hdiv : (r.val + j.val * m1) / m1 = j.val := by
    rw [Nat.add_mul_div_right _ _ hm1, Nat.div_eq_of_lt r.isLt, zero_add]
  have hmod : (r.val + j.val * m1) % m1 = r.val := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
  simp only [wB, hdiv, hmod]
  rw [wB_block c hxy hcop he hB j.isLt r]
  -- `c^{-x q ν} B_r c^{x q ν} = c^{-q} B_r c^{q}`
  have hq := conj_congr c (hB r) (α := -x * q * ν) (β := -q) ⟨q * y, by linear_combination (-q) * hxy⟩
  rw [hJ]
  calc c ^ (-q) * (c ^ (-x * j) * B r * c ^ (-(-x * j))) * c ^ q
      = c ^ (-x * j) * (c ^ (-q) * B r * c ^ (-(-q))) * c ^ (x * j) := by
        simp only [neg_neg, neg_mul]; group
    _ = c ^ (-x * j) * (c ^ (-x * q * ν) * B r * c ^ (-(-x * q * ν))) * c ^ (x * j) := by
        rw [hq]
    _ = c ^ (-x * (j + q * ν)) * B r * c ^ (x * (j + q * ν)) := by
        simp only [neg_neg, neg_mul, mul_add]; group

lemma wB_fixed (hν : 0 < ν) (hm1 : 0 < m1) (B : Fin m1 → G) (hB : ∀ r, Commute (B r) (c ^ h1)) :
    (rho c)^[h1 * m1] (wB c ν e B) = wB c ν e B := by
  rw [rho_fixed_iff c (Nat.mul_pos hν hm1)]
  intro i
  obtain ⟨r, J, rfl⟩ := decomp_m1 hm1 i
  rw [show (r : ℤ) + J * m1 + ((h1 * m1 : ℕ) : ℤ) = r + (J + h1) * m1 by push_cast; ring,
    ext_wB c hxy hcop he hν hm1 B hB, ext_wB c hxy hcop he hν hm1 B hB]
  have := conj_congr c (hB r) (α := -x * (J + h1)) (β := -x * J) ⟨-x, by ring⟩
  simpa only [neg_mul, neg_neg] using this

lemma wB_first (hν : 0 < ν) (B : Fin m1 → G) (hB : ∀ r, Commute (B r) (c ^ h1)) (r : Fin m1) :
    wB c ν e B ⟨r, by have := r.isLt; nlinarith⟩ = B r := by
  have hm1 : 0 < m1 := Nat.pos_of_ne_zero fun h => by have := r.isLt; omega
  have h0 : (h1 : ℤ) ∣ (e 0 : ℤ) - 0 := by
    have := he 0 hν
    simp only [CharP.cast_eq_zero, add_zero, sub_zero] at this ⊢
    exact hcop.dvd_of_dvd_mul_left this
  have := conj_congr c (hB r) h0
  simp only [zpow_zero, one_mul, mul_one, neg_zero, zpow_natCast, zpow_neg] at this
  simp only [wB, Nat.div_eq_of_lt r.isLt, Nat.mod_eq_of_lt r.isLt]
  exact this

end Blocks

end RS16
