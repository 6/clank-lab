import RS16.Fix

/-!
# The fixed-point count (the paper, Step 2)

`fixCount_eq_Lval`: for `s = ν m₁`, `p = h₁ m₁`, `gcd(h₁, ν) = 1` and exponents `e_j` with
`h₁ ∣ ν e_j + j`, the number of delta sequences fixed by `φ^p` with bottom class `X` is
`L_X(m₁) = Σ_k binom(m₁, k) Σ_{u ∈ U_X} c_k(u)`.
-/

open scoped Classical

set_option linter.unusedSectionVars false

namespace RS16

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] (c : G)

/-! ## Fixed points are block sequences -/

section Forward

variable {m1 ν h1 : ℕ} {x y : ℤ} (hxy : x * ν + y * h1 = 1)
  (hcop : IsCoprime (h1 : ℤ) (ν : ℤ)) {e : ℕ → ℕ} (he : ∀ j, j < ν → (h1 : ℤ) ∣ ν * e j + j)
  (hm1 : 0 < m1) (hν : 0 < ν)
include hxy hm1 hν

lemma per_zmul {w : Fin (ν * m1) → G} (hw : (rho c)^[h1 * m1] w = w) (i z : ℤ) :
    ext c (Nat.mul_pos hν hm1) w (i + z * (h1 * m1 : ℕ)) = ext c (Nat.mul_pos hν hm1) w i := by
  have hp := (rho_fixed_iff c (Nat.mul_pos hν hm1) (h1 * m1) w).mp hw
  induction z using Int.induction_on generalizing i with
  | zero => simp
  | succ k ih => rw [add_mul, one_mul, ← add_assoc, hp, ih]
  | pred k ih =>
    rw [← ih i, show i + (-(k : ℤ)) * (h1 * m1 : ℕ) = (i + (-(k : ℤ) - 1) * (h1 * m1 : ℕ)) +
      (h1 * m1 : ℕ) by ring, hp]

lemma shift_m1 {w : Fin (ν * m1) → G} (hw : (rho c)^[h1 * m1] w = w) (i : ℤ) :
    ext c (Nat.mul_pos hν hm1) w (i + m1) =
      c ^ (-x) * ext c (Nat.mul_pos hν hm1) w i * c ^ x := by
  have : i + m1 = (i + y * (h1 * m1 : ℕ)) + x * (ν * m1 : ℕ) := by
    push_cast; linear_combination (-(m1 : ℤ)) * hxy
  rw [this, ext_add_mul, per_zmul c hxy hm1 hν hw]

lemma shift_J {w : Fin (ν * m1) → G} (hw : (rho c)^[h1 * m1] w = w) (i J : ℤ) :
    ext c (Nat.mul_pos hν hm1) w (i + J * m1) =
      c ^ (-x * J) * ext c (Nat.mul_pos hν hm1) w i * c ^ (x * J) := by
  induction J using Int.induction_on generalizing i with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, ← add_assoc, shift_m1 c hxy hm1 hν hw, ih]
    simp only [mul_add, neg_mul, mul_one]; group
  | pred k ih =>
    have := shift_m1 c hxy hm1 hν hw (i + (-(k : ℤ) - 1) * m1)
    rw [show i + (-(k : ℤ) - 1) * m1 + m1 = i + (-(k : ℤ)) * m1 by ring, ih] at this
    have h2 : ext c (Nat.mul_pos hν hm1) w (i + (-(k : ℤ) - 1) * m1) =
        c ^ x * (c ^ (-x * -(k : ℤ)) * ext c (Nat.mul_pos hν hm1) w i * c ^ (x * -(k : ℤ))) *
          c ^ (-x) := by
      rw [this]; group
    rw [h2]
    simp only [mul_neg, neg_mul, neg_neg, sub_eq_add_neg]; group

lemma fixed_commute {w : Fin (ν * m1) → G} (hw : (rho c)^[h1 * m1] w = w) (i : ℤ) :
    Commute (ext c (Nat.mul_pos hν hm1) w i) (c ^ h1) := by
  set E := ext c (Nat.mul_pos hν hm1) w i
  -- `E = c^{-x h₁} E c^{x h₁}`
  have h1' : E = c ^ (-x * h1) * E * c ^ (x * h1) := by
    have := shift_J c hxy hm1 hν hw i h1
    rw [show i + (h1 : ℤ) * m1 = i + 1 * (h1 * m1 : ℕ) by push_cast; ring,
      per_zmul c hxy hm1 hν hw] at this
    exact this
  -- `c⁻¹ E c = c^{-x ν} E c^{x ν}`
  have h2' : c ^ (-1 : ℤ) * E * c ^ (1 : ℤ) = c ^ (-x * ν) * E * c ^ (x * ν) := by
    have := shift_J c hxy hm1 hν hw i ν
    rw [show i + (ν : ℤ) * m1 = i + 1 * (ν * m1 : ℕ) by push_cast; ring, ext_add_mul] at this
    exact this
  have ca : Commute E (c ^ (x * h1)) := by
    have : c ^ (x * h1) * E = E * c ^ (x * h1) := by
      conv_lhs => rw [h1']
      simp only [neg_mul]; group
    exact this.symm
  have cb : Commute E (c ^ (y * h1)) := by
    have hy : y * h1 = 1 - x * ν := by linarith
    have : c ^ (1 - x * ν) * E = E * c ^ (1 - x * ν) := by
      have h3 : E = c ^ (1 - x * ν) * E * c ^ (-(1 - x * ν)) := by
        calc E = c ^ (1 : ℤ) * (c ^ (-1 : ℤ) * E * c ^ (1 : ℤ)) * c ^ (-1 : ℤ) := by group
          _ = c ^ (1 : ℤ) * (c ^ (-x * ν) * E * c ^ (x * ν)) * c ^ (-1 : ℤ) := by rw [h2']
          _ = c ^ (1 - x * ν) * E * c ^ (-(1 - x * ν)) := by
            simp only [neg_mul, neg_sub]; group
      conv_rhs => rw [h3]
      group
    rw [hy]; exact this.symm
  have : (c ^ (x * h1)) ^ ν * (c ^ (y * h1)) ^ (h1 : ℤ) = c ^ h1 := by
    rw [← zpow_natCast (c ^ (x * h1)) ν, ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_natCast c h1]
    congr 1
    linear_combination (h1 : ℤ) * hxy
  rw [← this]
  exact (ca.pow_right _).mul_right (cb.zpow_right _)

include hcop he

lemma fixed_eq_wB {w : Fin (ν * m1) → G} (hw : (rho c)^[h1 * m1] w = w) :
    w = wB c ν e (fun r => w ⟨r, by have := r.isLt; nlinarith⟩) := by
  have hs := Nat.mul_pos hν hm1
  set B : Fin m1 → G := fun r => w ⟨r, by have := r.isLt; nlinarith⟩
  have hB : ∀ r, Commute (B r) (c ^ h1) := fun r => by
    have := fixed_commute c hxy hm1 hν hw r
    rwa [show ((r : ℕ) : ℤ) = (((⟨r, by have := r.isLt; nlinarith⟩ : Fin (ν * m1)) : ℕ) : ℤ)
      from rfl, ext_fin] at this
  apply ext_inj c hs
  intro i
  obtain ⟨r, J, hi⟩ := decomp_m1 hm1 (i : ℤ)
  rw [hi, ext_wB c hxy hcop he hν hm1 B hB, shift_J c hxy hm1 hν hw]
  rw [show ((r : ℕ) : ℤ) = (((⟨r, by have := r.isLt; nlinarith⟩ : Fin (ν * m1)) : ℕ) : ℤ)
    from rfl, ext_fin]

end Forward

/-! ## Products and lengths of block sequences -/

lemma ofFn_conj_prod {m : ℕ} (g : G) (B : Fin m → G) :
    (List.ofFn fun r => g * B r * g⁻¹).prod = g * (List.ofFn B).prod * g⁻¹ := by
  have := map_list_prod (MulAut.conj g) (List.ofFn B)
  rw [List.map_ofFn] at this
  simpa [Function.comp_def] using this.symm

lemma wB_prod {m1 ν : ℕ} (e : ℕ → ℕ) (B : Fin m1 → G) :
    (List.ofFn (wB c ν e B)).prod =
      (List.ofFn fun j : Fin ν => c ^ e j * (List.ofFn B).prod * (c ^ e j)⁻¹).prod := by
  rcases Nat.eq_zero_or_pos m1 with h | hm1
  · subst h; simp [List.ofFn_zero]
  rw [List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  simp only [Function.comp_apply]
  rw [← ofFn_conj_prod]
  congr 1
  apply List.ofFn_inj.mpr
  funext r
  simp only [wB]
  have hdiv : (j.val * m1 + r.val) / m1 = j.val := by
    rw [add_comm, Nat.add_mul_div_right _ _ hm1, Nat.div_eq_of_lt r.isLt, zero_add]
  have hmod : (j.val * m1 + r.val) % m1 = r.val := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
  simp only [hdiv, hmod]

lemma wB_sum {ℓ : G → ℕ} (hl : LenHyp ℓ) {m1 ν : ℕ} (e : ℕ → ℕ) (B : Fin m1 → G) :
    ∑ i, ℓ (wB c ν e B i) = ν * ∑ r, ℓ (B r) := by
  rcases Nat.eq_zero_or_pos m1 with h | hm1
  · subst h; simp
  rw [← List.sum_ofFn, List.ofFn_mul, List.sum_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.sum_ofFn]
  have : ∀ j : Fin ν, ∑ r : Fin m1, ℓ (wB c ν e B ⟨j * m1 + r, by
      have := r.isLt; have := j.isLt; nlinarith⟩) = ∑ r, ℓ (B r) := by
    intro j
    apply Finset.sum_congr rfl
    intro r _
    have hdiv : (j.val * m1 + r.val) / m1 = j.val := by
      rw [add_comm, Nat.add_mul_div_right _ _ hm1, Nat.div_eq_of_lt r.isLt, zero_add]
    have hmod : (j.val * m1 + r.val) % m1 = r.val := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
    simp only [wB, hdiv, hmod, hl.conj]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## The inequalities of Step 2 -/

section Ineq

variable {ℓ : G → ℕ} (hl : LenHyp ℓ) {h1 ν : ℕ} (e : ℕ → ℕ)
include hl

lemma blocks_len_le (u : G) :
    ℓ (List.ofFn fun j : Fin ν => c ^ e j * u * (c ^ e j)⁻¹).prod ≤ ν * ℓ u := by
  have := hl.ofFn_prod_le (fun j : Fin ν => c ^ e j * u * (c ^ e j)⁻¹)
  simpa [hl.conj] using this

omit hl in
lemma bottom_mul (u : G) :
    bottom c ν e u * (List.ofFn fun j : Fin ν => c ^ e j * u * (c ^ e j)⁻¹).prod = c := by
  simp [bottom]

/-- Step 2, (i) and (ii): `n = ℓ(w₀) + ν Σ ℓ(x) ≥ ℓ(w₀) + ν ℓ(u) ≥ ℓ(c) = n`. -/
lemma bottom_ineq (hν : 0 < ν) {m1 : ℕ} (B : Fin m1 → G)
    (h : ℓ (bottom c ν e (List.ofFn B).prod) + ν * ∑ r, ℓ (B r) = ℓ c) :
    ∑ r, ℓ (B r) = ℓ (List.ofFn B).prod ∧
      ℓ (bottom c ν e (List.ofFn B).prod) + ν * ℓ (List.ofFn B).prod = ℓ c := by
  set u := (List.ofFn B).prod
  have a := hl.mul (bottom c ν e u) (List.ofFn fun j : Fin ν => c ^ e j * u * (c ^ e j)⁻¹).prod
  rw [bottom_mul] at a
  have b := blocks_len_le c hl e (ν := ν) u
  have d := hl.ofFn_prod_le B
  have : ν * ℓ u ≤ ν * ∑ r, ℓ (B r) := Nat.mul_le_mul_left _ d
  have : ν * ℓ u = ν * ∑ r, ℓ (B r) := by omega
  exact ⟨(Nat.eq_of_mul_eq_mul_left hν this).symm, by omega⟩

/-- The `u` of a fixed point lies in `NC(W)`. -/
lemma bottom_absLE (hν : 0 < ν) (he0 : (h1 : ℤ) ∣ e 0) {u : G} (hu : Commute u (c ^ h1))
    (h : ℓ (bottom c ν e u) + ν * ℓ u = ℓ c) : absLE ℓ u c := by
  obtain ⟨n, rfl⟩ : ∃ n, ν = n + 1 := ⟨ν - 1, by omega⟩
  have hu0 : c ^ e 0 * u * (c ^ e 0)⁻¹ = u := by
    have := conj_congr c hu (α := e 0) (β := 0) (by simpa using he0)
    simpa [zpow_natCast] using this
  set b := bottom c (n + 1) e u
  have hc := bottom_mul c e (ν := n + 1) u
  rw [List.ofFn_succ, List.prod_cons] at hc
  simp only [Fin.val_zero] at hc
  rw [hu0] at hc
  set R := (List.ofFn fun i : Fin n => c ^ e (i.succ : ℕ) * u * (c ^ e (i.succ : ℕ))⁻¹).prod
  have huc : u⁻¹ * c = (u⁻¹ * b * u⁻¹⁻¹) * R := by
    rw [← hc, inv_inv]; simp only [b, mul_assoc]
  have h1' := hl.mul (u⁻¹ * b * u⁻¹⁻¹) R
  rw [← huc, hl.conj] at h1'
  have h2 := hl.ofFn_prod_le (fun i : Fin n => c ^ e (i.succ : ℕ) * u * (c ^ e (i.succ : ℕ))⁻¹)
  simp only [hl.conj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  have h3 := hl.le_split u c
  unfold absLE
  have : ℓ R ≤ n * ℓ u := h2
  nlinarith

end Ineq

/-! ## The count -/

variable {ℓ : G → ℕ} (hl : LenHyp ℓ) {α : Type*} (cls : G → α)
include hl

theorem fixCount_eq_Lval {m1 ν h1 : ℕ} (hm1 : 0 < m1) (hν : 0 < ν) (hcop : Nat.Coprime h1 ν)
    (e : ℕ → ℕ) (he : ∀ j, j < ν → (h1 : ℤ) ∣ ν * e j + j) (X : α) :
    fixCount ℓ c cls (ν * m1) (h1 * m1) X = Lval ℓ c cls h1 ν e X m1 := by
  have hs := Nat.mul_pos hν hm1
  have hcop' : IsCoprime (h1 : ℤ) (ν : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, x * ν + y * h1 = 1 := by
    obtain ⟨u, v, h⟩ := hcop'; exact ⟨v, u, by linarith⟩
  have he0 : (h1 : ℤ) ∣ e 0 := by
    have := he 0 hν; simp only [CharP.cast_eq_zero, add_zero] at this
    exact hcop'.dvd_of_dvd_mul_left this
  -- Step A: delta sequences fixed by `φ^p` are the `ρ^p`-fixed `w` with `w₀ = c (Π w)⁻¹`
  have eA : {x : G × (Fin (ν * m1) → G) // IsDelta ℓ c x ∧ (phi c)^[h1 * m1] x = x ∧ cls x.1 = X}
      ≃ {w : Fin (ν * m1) → G // (rho c)^[h1 * m1] w = w ∧
          ℓ (c * (List.ofFn w).prod⁻¹) + ∑ i, ℓ (w i) = ℓ c ∧ cls (c * (List.ofFn w).prod⁻¹) = X} :=
    { toFun := fun x => ⟨x.1.2, (phi_iter_fixed_iff c hl hs _ x.2.1).mp x.2.2.1,
        by rw [← delta_fst c x.2.1]; exact x.2.1.2, by rw [← delta_fst c x.2.1]; exact x.2.2.2⟩
      invFun := fun w => ⟨(c * (List.ofFn w.1).prod⁻¹, w.1), by
          have hd : IsDelta ℓ c (c * (List.ofFn w.1).prod⁻¹, w.1) := ⟨by simp, w.2.2.1⟩
          exact ⟨hd, (phi_iter_fixed_iff c hl hs _ hd).mpr w.2.1, w.2.2.2⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact Prod.ext (delta_fst c x.2.1).symm rfl
      right_inv := fun w => rfl }
  -- Step B: those are the block sequences of `B ∈ C^{m₁}`
  have eB : {w : Fin (ν * m1) → G // (rho c)^[h1 * m1] w = w ∧
          ℓ (c * (List.ofFn w).prod⁻¹) + ∑ i, ℓ (w i) = ℓ c ∧ cls (c * (List.ofFn w).prod⁻¹) = X}
      ≃ {B : Fin m1 → G // (∀ r, Commute (B r) (c ^ h1)) ∧
          ℓ (bottom c ν e (List.ofFn B).prod) + ν * ∑ r, ℓ (B r) = ℓ c ∧
          cls (bottom c ν e (List.ofFn B).prod) = X} :=
    { toFun := fun w => by
        refine ⟨fun r => w.1 ⟨r, by have := r.isLt; nlinarith⟩, fun r => ?_, ?_⟩
        · have := fixed_commute c hxy hm1 hν w.2.1 r
          rwa [show ((r : ℕ) : ℤ) = (((⟨r, by have := r.isLt; nlinarith⟩ : Fin (ν * m1)) : ℕ) : ℤ)
            from rfl, ext_fin] at this
        · have hw := fixed_eq_wB c hxy hcop' he hm1 hν w.2.1
          have h := w.2.2
          rw [hw, wB_prod, wB_sum c hl] at h
          exact h
      invFun := fun B => ⟨wB c ν e B.1, wB_fixed c hxy hcop' he hν hm1 B.1 B.2.1, by
          rw [wB_prod, wB_sum c hl]; exact B.2.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        exact (fixed_eq_wB c hxy hcop' he hm1 hν w.2.1).symm
      right_inv := fun B => by
        apply Subtype.ext
        funext r
        exact wB_first c hxy hcop' he hν B.1 B.2.1 r }
  unfold fixCount
  rw [Nat.card_congr (eA.trans eB), Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step C: group by `u = Π B`
  rw [Finset.card_eq_sum_card_fiberwise (f := fun B : Fin m1 → G => (List.ofFn B).prod)
    (t := Uset ℓ c cls h1 ν e X)]
  · unfold Lval
    rw [Finset.sum_congr rfl (g := fun u => fcount ℓ c h1 m1 u)]
    · calc ∑ u ∈ Uset ℓ c cls h1 ν e X, fcount ℓ c h1 m1 u
          = ∑ u ∈ Uset ℓ c cls h1 ν e X, ∑ k ∈ Finset.range (ℓ c + 1),
              m1.choose k * chains ℓ c h1 k u :=
            Finset.sum_congr rfl (fun u hu => fcount_eq_chains hl c h1 m1 u
              (by unfold Uset at hu; exact (Finset.mem_filter.mp hu).1))
        _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    · intro u hu
      obtain ⟨hu1, hu2, hu3⟩ := Finset.mem_filter.mp hu
      unfold fcount
      rw [Finset.filter_filter]
      congr 1
      apply Finset.filter_congr
      intro B _
      constructor
      · rintro ⟨⟨hC, hlen, -⟩, hp⟩
        have := bottom_ineq c hl e hν B hlen
        rw [hp] at this
        exact ⟨hC, hp, this.1⟩
      · rintro ⟨hC, hp, hlen⟩
        refine ⟨⟨hC, ?_, ?_⟩, hp⟩
        · rw [hp, hlen]; exact hu2
        · rw [hp]; exact hu3
  · intro B hB
    obtain ⟨-, hC, hlen, hcls⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hB)
    have h := bottom_ineq c hl e hν B hlen
    have hu : Commute (List.ofFn B).prod (c ^ h1) := commute_ofFn_prod B hC
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, h.2, hcls⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, bottom_absLE c hl e hν he0 hu h.2, hu⟩

/-- The paper, Step 2, "Large ν": for `ν > ℓ(c)` only `u = 1` survives, so
`L_X(m₁) = [X = [c]]`. -/
theorem Lval_large {m1 ν h1 : ℕ} (hν : ℓ c < ν) (e : ℕ → ℕ) (X : α) :
    Lval ℓ c cls h1 ν e X m1 = if cls c = X then 1 else 0 := by
  have hb1 : bottom c ν e 1 = c := by simp [bottom]
  have hU : Uset ℓ c cls h1 ν e X = if cls c = X then {1} else ∅ := by
    ext u
    unfold Uset ncC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hlen, hcls⟩
      have hu : u = 1 := by
        rw [← hl.zero]
        by_contra h0
        have : ν ≤ ν * ℓ u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
        omega
      subst hu
      rw [hb1] at hcls
      simp [hcls]
    · intro h
      split_ifs at h with hX
      · rw [Finset.mem_singleton] at h
        subst h
        exact ⟨⟨hl.absLE_one c, Commute.one_left _⟩, by rw [hb1, hl.one]; simp, by rw [hb1, hX]⟩
      · simp at h
  unfold Lval
  rw [hU]
  split_ifs
  · simp only [Finset.sum_singleton]
    rw [Finset.sum_eq_single 0]
    · simp [chains]
    · intro k _ hk
      rw [chains_eq_zero hl c h1 k 1 (by rw [hl.one]; omega), mul_zero]
    · simp
  · simp

end RS16
