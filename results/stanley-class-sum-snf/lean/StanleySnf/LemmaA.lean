import StanleySnf.Core

/-!
# Lemma A: the `α(ν)` are integral and span `ℤ^n`

Integrality goes through Hurwitz-integral polynomials (`t! [y^t] f ∈ ℤ` for all `t`), which
form a ring closed under divided powers `f^m/m!` of polynomials with `f(0) = 0`;
`Φ_s = ∏_k φ_k^{m_k}/m_k!` with `φ_k = ((1+y)^k - 1)/k` is then Hurwitz-integral.
The Euler identity `n Φ_s = ∑_k ((1+y)^k - 1) Φ_{s-k}` gives `j! n [y^{j+1}] Φ_s ∈ ℤ`,
and Bezout combines the two. Spanning is triangularity plus a prime-by-prime gcd argument.
-/

open Polynomial

namespace StanleySnf

namespace LA

/-! ## Hurwitz-integral polynomials -/

/-- `f` is Hurwitz-integral: `t! [y^t] f ∈ ℤ` for every `t`. -/
def Hur (f : ℚ[X]) : Prop := ∀ t : ℕ, ∃ z : ℤ, (t.factorial : ℚ) * f.coeff t = z

lemma hur_of_deriv {f : ℚ[X]} (h0 : ∃ z : ℤ, f.coeff 0 = z) (hd : Hur (derivative f)) :
    Hur f := by
  intro t
  cases t with
  | zero => simpa using h0
  | succ t =>
    obtain ⟨z, hz⟩ := hd t
    refine ⟨z, ?_⟩
    rw [← hz, coeff_derivative, Nat.factorial_succ]
    push_cast
    ring

lemma hur_deriv {f : ℚ[X]} (h : Hur f) : Hur (derivative f) := by
  intro t
  obtain ⟨z, hz⟩ := h (t + 1)
  refine ⟨z, ?_⟩
  rw [← hz, coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

lemma hur_int (p : ℤ[X]) : Hur (p.map (Int.castRingHom ℚ)) := by
  intro t
  exact ⟨t.factorial * p.coeff t, by simp⟩

lemma hur_one : Hur 1 := by
  simpa using hur_int 1

lemma hur_add {f g : ℚ[X]} (hf : Hur f) (hg : Hur g) : Hur (f + g) := by
  intro t
  obtain ⟨a, ha⟩ := hf t
  obtain ⟨b, hb⟩ := hg t
  exact ⟨a + b, by rw [coeff_add, mul_add, ha, hb]; push_cast; ring⟩

lemma hur_sum {ι : Type*} (S : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ S, Hur (f i)) :
    Hur (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro t; exact ⟨0, by simp⟩
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact hur_add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma hur_mul_aux (t : ℕ) : ∀ f g : ℚ[X], Hur f → Hur g →
    ∃ z : ℤ, (t.factorial : ℚ) * (f * g).coeff t = z := by
  induction t with
  | zero =>
    intro f g hf hg
    obtain ⟨a, ha⟩ := hf 0
    obtain ⟨b, hb⟩ := hg 0
    refine ⟨a * b, ?_⟩
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul] at ha hb ⊢
    rw [mul_coeff_zero, ha, hb]
    push_cast
    ring
  | succ t ih =>
    intro f g hf hg
    obtain ⟨a, ha⟩ := ih (derivative f) g (hur_deriv hf) hg
    obtain ⟨b, hb⟩ := ih f (derivative g) hf (hur_deriv hg)
    refine ⟨a + b, ?_⟩
    have h1 : (t.factorial : ℚ) * (derivative (f * g)).coeff t
        = ((t + 1).factorial : ℚ) * (f * g).coeff (t + 1) := by
      rw [coeff_derivative, Nat.factorial_succ]
      push_cast
      ring
    rw [← h1, derivative_mul, coeff_add, mul_add, ha, hb]
    push_cast
    ring

lemma hur_mul {f g : ℚ[X]} (hf : Hur f) (hg : Hur g) : Hur (f * g) :=
  fun t => hur_mul_aux t f g hf hg

lemma hur_prod {ι : Type*} (S : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ S, Hur (f i)) :
    Hur (∏ i ∈ S, f i) :=
  Finset.prod_induction f Hur (fun _ _ => hur_mul) hur_one h

/-- Divided powers: `f^m / m!` is Hurwitz-integral if `f` is and `f(0) = 0`. -/
lemma hur_divpow {f : ℚ[X]} (hf : Hur f) (h0 : f.coeff 0 = 0) (m : ℕ) :
    Hur (C ((m.factorial : ℚ)⁻¹) * f ^ m) := by
  induction m with
  | zero => simpa using hur_one
  | succ m ih =>
    apply hur_of_deriv
    · refine ⟨0, ?_⟩
      rw [coeff_C_mul, pow_succ, mul_coeff_zero, h0]
      simp
    · have : derivative (C (((m + 1).factorial : ℚ)⁻¹) * f ^ (m + 1))
          = C ((m.factorial : ℚ)⁻¹) * f ^ m * derivative f := by
        rw [derivative_C_mul, derivative_pow_succ, Nat.factorial_succ]
        have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
        have hf' : (m.factorial : ℚ) ≠ 0 := by positivity
        rw [← mul_assoc, ← mul_assoc, ← C_mul]
        congr 3
        push_cast
        field_simp
      rw [this]
      exact hur_mul ih (hur_deriv hf)

/-! ## `Φ_s` as a product of divided powers -/

/-- `φ_k = ((1+y)^k - 1)/k`. -/
noncomputable def phi (k : ℕ) : ℚ[X] := C ((k : ℚ)⁻¹) * ((1 + X) ^ k - 1)

lemma phi_coeff_zero (k : ℕ) : (phi k).coeff 0 = 0 := by
  simp [phi, coeff_zero_eq_eval_zero]

lemma hur_phi (k : ℕ) : Hur (phi k) := by
  apply hur_of_deriv ⟨0, by rw [phi_coeff_zero]; simp⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [phi] using hur_int 0
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : derivative (phi (j + 1)) = ((1 + X) ^ j : ℤ[X]).map (Int.castRingHom ℚ) := by
      rw [phi, derivative_C_mul, derivative_sub, derivative_one, sub_zero, derivative_pow_succ]
      simp only [derivative_add, derivative_one, derivative_X, zero_add, mul_one,
        Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]
      rw [← mul_assoc, ← C_mul]
      have : ((((j + 1 : ℕ)) : ℚ)⁻¹ * ((j : ℚ) + 1)) = 1 := by
        push_cast
        field_simp
      rw [this, C_1, one_mul]
    rw [this]
    exact hur_int _

lemma zeeM_eq_prod (s : Multiset ℕ) (T : Finset ℕ) (h : s.toFinset ⊆ T) :
    zeeM s = ∏ k ∈ T, k ^ (s.count k) * (s.count k).factorial := by
  apply Finset.prod_subset h
  intro k _ hk
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hk)]
  simp

lemma PhiM_eq_prod (s : Multiset ℕ) :
    PhiM s = ∏ k ∈ s.toFinset, C (((s.count k).factorial : ℚ)⁻¹) * phi k ^ (s.count k) := by
  rw [PhiM, HM, Polynomial.map_multiset_prod, Multiset.map_map,
    Finset.prod_multiset_map_count, zeeM, Nat.cast_prod, ← Finset.prod_inv_distrib, map_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [phi, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X]
  congr 2
  push_cast
  rw [mul_inv, inv_pow]
  ring

/-- `t! [y^t] Φ_s ∈ ℤ`. -/
lemma hur_PhiM (s : Multiset ℕ) : Hur (PhiM s) := by
  rw [PhiM_eq_prod]
  exact hur_prod _ _ fun k _ => hur_divpow (hur_phi k) (phi_coeff_zero k) _

/-! ## The Euler identity -/

lemma zeeM_erase {s : Multiset ℕ} {k : ℕ} (hk : k ∈ s) :
    zeeM s = k * s.count k * zeeM (s.erase k) := by
  have hkT : k ∈ s.toFinset := Multiset.mem_toFinset.2 hk
  have h1 := zeeM_eq_prod (s.erase k) s.toFinset (fun x hx => by
      simp only [Multiset.mem_toFinset] at hx ⊢
      exact Multiset.mem_of_mem_erase hx)
  have h2 : ∏ x ∈ s.toFinset.erase k,
        x ^ ((s.erase k).count x) * ((s.erase k).count x).factorial
      = ∏ x ∈ s.toFinset.erase k, x ^ (s.count x) * (s.count x).factorial :=
    Finset.prod_congr rfl fun x hx => by
      rw [Multiset.count_erase_of_ne (Finset.ne_of_mem_erase hx)]
  rw [zeeM, h1, ← Finset.mul_prod_erase _ _ hkT, ← Finset.mul_prod_erase s.toFinset _ hkT, h2,
    Multiset.count_erase_self]
  obtain ⟨c, hc⟩ : ∃ c, s.count k = c + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Multiset.count_ne_zero.2 hk)
  rw [hc, Nat.add_sub_cancel, pow_succ, Nat.factorial_succ]
  ring

lemma HM_erase {s : Multiset ℕ} {k : ℕ} (hk : k ∈ s) :
    HM s = ((1 + X) ^ k - 1) * HM (s.erase k) := by
  conv_lhs => rw [← Multiset.cons_erase hk]
  rw [HM, HM, Multiset.map_cons, Multiset.prod_cons]

lemma zeeM_pos {s : Multiset ℕ} (hs : ∀ m ∈ s, 0 < m) : 0 < zeeM s := by
  apply Finset.prod_pos
  intro k hk
  have := hs k (Multiset.mem_toFinset.1 hk)
  positivity

lemma PhiM_erase {s : Multiset ℕ} (hs : ∀ m ∈ s, 0 < m) {k : ℕ} (hk : k ∈ s) :
    C (((k * s.count k : ℕ)) : ℚ) * PhiM s
      = ((1 + X) ^ k - 1) * PhiM (s.erase k) := by
  have hz : (zeeM (s.erase k) : ℚ) ≠ 0 := by
    have := zeeM_pos (s := s.erase k) (fun m hm => hs m (Multiset.mem_of_mem_erase hm))
    positivity
  have hk0 : (k : ℚ) ≠ 0 := by have := hs k hk; positivity
  have hc0 : (s.count k : ℚ) ≠ 0 := by
    have := Multiset.count_pos.2 hk
    positivity
  have key : ((k * s.count k : ℕ) : ℚ) * ((zeeM s : ℕ) : ℚ)⁻¹ = ((zeeM (s.erase k) : ℕ) : ℚ)⁻¹ := by
    rw [zeeM_erase hk]
    push_cast
    field_simp
  rw [PhiM, PhiM, HM_erase hk, ← mul_assoc, ← C_mul, key]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X]
  ring

/-- Euler identity: `n Φ_s = ∑_k ((1+y)^k - 1) Φ_{s-k}`, `n = ∑ s`. -/
lemma PhiM_euler {s : Multiset ℕ} (hs : ∀ m ∈ s, 0 < m) :
    C ((s.sum : ℕ) : ℚ) * PhiM s
      = ∑ k ∈ s.toFinset, ((1 + X) ^ k - 1) * PhiM (s.erase k) := by
  rw [Finset.sum_multiset_count s, Nat.cast_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← PhiM_erase hs (Multiset.mem_toFinset.1 hk), smul_eq_mul, mul_comm (s.count k)]

/-- `(1+y)^k - 1 = y ∑_{i<k} (1+y)^i`. -/
lemma one_add_X_pow_sub_one (k : ℕ) :
    ((1 + X) ^ k - 1 : ℚ[X])
      = X * (∑ i ∈ Finset.range k, (1 + X) ^ i : ℤ[X]).map (Int.castRingHom ℚ) := by
  have := geom_sum_mul (1 + X : ℚ[X]) k
  rw [add_sub_cancel_left] at this
  rw [← this, Polynomial.map_sum]
  simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]
  ring

/-- `j! n [y^{j+1}] Φ_s ∈ ℤ`. -/
lemma euler_int {s : Multiset ℕ} (hs : ∀ m ∈ s, 0 < m) (j : ℕ) :
    ∃ z : ℤ, (j.factorial : ℚ) * (s.sum : ℚ) * (PhiM s).coeff (j + 1) = z := by
  have hF : Hur (∑ k ∈ s.toFinset, (∑ i ∈ Finset.range k, (1 + X) ^ i : ℤ[X]).map
      (Int.castRingHom ℚ) * PhiM (s.erase k)) :=
    hur_sum _ _ fun k _ => hur_mul (hur_int _) (hur_PhiM _)
  obtain ⟨z, hz⟩ := hF j
  refine ⟨z, ?_⟩
  have h := congrArg (fun p : ℚ[X] => p.coeff (j + 1)) (PhiM_euler hs)
  simp only [coeff_C_mul] at h
  rw [mul_assoc, h, ← hz]
  simp_rw [one_add_X_pow_sub_one, mul_assoc]
  rw [← Finset.mul_sum, coeff_X_mul]

end LA

/-- Integrality: `e_s [y^{s+1}] Φ_ν ∈ ℤ`. -/
theorem alpha_int {n : ℕ} (hn : 0 < n) (s : Fin n) (ν : n.Partition) :
    ∃ z : ℤ, alphaQ n s ν = z := by
  obtain ⟨z1, hz1⟩ := LA.hur_PhiM ν.parts ((s : ℕ) + 1)
  obtain ⟨z2, hz2⟩ := LA.euler_int (fun m hm => ν.parts_pos hm) (s : ℕ)
  rw [ν.parts_sum] at hz2
  obtain ⟨e, he⟩ : ∃ e : ℤ, (eps ν : ℚ) = e := ⟨eps ν, rfl⟩
  refine ⟨e * (Nat.gcdA n ((s : ℕ) + 1) * z2 + Nat.gcdB n ((s : ℕ) + 1) * z1), ?_⟩
  have hg := Nat.gcd_eq_gcd_ab n ((s : ℕ) + 1)
  have hg' : ((Nat.gcd n ((s : ℕ) + 1) : ℤ) : ℚ)
      = ((n : ℤ) * Nat.gcdA n ((s : ℕ) + 1) + (((s : ℕ) + 1 : ℕ) : ℤ) * Nat.gcdB n ((s : ℕ) + 1)
        : ℤ) := by rw [hg]
  push_cast at hg' hz1 hz2 ⊢
  rw [alphaQ, ee, he, ← hz1, ← hz2, Nat.factorial_succ]
  push_cast
  rw [hg']
  ring

namespace LA

/-! ## The lowest coefficient of `Φ_s` -/

/-- `H_s = y^{|s|} G_s` with `G_s = ∏_i ∑_{j < s_i} (1+y)^j`. -/
lemma HM_eq (s : Multiset ℕ) :
    HM s = (s.map fun m => ∑ i ∈ Finset.range m, (1 + X : ℤ[X]) ^ i).prod * X ^ s.card := by
  have h : ∀ m : ℕ, ((1 + X : ℤ[X]) ^ m - 1) = (∑ i ∈ Finset.range m, (1 + X) ^ i) * X := by
    intro m
    have := geom_sum_mul (1 + X : ℤ[X]) m
    rw [add_sub_cancel_left] at this
    exact this.symm
  rw [HM, Multiset.map_congr rfl (fun m _ => h m), Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate]

lemma PhiM_coeff (s : Multiset ℕ) (t : ℕ) :
    (PhiM s).coeff t = (zeeM s : ℚ)⁻¹ *
      (if s.card ≤ t then
        (((s.map fun m => ∑ i ∈ Finset.range m, (1 + X : ℤ[X]) ^ i).prod.coeff (t - s.card) : ℤ)
          : ℚ)
       else 0) := by
  rw [PhiM, coeff_C_mul, HM_eq, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    coeff_mul_X_pow', coeff_map]
  split_ifs <;> simp

lemma PhiM_coeff_lt (s : Multiset ℕ) {t : ℕ} (ht : t < s.card) : (PhiM s).coeff t = 0 := by
  rw [PhiM_coeff, if_neg (by omega), mul_zero]

lemma PhiM_coeff_card (s : Multiset ℕ) :
    (PhiM s).coeff s.card = (zeeM s : ℚ)⁻¹ * (s.prod : ℚ) := by
  rw [PhiM_coeff, if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero, eval_multiset_prod,
    Multiset.map_map]
  congr 1
  have : ((Polynomial.eval 0 ∘ fun m => ∑ i ∈ Finset.range m, (1 + X : ℤ[X]) ^ i))
      = fun m : ℕ => (m : ℤ) := by
    funext m
    simp [eval_finsetSum]
  rw [this, ← Nat.cast_multiset_prod (s := s)]
  simp

/-! ## Partitions with two distinct part sizes -/

/-- The partition `(A^a, B^b)` of `n`. -/
def twoPart (n A a B b : ℕ) (hA : 0 < A) (hB : 0 < B) (h : a * A + b * B = n) :
    n.Partition where
  parts := Multiset.replicate a A + Multiset.replicate b B
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.1 hi with hi | hi
    · rw [Multiset.eq_of_mem_replicate hi]; exact hA
    · rw [Multiset.eq_of_mem_replicate hi]; exact hB
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate, smul_eq_mul,
      smul_eq_mul, h]

lemma twoPart_coeff {A a B b : ℕ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≠ B) :
    (PhiM (Multiset.replicate a A + Multiset.replicate b B)).coeff (a + b)
      = ((a.factorial * b.factorial : ℕ) : ℚ)⁻¹ := by
  have hc : (Multiset.replicate a A + Multiset.replicate b B).card = a + b := by simp
  rw [← hc, PhiM_coeff_card, zeeM_eq_prod _ {A, B} (fun x hx => by
      simp only [Multiset.mem_toFinset, Multiset.mem_add] at hx
      rcases hx with hx | hx <;> simp [Multiset.eq_of_mem_replicate hx]),
    Finset.prod_pair hAB, Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate]
  simp only [Multiset.count_add, Multiset.count_replicate_self, Multiset.count_replicate,
    if_neg hAB, if_neg (Ne.symm hAB), add_zero, zero_add]
  have : (A : ℚ) ≠ 0 := by positivity
  have : (B : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ## The integer vectors `α(ν)` and their span -/

/-- `α(ν)` as an integer vector. -/
noncomputable def alphaZ {n : ℕ} (hn : 0 < n) (ν : n.Partition) : Fin n → ℤ :=
  fun t => (alpha_int hn t ν).choose

lemma alphaZ_spec {n : ℕ} (hn : 0 < n) (ν : n.Partition) (t : Fin n) :
    ((alphaZ hn ν t : ℤ) : ℚ) = alphaQ n t ν :=
  (alpha_int hn t ν).choose_spec.symm

/-- The integer span of the `α(ν)`. -/
noncomputable def Lsp {n : ℕ} (hn : 0 < n) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range (alphaZ hn))

/-- The `s`-th coordinates of vectors of the span that vanish below `s`. -/
def Jd {n : ℕ} (hn : 0 < n) (s : Fin n) : Ideal ℤ where
  carrier := {z | ∃ w ∈ Lsp hn, (∀ t, t < s → w t = 0) ∧ w s = z}
  add_mem' := by
    rintro a b ⟨w1, h1, h1', rfl⟩ ⟨w2, h2, h2', rfl⟩
    exact ⟨w1 + w2, add_mem h1 h2, fun t ht => by simp [h1' t ht, h2' t ht], by simp⟩
  zero_mem' := ⟨0, zero_mem _, fun _ _ => rfl, rfl⟩
  smul_mem' := by
    rintro c a ⟨w, h, h', rfl⟩
    exact ⟨c • w, Submodule.smul_mem _ c h, fun t ht => by simp [h' t ht], by simp⟩

lemma eps_mul_self {n : ℕ} (ν : n.Partition) : eps ν * eps ν = 1 := by
  rw [eps, ← mul_pow]
  simp

/-- A two-part partition with `s + 1` parts puts `s! gcd(n, s+1) / (a! b!)` into `Jd s`. -/
lemma twoPart_mem {n : ℕ} (hn : 0 < n) (s : Fin n) {A a B b : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≠ B) (h : a * A + b * B = n) (hab : a + b = (s : ℕ) + 1) (X : ℕ)
    (hX : (s : ℕ).factorial * Nat.gcd n ((s : ℕ) + 1) = X * (a.factorial * b.factorial)) :
    (X : ℤ) ∈ Jd hn s := by
  set ν := twoPart n A a B b hA hB h
  have hcard : ν.parts.card = (s : ℕ) + 1 := by simp [ν, twoPart, hab]
  have hw : ((alphaZ hn ν s : ℤ) : ℚ) = (eps ν : ℚ) * X := by
    rw [alphaZ_spec, alphaQ, ee, ← hab]
    simp only [ν, twoPart]
    rw [twoPart_coeff hA hB hAB, hab]
    have : ((a.factorial * b.factorial : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hX]
    push_cast
    field_simp
  have hmem : eps ν * alphaZ hn ν s ∈ Jd hn s := by
    refine Ideal.mul_mem_left _ _ ⟨alphaZ hn ν, Submodule.subset_span ⟨ν, rfl⟩, ?_, rfl⟩
    intro t ht
    have : alphaQ n t ν = 0 := by
      rw [alphaQ, PhiM_coeff_lt _ (by rw [hcard]; exact Nat.add_lt_add_right ht 1), mul_zero]
    exact_mod_cast (alphaZ_spec hn ν t).trans this
  convert hmem using 1
  have h1 : ((eps ν * alphaZ hn ν s : ℤ) : ℚ) = (X : ℚ) := by
    push_cast
    rw [hw, ← mul_assoc]
    exact_mod_cast (by rw [eps_mul_self, one_mul] : (eps ν * eps ν * X : ℤ) = X)
  exact_mod_cast h1.symm

/-- An ideal of `ℤ` not contained in any `pℤ` is `ℤ`. -/
lemma one_mem_of_forall_prime (I : Ideal ℤ) (h : ∀ p : ℕ, p.Prime → ∃ x ∈ I, ¬ (p : ℤ) ∣ x) :
    (1 : ℤ) ∈ I := by
  obtain ⟨d, hd⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ x, x ∈ I ↔ d ∣ x := fun x => by
    rw [hd]
    exact Ideal.mem_span_singleton
  rw [hmem]
  by_cases hd1 : d.natAbs = 1
  · exact isUnit_iff_dvd_one.1 (Int.isUnit_iff_natAbs_eq.2 hd1)
  · obtain ⟨p, hp, hpd⟩ := Int.exists_prime_and_dvd hd1
    obtain ⟨x, hx, hpx⟩ := h p.natAbs (Int.prime_iff_natAbs_prime.1 hp)
    exact absurd (Int.natAbs_dvd.2 (hpd.trans ((hmem x).1 hx))) hpx

/-- Lucas: `C(c p^v - 1, p^v - 1) ≡ 1 (mod p)`. -/
lemma choose_modEq_one (p : ℕ) [hp : Fact p.Prime] (v : ℕ) :
    ∀ c : ℕ, 1 ≤ c → Nat.choose (c * p ^ v - 1) (p ^ v - 1) ≡ 1 [MOD p] := by
  have hp2 := hp.out.two_le
  induction v with
  | zero =>
    intro c _
    simp
    rfl
  | succ v ih =>
    intro c hc
    have hY : 1 ≤ c * p ^ v := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hq : 1 ≤ p ^ v := Nat.one_le_iff_ne_zero.2 (by positivity)
    have key : ∀ Y : ℕ, 1 ≤ Y → p * Y - 1 = p * (Y - 1) + (p - 1) := by
      intro Y hY1
      obtain ⟨Y', rfl⟩ : ∃ Y', Y = Y' + 1 := ⟨Y - 1, by omega⟩
      rw [mul_add, mul_one, Nat.add_sub_cancel]
      omega
    rw [show c * p ^ (v + 1) = p * (c * p ^ v) by ring, pow_succ, mul_comm (p ^ v) p,
      key _ hY, key _ hq]
    refine (Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p)).trans ?_
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mul_add_div (by omega),
      Nat.mul_add_div (by omega), Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega),
      Nat.choose_self, one_mul, add_zero]
    exact ih c hc

lemma arith_last (r n : ℕ) (h : r + 1 = n) :
    r.factorial * Nat.gcd n (r + 1) = 1 * (Nat.factorial 0 * n.factorial) := by
  subst h
  rw [Nat.gcd_self, Nat.factorial_succ]
  simp
  ring

lemma arith_q (r q g : ℕ) (hq : 1 ≤ q) (hqr : q ≤ r + 1) (hqg : q ∣ g) :
    r.factorial * g = (Nat.choose r (q - 1) * (g / q)) * (q.factorial * (r + 1 - q).factorial) := by
  obtain ⟨g', rfl⟩ := hqg
  have h := Nat.choose_mul_factorial_mul_factorial (n := r) (k := q - 1) (by omega)
  rw [Nat.mul_div_cancel_left g' (by omega), ← Nat.mul_factorial_pred (by omega : q ≠ 0), ← h,
    show r - (q - 1) = r + 1 - q by omega]
  ring

/-- For every `s`, some vector of the span vanishes below `s` and is `1` at `s`. -/
lemma one_mem_Jd {n : ℕ} (hn : 0 < n) (s : Fin n) : (1 : ℤ) ∈ Jd hn s := by
  have hs := s.isLt
  by_cases hl : (s : ℕ) + 1 = n
  · exact_mod_cast twoPart_mem hn s (A := 2) (a := 0) (B := 1) (b := n) (by norm_num)
      (by norm_num) (by norm_num) (by simp) (by omega) 1 (arith_last _ _ hl)
  have hl' : (s : ℕ) + 1 < n := by omega
  set l := (s : ℕ) + 1 with hl_def
  set g := Nat.gcd n l with hg_def
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  apply one_mem_of_forall_prime
  intro p hp
  by_cases hpg : p ∣ g
  · haveI := Fact.mk hp
    set v := g.factorization p
    set q := p ^ v with hq_def
    have hv : 0 < v := hp.factorization_pos_of_dvd hg0 hpg
    have hqg : q ∣ g := Nat.ordProj_dvd g p
    have hqn : q ∣ n := hqg.trans (Nat.gcd_dvd_left n l)
    have hql : q ∣ l := hqg.trans (Nat.gcd_dvd_right n l)
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)
    have hqle : q ≤ l := Nat.le_of_dvd (by omega) hql
    have hqnl : q ∣ n - l := Nat.dvd_sub hqn hql
    have hdiv : 1 ≤ (n - l) / q := (Nat.le_div_iff_mul_le (by omega)).2
      (by rw [one_mul]; exact Nat.le_of_dvd (by omega) hqnl)
    have hmem := twoPart_mem hn s (A := (n - l) / q + 1) (a := q) (B := 1) (b := l - q)
      (by omega) (by norm_num) (by omega)
      (by rw [mul_comm q, add_mul, one_mul, Nat.div_mul_cancel hqnl]; omega) (by omega)
      (Nat.choose (s : ℕ) (q - 1) * (g / q)) (arith_q _ _ _ hq1 hqle hqg)
    refine ⟨_, hmem, ?_⟩
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · have hc : 1 ≤ l / q := (Nat.le_div_iff_mul_le (by omega)).2
        (by rw [one_mul]; exact hqle)
      have hL := choose_modEq_one p v (l / q) hc
      rw [Nat.div_mul_cancel hql, show l - 1 = (s : ℕ) by omega] at hL
      unfold Nat.ModEq at hL
      rw [(Nat.dvd_iff_mod_eq_zero ..).1 h, Nat.mod_eq_of_lt hp.one_lt] at hL
      exact absurd hL (by norm_num)
    · exact Nat.not_dvd_ordCompl hp hg0 h
  · refine ⟨g, ?_, by rwa [Int.natCast_dvd_natCast]⟩
    exact twoPart_mem hn s (A := n - l + 1) (a := 1) (B := 1) (b := (s : ℕ)) (by omega)
      (by norm_num) (by omega) (by omega) (by omega) g (by simp; ring)

/-- Triangularity: vectors vanishing below `n - k` lie in the span. -/
lemma mem_Lsp {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∀ v : Fin n → ℤ, (∀ t : Fin n, (t : ℕ) < n - k → v t = 0) → v ∈ Lsp hn := by
  induction k with
  | zero =>
    intro v hv
    have : v = 0 := funext fun t => hv t (by have := t.isLt; omega)
    rw [this]
    exact zero_mem _
  | succ k ih =>
    intro v hv
    by_cases hk : n ≤ k
    · exact ih v fun t ht => hv t (by omega)
    set s : Fin n := ⟨n - (k + 1), by omega⟩
    obtain ⟨w, hwL, hw0, hw1⟩ : ∃ w ∈ Lsp hn, (∀ t, t < s → w t = 0) ∧ w s = 1 :=
      one_mem_Jd hn s
    have hrest : v - v s • w ∈ Lsp hn := by
      apply ih
      intro t ht
      rcases Nat.lt_or_ge (t : ℕ) (n - (k + 1)) with h | h
      · have ht' : t < s := by rw [Fin.lt_def]; exact h
        simp [hv t h, hw0 t ht']
      · have : t = s := Fin.ext (by simp [s]; omega)
        subst this
        simp [hw1]
    have : v = (v - v s • w) + v s • w := by abel
    rw [this]
    exact add_mem hrest (Submodule.smul_mem _ _ hwL)

end LA

/-- Spanning: every integer vector is an integer combination of the `α(ν)`. -/
theorem alpha_surj {n : ℕ} (hn : 0 < n) (v : Fin n → ℤ) :
    ∃ f : n.Partition → ℤ, ∀ t : Fin n, ∑ ν, (f ν : ℚ) * alphaQ n t ν = v t := by
  have hv := LA.mem_Lsp hn n v (fun t ht => by omega)
  rw [LA.Lsp, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  refine ⟨c, fun t => ?_⟩
  rw [← hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [LA.alphaZ_spec]

end StanleySnf
