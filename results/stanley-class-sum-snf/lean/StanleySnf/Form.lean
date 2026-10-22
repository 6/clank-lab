import StanleySnf.Core

/-!
# The bridge in the `y`-basis
-/

open Polynomial

namespace StanleySnf

namespace Fm

theorem card_pos {n : ℕ} (hn : 0 < n) (μ : n.Partition) : 0 < μ.parts.card := by
  rw [Multiset.card_pos]
  intro h
  have := μ.parts_sum
  rw [h, Multiset.sum_zero] at this
  omega

theorem coeff_X_sub_one_pow (i k : ℕ) :
    ((X - 1 : ℤ[X]) ^ i).coeff k = (-1) ^ (i - k) * (i.choose k : ℤ) := by
  have : (X - 1 : ℤ[X]) = X + C (-1) := by rw [map_neg, map_one, sub_eq_add_neg]
  rw [this, coeff_X_add_C_pow]

theorem fact_choose (N j k : ℕ) (hj : j ≤ N) (hk : k ≤ N) :
    k.factorial * j.choose k * (N - k).factorial =
      j.factorial * (N - j).factorial * (N - k).choose (N - j) := by
  rcases le_or_gt k j with hkj | hkj
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hkj
    by_cases hN : k + a ≤ N
    · apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos a)
      have e1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k a)
      have e2 := Nat.choose_mul_factorial_mul_factorial
        (show N - (k + a) ≤ N - k by omega)
      rw [show N - k - (N - (k + a)) = a by omega] at e2
      rw [Nat.add_sub_cancel_left] at e1
      calc k.factorial * (k + a).choose k * (N - k).factorial * a.factorial
          = ((k + a).choose k * k.factorial * a.factorial) * (N - k).factorial := by ring
        _ = (k + a).factorial * ((N - k).choose (N - (k + a)) * (N - (k + a)).factorial *
              a.factorial) := by rw [e1, e2]
        _ = _ := by ring
    · omega
  · rw [Nat.choose_eq_zero_of_lt hkj, Nat.choose_eq_zero_of_lt (by omega : N - k < N - j)]
    simp

theorem alt_sum (N i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (i.choose k : ℤ) * ((N - k).choose (N - j) : ℤ) =
      ((N - i).choose j : ℤ) := by
  have hP : ∑ k ∈ Finset.range (N + 1),
      C ((-1 : ℤ) ^ k * (i.choose k : ℤ)) * (X + 1 : ℤ[X]) ^ (N - k) =
      X ^ i * (X + 1) ^ (N - i) := by
    rw [← Finset.sum_subset (Finset.range_mono (by omega : i + 1 ≤ N + 1))]
    · have hb := add_pow (-1 : ℤ[X]) (X + 1) i
      rw [show (-1 + (X + 1) : ℤ[X]) = X by ring] at hb
      rw [hb, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show N - k = (i - k) + (N - i) by omega, pow_add]
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
      ring
    · intro k _ hk
      have : i < k := by simpa using hk
      rw [Nat.choose_eq_zero_of_lt this]
      simp
  have hc := congrArg (fun p => p.coeff (N - j)) hP
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow, coeff_X_pow_mul'] at hc
  rw [hc]
  split_ifs with h
  · rw [Nat.choose_symm_of_eq_add (by omega : N - i = (N - j - i) + j)]
  · rw [Nat.choose_eq_zero_of_lt (by omega : N - i < j), Nat.cast_zero]

end Fm

/-- `hookPoly μ` is the generating function `∏_i (1 - (-q)^{μ_i}) / (1 + q)`. -/
theorem hookPoly_mul {n : ℕ} (hn : 0 < n) (μ : n.Partition) :
    hookPoly μ * (1 + X) = (μ.parts.map fun m => 1 - (-X : ℤ[X]) ^ m).prod := by
  have hc := Fm.card_pos hn μ
  unfold hookPoly
  calc (1 + X) ^ (μ.parts.card - 1) * (μ.parts.map fun m => ∑ a ∈ Finset.range m, (-X) ^ a).prod
        * (1 + X)
      = (μ.parts.map fun _ => (1 + X : ℤ[X])).prod *
          (μ.parts.map fun m => ∑ a ∈ Finset.range m, (-X : ℤ[X]) ^ a).prod := by
        rw [Multiset.map_const', Multiset.prod_replicate, mul_right_comm, ← pow_succ,
          Nat.sub_add_cancel hc]
    _ = (μ.parts.map fun m => (1 + X) * ∑ a ∈ Finset.range m, (-X : ℤ[X]) ^ a).prod := by
        rw [Multiset.prod_map_mul]
    _ = _ := by
        congr 1
        refine Multiset.map_congr rfl fun m _ => ?_
        have := mul_neg_geom_sum (-X : ℤ[X]) m
        rwa [sub_neg_eq_add] at this

/-- Lemma 2.1: `g_μ(1+y) = ε_μ H_μ(y)/y`, with `g_μ(x) = hookPoly μ (-x)`. -/
theorem hookPoly_comp {n : ℕ} (hn : 0 < n) (μ : n.Partition) :
    X * (hookPoly μ).comp (-1 - X) = C (eps μ) * HM μ.parts := by
  have hc := Fm.card_pos hn μ
  simp only [hookPoly, HM, eps, mul_comp, pow_comp, add_comp, one_comp, X_comp,
    multiset_prod_comp, Multiset.map_map, Function.comp_def, sum_comp, neg_comp]
  have h1 : (1 + (-1 - X) : ℤ[X]) = -X := by ring
  have h2 : (-(-1 - X) : ℤ[X]) = 1 + X := by ring
  rw [h1, h2]
  calc X * ((-X) ^ (μ.parts.card - 1) *
        (μ.parts.map fun m => ∑ a ∈ Finset.range m, (1 + X : ℤ[X]) ^ a).prod)
      = C ((-1) ^ (μ.parts.card - 1)) * ((μ.parts.map fun _ => (X : ℤ[X])).prod *
        (μ.parts.map fun m => ∑ a ∈ Finset.range m, (1 + X : ℤ[X]) ^ a).prod) := by
        rw [Multiset.map_const', Multiset.prod_replicate, map_pow, map_neg, map_one]
        obtain ⟨c, hc'⟩ : ∃ c, μ.parts.card = c + 1 := ⟨_, (Nat.sub_add_cancel hc).symm⟩
        rw [hc', Nat.add_sub_cancel]
        ring
    _ = _ := by
        rw [← Multiset.prod_map_mul]
        congr 2
        refine Multiset.map_congr rfl fun m _ => ?_
        have := geom_sum_mul (1 + X : ℤ[X]) m
        rw [add_sub_cancel_left] at this
        rw [mul_comm, this]

/-- Lemma 2.2: the form `∑_k (-1)^k k! (N-k)! g_k g'_k` on the basis `(x-1)^i`. -/
theorem binom_form (N i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    ∑ k ∈ Finset.range (N + 1),
      (-1 : ℤ) ^ k * (k.factorial : ℤ) * ((N - k).factorial : ℤ) *
        ((X - 1 : ℤ[X]) ^ i).coeff k * ((X - 1 : ℤ[X]) ^ j).coeff k = Qf N i j := by
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (-1 : ℤ) ^ k * (k.factorial : ℤ) * ((N - k).factorial : ℤ) *
        ((X - 1 : ℤ[X]) ^ i).coeff k * ((X - 1 : ℤ[X]) ^ j).coeff k =
      (-1) ^ (i + j) * ((j.factorial * (N - j).factorial : ℕ) : ℤ) *
        ((-1 : ℤ) ^ k * (i.choose k : ℤ) * ((N - k).choose (N - j) : ℤ)) := by
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hf : ((k.factorial * j.choose k * (N - k).factorial : ℕ) : ℤ) =
        ((j.factorial * (N - j).factorial * (N - k).choose (N - j) : ℕ) : ℤ) := by
      rw [Fm.fact_choose N j k hj hkN]
    push_cast at hf
    rw [Fm.coeff_X_sub_one_pow, Fm.coeff_X_sub_one_pow]
    rcases le_or_gt k i with hki | hki
    · rcases le_or_gt k j with hkj | hkj
      · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hki
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hkj
        have hs : (-1 : ℤ) ^ (k + a + (k + b)) = (-1) ^ a * (-1) ^ b := by
          rw [show k + a + (k + b) = 2 * k + (a + b) by ring, pow_add, pow_mul, neg_one_sq,
            one_pow, one_mul, pow_add]
        rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, hs]
        push_cast
        linear_combination ((-1 : ℤ) ^ k * (-1) ^ a * (-1) ^ b * ((k + a).choose k : ℤ)) * hf
      · rw [Nat.choose_eq_zero_of_lt hkj, Nat.choose_eq_zero_of_lt (by omega : N - k < N - j)]
        simp
    · rw [Nat.choose_eq_zero_of_lt hki]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Fm.alt_sum N i j hi hj, Qf]
  push_cast
  ring

namespace Fm

theorem HM_natDegree {n : ℕ} (μ : n.Partition) : (HM μ.parts).natDegree ≤ n := by
  unfold HM
  refine (natDegree_multiset_prod_le _).trans ?_
  rw [Multiset.map_map]
  calc (μ.parts.map (natDegree ∘ fun m => (1 + X : ℤ[X]) ^ m - 1)).sum
      ≤ (μ.parts.map fun m => m).sum := by
        refine Multiset.sum_map_le_sum_map _ _ fun m _ => ?_
        simp only [Function.comp_apply]
        compute_degree
    _ = n := by rw [Multiset.map_id', μ.parts_sum]

theorem HM_coeff_zero {n : ℕ} (hn : 0 < n) (μ : n.Partition) : (HM μ.parts).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, HM, eval_multiset_prod, Multiset.map_map]
  apply Multiset.prod_eq_zero
  obtain ⟨m, hm⟩ := Multiset.card_pos_iff_exists_mem.mp (card_pos hn μ)
  refine Multiset.mem_map.mpr ⟨m, hm, ?_⟩
  simp

theorem HM_eq {n : ℕ} (hn : 0 < n) (μ : n.Partition) :
    HM μ.parts = X * ∑ i ∈ Finset.range n, C (eta μ i) * X ^ i := by
  rw [as_sum_range' (HM μ.parts) (n + 1) (Nat.lt_succ_of_le (HM_natDegree μ)),
    Finset.sum_range_succ', HM_coeff_zero hn μ, map_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eta, ← C_mul_X_pow_eq_monomial, pow_succ]
  ring

theorem hookPoly_eq {n : ℕ} (hn : 0 < n) (μ : n.Partition) :
    hookPoly μ = C (eps μ) * ∑ i ∈ Finset.range n, C (eta μ i) * (-1 - X) ^ i := by
  have h := hookPoly_comp hn μ
  rw [HM_eq hn μ, mul_left_comm] at h
  have h' := mul_left_cancel₀ X_ne_zero h
  have hinv : (-1 - X : ℤ[X]).comp (-1 - X) = X := by
    simp only [sub_comp, neg_comp, one_comp, X_comp]
    ring
  calc hookPoly μ = ((hookPoly μ).comp (-1 - X)).comp (-1 - X) := by
        rw [comp_assoc, hinv, comp_X]
    _ = _ := by
        rw [h']
        simp only [mul_comp, C_comp, sum_comp, pow_comp, X_comp]

theorem coeff_neg_one_sub_X_pow (i k : ℕ) :
    ((-1 - X : ℤ[X]) ^ i).coeff k = (-1) ^ k * ((X - 1 : ℤ[X]) ^ i).coeff k := by
  have h : (-1 - X : ℤ[X]) ^ i = C ((-1) ^ i) * (X + C 1) ^ i := by
    rw [map_pow, ← mul_pow, map_neg, map_one]
    ring
  rw [h, coeff_C_mul, coeff_X_add_C_pow, coeff_X_sub_one_pow, one_pow, one_mul]
  rcases le_or_gt k i with hki | hki
  · rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hki]
  · rw [Nat.choose_eq_zero_of_lt hki]
    simp

theorem hookChar_eq {n : ℕ} (hn : 0 < n) (μ : n.Partition) (k : ℕ) :
    hookChar k μ = eps μ * (-1) ^ k *
      ∑ i : Fin n, eta μ i * ((X - 1 : ℤ[X]) ^ (i : ℕ)).coeff k := by
  rw [hookChar, hookPoly_eq hn μ, coeff_C_mul, finsetSum_coeff,
    Fin.sum_univ_eq_sum_range (fun i => eta μ i * ((X - 1 : ℤ[X]) ^ i).coeff k)]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_C_mul, coeff_neg_one_sub_X_pow]
  ring

theorem form_sum (n : ℕ) (a b : ℕ → ℤ) :
    ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * (k.factorial : ℤ) * ((n - 1 - k).factorial : ℤ) *
      (∑ i : Fin n, a i * ((X - 1 : ℤ[X]) ^ (i : ℕ)).coeff k) *
      (∑ s : Fin n, b s * ((X - 1 : ℤ[X]) ^ (s : ℕ)).coeff k) =
    ∑ i : Fin n, ∑ s : Fin n, a i * Qf (n - 1) i s * b s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hQ : ∀ i s : Fin n, Qf (n - 1) i s = ∑ k ∈ Finset.range n,
      (-1 : ℤ) ^ k * (k.factorial : ℤ) * ((n - 1 - k).factorial : ℤ) *
        ((X - 1 : ℤ[X]) ^ (i : ℕ)).coeff k * ((X - 1 : ℤ[X]) ^ (s : ℕ)).coeff k := by
    intro i s
    rw [← binom_form (n - 1) i s (by omega) (by omega), Nat.sub_add_cancel hn]
  set c : ℕ → ℕ → ℤ := fun k i => ((X - 1 : ℤ[X]) ^ i).coeff k with hc
  set w : ℕ → ℤ := fun k => (-1 : ℤ) ^ k * (k.factorial : ℤ) * ((n - 1 - k).factorial : ℤ)
    with hw
  calc ∑ k ∈ Finset.range n, w k * (∑ i : Fin n, a i * c k i) * (∑ s : Fin n, b s * c k s)
      = ∑ k ∈ Finset.range n, ∑ i : Fin n, ∑ s : Fin n, a i * (w k * c k i * c k s) * b s := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum Finset.univ (fun i : Fin n => a i * c k i) (w k), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ i : Fin n, ∑ k ∈ Finset.range n, ∑ s : Fin n, a i * (w k * c k i * c k s) * b s :=
        Finset.sum_comm
    _ = ∑ i : Fin n, ∑ s : Fin n, ∑ k ∈ Finset.range n, a i * (w k * c k i * c k s) * b s :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
        rw [hQ, Finset.mul_sum, Finset.sum_mul]

end Fm

/-- Corollary 2.3: the classical formula, rewritten in the `y`-basis. -/
theorem bridge_y {n : ℕ} (hn : 0 < n) (μ ν : n.Partition) :
    bridgeFormula n μ ν =
      (eps μ : ℚ) * (eps ν : ℚ) / (zee ν : ℚ) *
        ∑ i : Fin n, ∑ s : Fin n, ((eta μ i * Qf (n - 1) i s * eta ν s : ℤ) : ℚ) := by
  set A : ℕ → n.Partition → ℤ :=
    fun k ρ => ∑ i : Fin n, eta ρ i * ((X - 1 : ℤ[X]) ^ (i : ℕ)).coeff k with hA
  have hF := Fm.form_sum n (eta μ) (eta ν)
  set t : ℕ → ℤ := fun k =>
    (-1 : ℤ) ^ k * (k.factorial : ℤ) * ((n - 1 - k).factorial : ℤ) * A k μ * A k ν with ht
  have hterm : ∀ k ∈ Finset.range n,
      ((n - 1).factorial : ℚ) *
        ((-1 : ℚ) ^ k * hookChar k ν * hookChar k μ / ((n - 1).choose k : ℚ)) =
      (eps μ : ℚ) * (eps ν : ℚ) * (t k : ℚ) := by
    intro k hk
    have hkN : k ≤ n - 1 := by have := Finset.mem_range.mp hk; omega
    have hfac : ((n - 1).factorial : ℚ) =
        ((n - 1).choose k : ℚ) * k.factorial * (n - 1 - k).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hkN).symm
    have hC : ((n - 1).choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkN).ne'
    have hs : ((-1 : ℚ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [Fm.hookChar_eq hn ν k, Fm.hookChar_eq hn μ k, hfac]
    simp only [ht, hA]
    push_cast
    field_simp
    rw [hs, one_mul]
  calc bridgeFormula n μ ν
      = (1 / zee ν : ℚ) * ∑ k ∈ Finset.range n, ((n - 1).factorial : ℚ) *
          ((-1 : ℚ) ^ k * hookChar k ν * hookChar k μ / ((n - 1).choose k : ℚ)) := by
        rw [bridgeFormula, ← Finset.mul_sum]
        ring
    _ = (eps μ : ℚ) * (eps ν : ℚ) / (zee ν : ℚ) * (((Finset.range n).sum t : ℤ) : ℚ) := by
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Int.cast_sum]
        ring
    _ = _ := by
        rw [hF, Int.cast_sum]
        simp_rw [Int.cast_sum]

/-- The factorisation `M = E Γ α` (given the classical bridge). -/
theorem M_factor {n : ℕ} (hn : 0 < n)
    (hB : ∀ μ ν : n.Partition, (M n μ ν : ℚ) = bridgeFormula n μ ν) (μ ν : n.Partition) :
    (M n μ ν : ℚ) = (eps μ : ℚ) * ∑ s : Fin n, GamQ n μ s * alphaQ n s ν := by
  have hPhi : ∀ s : ℕ, (PhiM ν.parts).coeff (s + 1) = (eta ν s : ℚ) / (zee ν : ℚ) := by
    intro s
    rw [PhiM, coeff_C_mul, coeff_map, eta, zee, eq_intCast, div_eq_inv_mul]
  have hz : (zee ν : ℚ) ≠ 0 := by
    rw [zee, zeeM, Nat.cast_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
    have hk0 : 0 < k := ν.parts_pos (Multiset.mem_toFinset.mp hk)
    exact Nat.mul_ne_zero (pow_ne_zero _ hk0.ne') (Nat.factorial_ne_zero _)
  rw [hB, bridge_y hn, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have he : (ee n s : ℚ) ≠ 0 := by
    rw [ee, Nat.cast_ne_zero]
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero _)
      (Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _)).ne'
  simp only [GamQ, alphaQ, hPhi]
  have hsum : ∑ i : Fin n, ((eta μ i * Qf (n - 1) i s * eta ν s : ℤ) : ℚ) =
      (∑ i : Fin n, ((eta μ i * Qf (n - 1) i s : ℤ) : ℚ)) * (eta ν s : ℚ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [hsum]
  field_simp

end StanleySnf
