import StanleySnf.Core

/-!
# Lemma C (row divisibility), the anti-diagonal, and the divisor chain
-/

open Polynomial

namespace StanleySnf

namespace LC

/-- `gcd(n,r) ∣ a_r r!`, so `δ_r` is an exact quotient. -/
theorem gcd_dvd_aa_mul {n : ℕ} (r : ℕ) : Nat.gcd n r ∣ aa n r * r.factorial := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [aa]
  · exact Dvd.dvd.mul_left ((Nat.gcd_dvd_right n r).trans (Nat.dvd_factorial hr le_rfl)) _

theorem delta_mul_gcd {n : ℕ} (r : ℕ) : delta n r * Nat.gcd n r = aa n r * r.factorial :=
  Nat.div_mul_cancel (gcd_dvd_aa_mul r)

theorem aa_pos {n : ℕ} (hn : 0 < n) (r : ℕ) : 0 < aa n r := by
  unfold aa; split_ifs <;> omega

theorem gcd_pos' {n : ℕ} (hn : 0 < n) (r : ℕ) : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_left r hn

theorem ee_pos {n : ℕ} (hn : 0 < n) (s : ℕ) : 0 < ee n s :=
  Nat.mul_pos (Nat.factorial_pos s) (gcd_pos' hn _)

/-- An odd-modulus fact: if `b` divides an odd `n`, `b` is odd. -/
theorem odd_of_dvd_odd {b n : ℕ} (hb : b ∣ n) (hn : n % 2 = 1) : Nat.Coprime 2 b := by
  rw [Nat.coprime_two_left]
  rcases hb with ⟨c, rfl⟩
  rw [Nat.odd_iff]
  rw [Nat.mul_mod] at hn
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp_all

/-- `r! · t ∣ t!` for `r < t`. -/
theorem fact_mul_dvd {r t : ℕ} (h : r < t) : r.factorial * t ∣ t.factorial := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [Nat.factorial_succ, mul_comm]
  exact mul_dvd_mul_left _ (Nat.factorial_dvd_factorial (by omega))

/-- The number theory of the case `s < N - r`: `a_r r! b ∣ gcd(n,r) t!` with
`t = n - 1 - s > r` and `b = gcd(n, s+1)`. -/
theorem key_dvd {n r s : ℕ} (h : r + s + 1 < n) :
    aa n r * r.factorial * Nat.gcd n (s + 1) ∣ Nat.gcd n r * (n - 1 - s).factorial := by
  set t := n - 1 - s with ht
  set b := Nat.gcd n (s + 1)
  have hbt : b ∣ t := by
    have := Nat.dvd_sub (Nat.gcd_dvd_left n (s + 1)) (Nat.gcd_dvd_right n (s + 1))
    rwa [show n - (s + 1) = t by omega] at this
  have hrt : r < t := by omega
  have h1 : r.factorial * b ∣ t.factorial :=
    (mul_dvd_mul_left _ hbt).trans (fact_mul_dvd hrt)
  unfold aa
  split_ifs with h0 hp
  · subst h0; simp only [Nat.gcd_zero_right, Nat.factorial_zero, mul_one]
    exact mul_dvd_mul_left _ (hbt.trans (Nat.dvd_factorial (by omega) le_rfl))
  · rcases Nat.mod_two_eq_zero_or_one n with hn2 | hn2
    · -- `n, r` even: `2 ∣ gcd(n, r)`
      rw [mul_assoc]
      exact mul_dvd_mul (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hn2)
        (Nat.dvd_of_mod_eq_zero (by omega))) h1
    · -- `n, r` odd: `b` odd, `r + 1` even
      have hb2 : Nat.Coprime 2 b := odd_of_dvd_odd (Nat.gcd_dvd_left n (s + 1)) hn2
      apply Dvd.dvd.mul_left
      rcases Nat.lt_or_ge (r + 1) t with hlt | hge
      · have h2 : (r + 1).factorial * t ∣ t.factorial := fact_mul_dvd hlt
        rw [Nat.factorial_succ] at h2
        obtain ⟨k, hk⟩ : 2 ∣ r + 1 := Nat.dvd_of_mod_eq_zero (by omega)
        obtain ⟨c, hc⟩ := hbt
        refine Dvd.dvd.trans ?_ h2
        rw [hk, hc]
        exact ⟨k * c, by ring⟩
      · have htr : t = r + 1 := by omega
        have h2 : r.factorial * t ∣ t.factorial := fact_mul_dvd hrt
        have h3 : 2 * b ∣ t :=
          hb2.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mod_eq_zero (by omega)) hbt
        refine Dvd.dvd.trans ?_ h2
        rw [mul_comm 2, mul_assoc]
        exact mul_dvd_mul_left _ h3
  · rw [one_mul]; exact h1.mul_left _

/-- `(1+y)^m - 1 = G_m · y` with `G_m = ∑_{k<m} (1+y)^k`. -/
noncomputable def G (m : ℕ) : ℤ[X] := ∑ k ∈ Finset.range m, (1 + X) ^ k

theorem factor_eq (m : ℕ) : (1 + X : ℤ[X]) ^ m - 1 = G m * X := by
  rw [G, ← geom_sum_mul]; ring

theorem HM_eq (s : Multiset ℕ) : HM s = (s.map G).prod * X ^ s.card := by
  unfold HM
  simp_rw [factor_eq]
  rw [Multiset.prod_map_mul]
  simp

theorem G_coeff_zero (m : ℕ) : (G m).coeff 0 = m := by
  simp [G, coeff_zero_eq_eval_zero, eval_finsetSum]

theorem HM_coeff_lt (s : Multiset ℕ) {j : ℕ} (hj : j < s.card) : (HM s).coeff j = 0 := by
  rw [HM_eq, coeff_mul_X_pow', if_neg (by omega)]

theorem HM_coeff_card (s : Multiset ℕ) : (HM s).coeff s.card = (s.prod : ℤ) := by
  rw [HM_eq, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_eval_zero,
    eval_multiset_prod, Multiset.map_map, Nat.cast_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun m _ => ?_
  simp [← coeff_zero_eq_eval_zero, G_coeff_zero]

/-- If every part is odd, the sum and the number of parts have the same parity. -/
theorem sum_mod_two (s : Multiset ℕ) (h : ∀ m ∈ s, m % 2 = 1) : s.sum % 2 = s.card % 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha := h a (Multiset.mem_cons_self a s)
    have := ih fun m hm => h m (Multiset.mem_cons_of_mem hm)
    omega

/-- `a_r ∣ ∏ μ_i` when `ℓ(μ) = r + 1`. -/
theorem aa_dvd_prod {n : ℕ} (μ : n.Partition) (r : ℕ) (hr : μ.parts.card = r + 1) :
    aa n r ∣ μ.parts.prod := by
  unfold aa
  split_ifs with h0 hp
  · subst h0
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hr
    have := μ.parts_sum
    rw [ha] at this ⊢
    simp_all
  · by_contra hc
    have hodd : ∀ m ∈ μ.parts, m % 2 = 1 := fun m hm => by
      by_contra he
      exact hc ((Nat.dvd_of_mod_eq_zero (by omega)).trans (Multiset.dvd_prod hm))
    have := sum_mod_two _ hodd
    rw [μ.parts_sum, hr] at this
    omega
  · exact one_dvd _

/-- `δ_r e_s ∣ s! (N-s)!` when `r + s < N`. -/
theorem main_dvd {n r s : ℕ} (h : r + s + 1 < n) :
    delta n r * ee n s ∣ s.factorial * (n - 1 - s).factorial := by
  apply Nat.dvd_of_mul_dvd_mul_right (gcd_pos' (by omega : 0 < n) r)
  have e1 : delta n r * ee n s * Nat.gcd n r =
      s.factorial * (aa n r * r.factorial * Nat.gcd n (s + 1)) := by
    rw [ee, ← delta_mul_gcd]; ring
  rw [e1]
  calc _ ∣ s.factorial * (Nat.gcd n r * (n - 1 - s).factorial) := mul_dvd_mul_left _ (key_dvd h)
    _ = _ := by ring

end LC

/-- Anti-triangularity of the form: `Q(i,s) = 0` for `i + s > N` (`i, s ≤ N`). -/
theorem Qf_eq_zero {N i s : ℕ} (hi : i ≤ N) (hs : s ≤ N) (h : N < i + s) : Qf N i s = 0 := by
  unfold Qf
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- Lemma C. -/
theorem lemmaC {n : ℕ} (hn : 0 < n) (μ : n.Partition) (r : ℕ) (hr : μ.parts.card = r + 1)
    (s : Fin n) : ∃ z : ℤ, GamQ n μ s = (delta n r : ℚ) * z := by
  set N := n - 1 with hN
  have hs_lt : (s : ℕ) < n := s.isLt
  have hterm : ∀ i : Fin n, ((delta n r * ee n s : ℕ) : ℤ) ∣ eta μ i * Qf N i s := by
    intro i
    have hi_lt : (i : ℕ) < n := i.isLt
    by_cases hi : (i : ℕ) < r
    · rw [eta, LC.HM_coeff_lt _ (by omega)]; simp
    by_cases hs : N < i + s
    · rw [Qf_eq_zero (by omega) (by omega) hs]; simp
    rcases Nat.lt_or_ge (r + s) N with hlt | hge
    · -- `s < N - r`: the number theory of `LC.key_dvd`
      apply Dvd.dvd.mul_left
      unfold Qf
      apply Dvd.dvd.mul_left
      apply Int.natCast_dvd_natCast.mpr
      apply Dvd.dvd.mul_right
      exact LC.main_dvd (by omega)
    · -- `s = N - r`: only `i = r` survives, with `η_μ(r) = ∏ μ_i`
      have hir : (i : ℕ) = r := by omega
      have hee : delta n r * ee n s = aa n r * ((s : ℕ).factorial * r.factorial) := by
        unfold ee
        rw [show (s : ℕ) + 1 = n - r by omega, Nat.gcd_self_sub_right (by omega),
          show delta n r * ((s : ℕ).factorial * Nat.gcd n r) =
            (s : ℕ).factorial * (delta n r * Nat.gcd n r) by ring, LC.delta_mul_gcd]
        ring
      rw [hee, eta, Qf, hir, show r + 1 = μ.parts.card from hr.symm, LC.HM_coeff_card,
        show N - s = r by omega, show N - r = s by omega, Nat.choose_self, mul_one]
      obtain ⟨c, hc⟩ := LC.aa_dvd_prod μ r hr
      rw [hc]
      push_cast
      exact ⟨c * (-1) ^ (r + (s : ℕ)), by ring⟩
  obtain ⟨z, hz⟩ : ((delta n r * ee n s : ℕ) : ℤ) ∣ ∑ i : Fin n, eta μ i * Qf N i s :=
    Finset.dvd_sum fun i _ => hterm i
  refine ⟨z, ?_⟩
  have hee : (ee n s : ℚ) ≠ 0 := by exact_mod_cast (LC.ee_pos hn s).ne'
  unfold GamQ
  rw [← Int.cast_sum, ← hN, hz]
  push_cast
  field_simp

/-- The anti-diagonal: `a_r Q(r, N-r) / e_{N-r} = ± δ_r`. -/
theorem antidiag {n : ℕ} (hn : 0 < n) (r : ℕ) (hr : r < n) :
    (aa n r : ℚ) * (Qf (n - 1) r (n - 1 - r) : ℚ) / (ee n (n - 1 - r) : ℚ) = delta n r ∨
    (aa n r : ℚ) * (Qf (n - 1) r (n - 1 - r) : ℚ) / (ee n (n - 1 - r) : ℚ) = -(delta n r : ℚ) := by
  have hQ : Qf (n - 1) r (n - 1 - r) =
      (-1) ^ (n - 1) * (((n - 1 - r).factorial * r.factorial : ℕ) : ℤ) := by
    unfold Qf
    rw [show r + (n - 1 - r) = n - 1 by omega, show n - 1 - (n - 1 - r) = r by omega,
      Nat.choose_self, mul_one]
  have hee : ee n (n - 1 - r) = (n - 1 - r).factorial * Nat.gcd n r := by
    unfold ee
    rw [show n - 1 - r + 1 = n - r by omega, Nat.gcd_self_sub_right hr.le]
  have hd : (delta n r : ℚ) * (Nat.gcd n r : ℚ) = (aa n r : ℚ) * r.factorial := by
    exact_mod_cast LC.delta_mul_gcd r
  have hg : (Nat.gcd n r : ℚ) ≠ 0 := by exact_mod_cast (LC.gcd_pos' hn r).ne'
  have hf : ((n - 1 - r).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [hQ, hee]
  push_cast
  rcases neg_one_pow_eq_or ℚ (n - 1) with h | h
  · left
    rw [h, div_eq_iff (mul_ne_zero hf hg)]
    linear_combination (-(n - 1 - r).factorial : ℚ) * hd
  · right
    rw [h, div_eq_iff (mul_ne_zero hf hg)]
    linear_combination ((n - 1 - r).factorial : ℚ) * hd

theorem delta_pos {n : ℕ} (hn : 0 < n) (r : ℕ) (hr : r < n) : 0 < delta n r := by
  rcases Nat.eq_zero_or_pos (delta n r) with h | h
  · have := LC.delta_mul_gcd (n := n) r
    rw [h, zero_mul] at this
    exact absurd this.symm (Nat.mul_pos (LC.aa_pos hn r) (Nat.factorial_pos r)).ne'
  · exact h

theorem delta_eq_stanleyD {n : ℕ} (hn : 0 < n) (r : ℕ) (hr : r < n) :
    delta n r = stanleyD n r := by
  unfold delta stanleyD aa
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp [Nat.div_self hn]
  · simp only [if_neg hr0.ne', Nat.gcd_comm n r]

/-- `stanleyD n k = c·k!/gcd(k,n)` exactly (the division is exact). -/
theorem stanleyD_mul_gcd {n : ℕ} (k : ℕ) (hk : 0 < k) :
    stanleyD n k * Nat.gcd k n = (if k % 2 = n % 2 then 2 else 1) * k.factorial := by
  unfold stanleyD
  rw [if_neg hk.ne']
  exact Nat.div_mul_cancel
    (((Nat.gcd_dvd_left k n).trans (Nat.dvd_factorial hk le_rfl)).mul_left _)

/-- The invariant factors form a divisor chain. -/
theorem stanleyD_dvd {n : ℕ} (r : ℕ) (hr : r + 1 < n) : stanleyD n r ∣ stanleyD n (r + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp [stanleyD]
  have h1 := stanleyD_mul_gcd (n := n) r hr0
  have h2 := stanleyD_mul_gcd (n := n) (r + 1) (by omega)
  set c1 := if r % 2 = n % 2 then 2 else 1 with hc1
  set c2 := if (r + 1) % 2 = n % 2 then 2 else 1 with hc2
  set g1 := Nat.gcd r n
  set g2 := Nat.gcd (r + 1) n
  have hg1 : 0 < g1 := Nat.gcd_pos_of_pos_left n hr0
  have hg2 : 0 < g2 := Nat.gcd_pos_of_pos_left n (by omega)
  obtain ⟨m, hm⟩ : g2 ∣ r + 1 := Nat.gcd_dvd_left _ _
  have key : c1 ∣ c2 * m * g1 := by
    rw [hc1, hc2]
    split_ifs with ha hb
    · omega
    · rcases Nat.mod_two_eq_zero_or_one n with hn2 | hn2
      · exact Dvd.dvd.mul_left
          (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero hn2)) _
      · have hc : Nat.Coprime 2 g2 := LC.odd_of_dvd_odd (Nat.gcd_dvd_right _ _) hn2
        have h2m : 2 ∣ g2 * m := hm ▸ Nat.dvd_of_mod_eq_zero (by omega)
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hc.dvd_of_dvd_mul_left h2m) _) _
    · exact one_dvd _
    · exact one_dvd _
  apply Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos hg1 hg2)
  have e1 : stanleyD n r * (g1 * g2) = c1 * r.factorial * g2 := by rw [← mul_assoc, h1]
  have e2 : stanleyD n (r + 1) * (g1 * g2) = c2 * (r + 1).factorial * g1 := by
    rw [mul_comm g1, ← mul_assoc, h2]
  rw [e1, e2, Nat.factorial_succ, hm]
  obtain ⟨c, hc⟩ := key
  exact ⟨c, by
    rw [show c2 * (g2 * m * r.factorial) * g1 = (c2 * m * g1) * (g2 * r.factorial) by ring, hc]
    ring⟩


end StanleySnf
