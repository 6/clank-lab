import RS16.Rhs

/-!
# From finitely many `m₁` to all `m₁` (the paper, Steps 3–4)

If the `N`-th difference of `F` is regular with value `0` at `ω`, and `L` has vanishing `N`-th
difference, then `F(m₁)` regular with value `L(m₁)` for `m₁ = 1, …, N` gives the same for every
`m₁ ≥ 1` (`propagate`). Binomial sums `Σ_{j ≤ n} binom(m₁, j) a_j` have vanishing `(n+1)`-th
difference (`choose_sum_diff`).
-/

open Polynomial

namespace RS16

variable {K : Type*} [Field K]

theorem propagate {F : ℕ → RatFunc K} {L : ℕ → K} {N : ℕ} {ω : K}
    (hF : ∀ m1, HasValueAt (∑ k ∈ Finset.range (N + 1),
      ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) • F (m1 + k)) ω 0)
    (hL : ∀ m1, ∑ k ∈ Finset.range (N + 1), ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) • L (m1 + k) = 0)
    (h0 : ∀ m1, 1 ≤ m1 → m1 ≤ N → HasValueAt (F m1) ω (L m1)) :
    ∀ m1, 1 ≤ m1 → HasValueAt (F m1) ω (L m1) := by
  intro m1
  induction m1 using Nat.strong_induction_on with
  | _ m1 ih =>
    intro h1
    by_cases hm : m1 ≤ N
    · exact h0 m1 h1 hm
    obtain ⟨m', rfl⟩ : ∃ m', m1 = m' + N := ⟨m1 - N, by omega⟩
    have hm' : 1 ≤ m' := by omega
    have hsplit := hF m'
    rw [Finset.sum_range_succ] at hsplit
    have hLs := hL m'
    rw [Finset.sum_range_succ] at hLs
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, one_smul] at hsplit hLs
    have hrest : HasValueAt (∑ k ∈ Finset.range N, ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) •
        F (m' + k)) ω (∑ k ∈ Finset.range N, ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) •
        L (m' + k)) :=
      hasValueAt_finset_sum _ _ _ fun k hk =>
        (ih (m' + k) (by have := Finset.mem_range.mp hk; omega) (by omega)).zsmul _
    have := hsplit.sub hrest
    rw [add_sub_cancel_left, zero_sub] at this
    rwa [show L (m' + N) = -∑ k ∈ Finset.range N, ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) •
      L (m' + k) by linear_combination hLs]

lemma fwdDiff_iter_choose_eq_zero (j N : ℕ) (hj : j < N) :
    (fwdDiff 1)^[N] (fun x : ℕ => (x.choose j : K)) = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hj
  rw [show j + r + 1 = (r + 1) + j by ring, Function.iterate_add_apply]
  have := fwdDiff_iter_choose (R := K) 0 j
  simp only [add_zero] at this
  rw [this]
  simp only [Nat.choose_zero_right, Nat.cast_one, Function.iterate_succ_apply]
  rw [fwdDiff_const]
  clear hj this
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih]; exact fwdDiff_const 1 (0 : K)

theorem choose_sum_diff (n : ℕ) (a : ℕ → K) (m1 : ℕ) :
    ∑ k ∈ Finset.range (n + 1 + 1), ((-1 : ℤ) ^ (n + 1 - k) * ((n + 1).choose k : ℤ)) •
      (∑ j ∈ Finset.range (n + 1), ((m1 + k).choose j : K) * a j) = 0 := by
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x : ℕ => (x.choose j : K)) (n + 1) m1
  rw [fwdDiff_iter_choose_eq_zero j (n + 1) (by have := Finset.mem_range.mp hj; omega)] at h
  simp only [Pi.zero_apply, smul_eq_mul, mul_one] at h
  have : ∑ k ∈ Finset.range (n + 1 + 1), ((-1 : ℤ) ^ (n + 1 - k) * ((n + 1).choose k : ℤ)) •
      (((m1 + k).choose j : K) * a j) = (∑ k ∈ Finset.range (n + 1 + 1),
        ((-1 : ℤ) ^ (n + 1 - k) * ((n + 1).choose k : ℤ)) • ((m1 + k).choose j : K)) * a j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_mul_assoc]
  rw [this, ← h, zero_mul]

/-- The paper, Step 3 with Step 4's interpolation: a row of the accepted shape with at most `n`
numerator and at most `n` denominator brackets, evaluated at `m = E m₁ + 1` with `d ∣ E`, that is
regular at a primitive `d`-th root of unity `ω` with value `Σ_{j ≤ n} binom(m₁, j) a_j` for
`m₁ = 1, …, n + 1`, is so for every `m₁ ≥ 1`. -/
theorem step3 [CharZero K] (row : Row) (n d E : ℕ) {ω : K} (hd0 : 0 < d)
    (hω : IsPrimitiveRoot ω d) (hdE : d ∣ E) (hnum : row.numCount ≤ n)
    (hden : row.dens.length ≤ n) (a : ℕ → K)
    (h : ∀ m1 : ℕ, 1 ≤ m1 → m1 ≤ n + 1 → HasValueAt (row.eval K ((E : ℤ) * m1 + 1)) ω
      (∑ j ∈ Finset.range (n + 1), (m1.choose j : K) * a j)) :
    ∀ m1 : ℕ, 1 ≤ m1 → HasValueAt (row.eval K ((E : ℤ) * m1 + 1)) ω
      (∑ j ∈ Finset.range (n + 1), (m1.choose j : K) * a j) := by
  have hω0 : ω ≠ 0 := hω.ne_zero hd0.ne'
  have hωE : ω ^ E = 1 := (hω.pow_eq_one_iff_dvd E).mpr hdE
  have hD : poleBound ω row < n + 1 := by
    by_cases h1 : ω = 1
    · subst h1; have := poleBound_le_numCount (K := K) row; omega
    · have := poleBound_le_dens h1 row; omega
  exact propagate (F := fun m1 => row.eval K ((E : ℤ) * m1 + 1))
    (zexp_diff_zero hω0 hωE hD (row_zexp E hω0 row)) (choose_sum_diff n a) h

end RS16
