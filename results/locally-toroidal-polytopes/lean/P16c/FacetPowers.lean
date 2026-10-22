import P16c.Translations

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo

/-- A facet translation power is scalar precisely when it is the identity. -/
lemma t_scalar_period (a b l : K) (hl : l ≠ 0) (hs : Odd (orderOf l))
    (hσ : a + b = traceParam l) (n : ℕ) (c : K) (hc : T a b ^ n = c • (1 : Mat K)) :
    orderOf l ∣ n := by
  have hM : T a b ^ 2 = (l + l⁻¹) • T a b + 1 := by simpa [hσ, traceParam] using t_square a b
  obtain ⟨α, β, hp, h₁, h₂⟩ := quadratic_power (T a b) l hl hM n
  have hb : β = 0 := by
    have hh := congrArg (fun M : Mat K => M 0 2) (hp.symm.trans hc)
    simpa [T, r, r₁, Matrix.mul_apply, Fin.sum_univ_succ] using hh
  have heq : l ^ n = (l⁻¹) ^ n := by
    simp only [hb, zero_mul, add_zero] at h₁ h₂
    exact h₁.trans h₂.symm
  have hpow : l ^ (2 * n) = 1 := by
    rw [mul_comm 2 n, pow_mul, pow_two]
    calc
      l ^ n * l ^ n = l ^ n * (l⁻¹) ^ n := by rw [heq]
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hl, one_pow]
  exact hs.coprime_two_right.dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one hpow)

/-- L4(ii), independence of the two facet directions, as exact exponent divisibility. -/
theorem facet_power_independence (a b l : K) (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hs : Odd (orderOf l)) (hσ : a + b = traceParam l) (i j : ℕ)
    (h : T a b ^ i * T₂ a b ^ j = 1) : orderOf l ∣ i ∧ orderOf l ∣ j := by
  let s := orderOf l
  have hspos : 0 < s := hs.pos
  have ht₂ : T₂ a b ^ s = 1 := by
    change T₂ a b ^ orderOf l = 1
    rw [← t₂_order a b l hl hl2 hσ]
    exact pow_orderOf_eq_one _
  let k := (s - 1) * j
  have hsum : j + k = s * j := by
    have hs1 : 1 + (s - 1) = s := by omega
    dsimp [k]
    calc
      j + (s - 1) * j = (1 + (s - 1)) * j := by ring
      _ = s * j := by rw [hs1]
  have hcancel : T₂ a b ^ j * T₂ a b ^ k = 1 := by
    rw [← pow_add, hsum, pow_mul, ht₂, one_pow]
  have heq : T a b ^ i = T₂ a b ^ k := by
    calc
      T a b ^ i = T a b ^ i * (T₂ a b ^ j * T₂ a b ^ k) := by rw [hcancel, mul_one]
      _ = T₂ a b ^ k := by rw [← mul_assoc, h, one_mul]
  have hM : T a b ^ 2 = (l + l⁻¹) • T a b + 1 := by simpa [hσ, traceParam] using t_square a b
  have hM₂ : T₂ a b ^ 2 = (l + l⁻¹) • T₂ a b + 1 := by simpa [hσ, traceParam] using t₂_square a b
  obtain ⟨α, β, hp, _, _⟩ := quadratic_power (T a b) l hl hM i
  obtain ⟨γ, δ, hq, _, _⟩ := quadratic_power (T₂ a b) l hl hM₂ k
  have hab : a + b ≠ 0 := by
    rw [hσ]
    exact traceParam_ne_zero hl hl2
  have hβ := (translation_planes_intersect a b hab α β γ δ (hp.symm.trans (heq.trans hq))).1
  have hscalar : T a b ^ i = α • (1 : Mat K) := by simpa [hβ] using hp
  have hi := t_scalar_period a b l hl hs hσ i α hscalar
  have hti : T a b ^ i = 1 := by rw [← t_order a b l hl hl2 hσ] at hi; exact orderOf_dvd_iff_pow_eq_one.mp hi
  have htj : T₂ a b ^ j = 1 := by simpa [hti] using h
  refine ⟨hi, ?_⟩
  rw [← t₂_order a b l hl hl2 hσ]
  exact orderOf_dvd_of_pow_eq_one htj
end P16c
