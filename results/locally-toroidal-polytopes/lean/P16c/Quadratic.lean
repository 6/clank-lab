import Mathlib

namespace P16c
open scoped CharTwo
variable {K A : Type*} [Field K] [CharP K 2] [Ring A] [Algebra K A]

/-- Reduction of powers modulo a split quadratic, with evaluation at both roots. -/
lemma quadratic_power (M : A) (l : K) (hl : l ≠ 0)
    (hM : M ^ 2 = (l + l⁻¹) • M + 1) (n : ℕ) :
    ∃ α β : K, M ^ n = α • (1 : A) + β • M ∧
      l ^ n = α + β * l ∧ (l⁻¹) ^ n = α + β * l⁻¹ := by
  have hroot (x : K) (hx : x = l ∨ x = l⁻¹) : x ^ 2 = 1 + (l + l⁻¹) * x := by
    rcases hx with rfl | rfl <;> field_simp <;> ring_nf <;> simp_all
  induction n with
  | zero => exact ⟨1, 0, by simp⟩
  | succ n ih =>
    obtain ⟨α, β, hpow, h₁, h₂⟩ := ih
    refine ⟨β, α + β * (l + l⁻¹), ?_, ?_, ?_⟩
    · rw [pow_succ, hpow, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
        ← pow_two, hM, smul_add, smul_smul]
      module
    · rw [pow_succ, h₁]
      calc
        (α + β * l) * l = α * l + β * l ^ 2 := by ring
        _ = β + (α + β * (l + l⁻¹)) * l := by rw [hroot l (Or.inl rfl)]; ring
    · rw [pow_succ, h₂]
      calc
        (α + β * l⁻¹) * l⁻¹ = α * l⁻¹ + β * (l⁻¹) ^ 2 := by ring
        _ = β + (α + β * (l + l⁻¹)) * l⁻¹ := by rw [hroot l⁻¹ (Or.inr rfl)]; ring

/-- A nonscalar quadratic element has exactly its root's multiplicative order. -/
lemma quadratic_order [Nontrivial A] (M : A) (l : K) (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1)
    (hM : M ^ 2 = (l + l⁻¹) • M + 1)
    (hscalar : ∀ c : K, M ≠ c • (1 : A)) : orderOf M = orderOf l := by
  have hlin : ∀ α β : K, α • (1 : A) + β • M = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    by_cases hb : β = 0
    · simp only [hb, zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h
      exact ⟨h, hb⟩
    · exfalso
      apply hscalar (-α / β)
      have hh := congrArg (fun x : A => β⁻¹ • x) h
      have hx : (α / β) • (1 : A) + M = 0 := by
        simpa [smul_add, smul_smul, hb, div_eq_mul_inv, mul_comm] using hh
      rw [neg_div, neg_smul]
      exact eq_neg_of_add_eq_zero_right hx
  rw [orderOf_eq_orderOf_iff]
  intro n
  obtain ⟨α, β, hpow, h₁, h₂⟩ := quadratic_power M l hl hM n
  constructor
  · intro hn
    have hz : (α - 1) • (1 : A) + β • M = 0 := by
      rw [sub_smul, one_smul]
      rw [← sub_eq_zero] at hn
      rw [hpow] at hn
      convert hn using 1 <;> abel
    obtain ⟨ha, hb⟩ := hlin _ _ hz
    rw [sub_eq_zero] at ha
    simpa [ha, hb] using h₁
  · intro hn
    have hn' : (l⁻¹) ^ n = 1 := by rw [inv_pow, hn, inv_one]
    have hd : l - l⁻¹ ≠ 0 := by
      intro heq
      apply hl2
      have := congrArg (fun x : K => x * l) (sub_eq_zero.mp heq)
      simpa [pow_two, hl] using this
    have hb : β = 0 := by
      have hz : β * (l - l⁻¹) = 0 := by
        rw [hn] at h₁
        rw [hn'] at h₂
        rw [mul_sub]
        linear_combination -h₁ + h₂
      exact (mul_eq_zero.mp hz).resolve_right hd
    have ha : α = 1 := by simpa [hb, hn] using h₁.symm
    simpa [ha, hb] using hpow
end P16c
