import P16c.FacetPowers

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]

/-- L5's key obstruction: no nontrivial facet translation power commutes with V. -/
lemma t_power_commuting_period (a b l : K) (ha : a ≠ 0) (hl : l ≠ 0)
    (hl2 : l ^ 2 ≠ 1) (hs : Odd (orderOf l)) (hσ : a + b = traceParam l)
    (n : ℕ) (hcomm : T a b ^ n * V a b = V a b * T a b ^ n) : orderOf l ∣ n := by
  have hM : T a b ^ 2 = (l + l⁻¹) • T a b + 1 := by simpa [hσ, traceParam] using t_square a b
  obtain ⟨α, β, hp, _, _⟩ := quadratic_power (T a b) l hl hM n
  have hβ : β = 0 := by
    by_contra hb
    have hh : β • (T a b * V a b) = β • (V a b * T a b) := by
      rw [hp] at hcomm
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at hcomm
      exact add_left_cancel hcomm
    have htv : T a b * V a b = V a b * T a b := by
      have hh' := congrArg (fun M : Mat K => β⁻¹ • M) hh
      simpa [smul_smul, hb] using hh'
    exact tv_ne_vt a b ha (by rw [hσ]; exact traceParam_ne_zero hl hl2) htv
  apply t_scalar_period a b l hl hs hσ n α
  simpa [hβ] using hp
end P16c
