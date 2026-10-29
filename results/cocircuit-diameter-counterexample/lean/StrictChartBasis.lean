import IntegralProductChart

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem strict_chart_mulVec_injective {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ)
    (hc : ∀ v, StarFeasible A none v → v ≠ 0 → 0 < v 0) :
    Function.Injective A.mulVec := by
  suffices hker : ∀ v, A.mulVec v = 0 → v = 0 by
    intro x y hxy
    have he : A.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker _ he)
  intro v hv
  by_contra hn
  have hp : StarFeasible A none v := by
    intro i
    have hz := congrFun hv i
    change A i ⬝ᵥ v = 0 at hz
    rw [hz, mul_zero]
  have hm : StarFeasible A none (-v) := by
    intro i
    have hz := congrFun hv i
    change A i ⬝ᵥ v = 0 at hz
    rw [dotProduct_neg, hz, neg_zero, mul_zero]
  have h1 := hc v hp hn
  have h2 := hc (-v) hm (neg_ne_zero.mpr hn)
  change 0 < -v 0 at h2
  linarith

/-- A strict common chart supplies a full row subsystem. This is an
    existence proof from exact linear algebra, not a scan of all minors. -/
theorem exists_full_row_basis {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (hi : Function.Injective A.mulVec) :
    ∃ f : Fin r → Fin n, Function.Injective f ∧ (A.submatrix f id).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hs, hl⟩ := exists_linearIndependent' ℚ A
  letI : Fintype κ := Fintype.ofInjective a ha
  let M : Matrix κ (Fin r) ℚ := fun i => A (a i)
  have hmi : Function.Injective M.mulVecLin := by
    intro x y hxy
    apply hi
    ext i
    let K : Submodule ℚ (Fin r → ℚ) := {
      carrier := {w | w ⬝ᵥ (x - y) = 0}
      zero_mem' := by simp
      add_mem' := by intro u v hu hv; change (u + v) ⬝ᵥ (x - y) = 0; rw [add_dotProduct, hu, hv, add_zero]
      smul_mem' := by intro c u hu; change (c • u) ⬝ᵥ (x - y) = 0; rw [smul_dotProduct, hu, smul_zero] }
    have hK : Submodule.span ℚ (Set.range (A ∘ a)) ≤ K := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change A (a k) ⬝ᵥ (x - y) = 0
      rw [dotProduct_sub]
      exact sub_eq_zero.mpr (congrFun hxy k)
    have hm : A i ∈ K := hK (hs.symm ▸ Submodule.subset_span (Set.mem_range_self i))
    change A i ⬝ᵥ (x - y) = 0 at hm
    rw [dotProduct_sub] at hm
    exact sub_eq_zero.mp hm
  have hupper : Fintype.card κ ≤ r := by
    simpa using hl.fintype_card_le_finrank
  have hlower : r ≤ Fintype.card κ := by
    simpa using LinearMap.finrank_le_finrank_of_injective hmi
  have hcard : Fintype.card κ = r := le_antisymm hupper hlower
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hl.comp e e.injective

#print axioms strict_chart_mulVec_injective
#print axioms exists_full_row_basis
end
end ADKZPricing
