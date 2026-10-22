import P16c.MatrixDefs

namespace P16c
variable {K : Type*} [Field K] [CharP K 2]
open scoped CharTwo

/-- L2': the minor on entries (0,0), (0,2), (1,0) is nonzero. -/
lemma independent_coefficients (a b : K) (hab : a + b ≠ 0) (α β γ : K)
    (h : α • (1 : Mat K) + β • T a b + γ • T₂ a b = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  have h02 := congrArg (fun M : Mat K => M 0 2) h
  have h10 := congrArg (fun M : Mat K => M 1 0) h
  have h00 := congrArg (fun M : Mat K => M 0 0) h
  simp [T, T₂, r, r₁, Matrix.mul_apply, Fin.sum_univ_succ] at h02 h10 h00
  have hg : γ = β := by
    exact eq_of_sub_eq_zero (by simpa [add_comm] using h02)
  have hb : β = 0 := by
    have hz : β * (a + b) = 0 := by
      rw [hg] at h10
      convert h10 using 1 <;> ring_nf <;> simp
    exact (mul_eq_zero.mp hz).resolve_right hab
  exact ⟨by simpa [hb, hg] using h00, hb, hg.trans hb⟩

lemma t_not_scalar (a b : K) (c : K) : T a b ≠ c • (1 : Mat K) := by
  intro h
  have := congrArg (fun M : Mat K => M 0 2) h
  simpa [T, r, r₁, Matrix.mul_apply, Fin.sum_univ_succ] using this

lemma t₂_not_scalar (a b : K) (c : K) : T₂ a b ≠ c • (1 : Mat K) := by
  intro h
  have := congrArg (fun M : Mat K => M 0 2) h
  simpa [T₂, T, r, r₁, Matrix.mul_apply, Fin.sum_univ_succ] using this

lemma translations_linearIndependent (a b : K) (hab : a + b ≠ 0) :
    LinearIndependent K ![(1 : Mat K), T a b, T₂ a b] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h : c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 := by
    apply independent_coefficients a b hab
    simpa [Fin.sum_univ_succ, add_assoc] using hc
  intro i
  fin_cases i <;> simp_all

/-- The two translation planes meet precisely in the scalar line. -/
lemma translation_planes_intersect (a b : K) (hab : a + b ≠ 0)
    (α β γ δ : K) (h : α • (1 : Mat K) + β • T a b = γ • (1 : Mat K) + δ • T₂ a b) :
    β = 0 ∧ δ = 0 ∧ α = γ := by
  have hz : (α - γ) • (1 : Mat K) + β • T a b + (-δ) • T₂ a b = 0 := by
    rw [sub_smul, neg_smul]
    rw [← sub_eq_zero] at h
    convert h using 1 <;> abel
  obtain ⟨ha, hb, hd⟩ := independent_coefficients a b hab _ _ _ hz
  exact ⟨hb, neg_eq_zero.mp hd, sub_eq_zero.mp ha⟩
end P16c
