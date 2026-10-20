import Uniform5.CompositionCaseBCellRayMetrics

/-! Three actual normal rays span the transverse space in Case B(ii). -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

/-- Three unit rays, with one orthogonal to the other two and a nondegenerate
Gram entry between those two, form a basis of a three-dimensional subspace. -/
theorem three_ray_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : Submodule ℝ E) (hS : Module.finrank ℝ S = 3)
    {h z₁ z₂ : E} (hm : h ∈ S) (h₁m : z₁ ∈ S) (h₂m : z₂ ∈ S)
    (hh : ‖h‖ = 1) (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1)
    (hh₁ : ⟪h, z₁⟫ = 0) (hh₂ : ⟪h, z₂⟫ = 0)
    (hg₁ : ⟪z₁, z₂⟫ ≠ 1) (hg₂ : ⟪z₁, z₂⟫ ≠ -1) :
    Submodule.span ℝ ({h, z₁, z₂} : Set E) = S := by
  have hli : LinearIndependent ℝ ![h, z₁, z₂] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have he : c 0 • h + c 1 • z₁ + c 2 • z₂ = 0 := by
      simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, add_assoc] using hc
    have eh := congrArg (fun x => ⟪h, x⟫) he
    have e₁ := congrArg (fun x => ⟪z₁, x⟫) he
    have e₂ := congrArg (fun x => ⟪z₂, x⟫) he
    have hh₁' : ⟪z₁, h⟫ = 0 := by rw [real_inner_comm, hh₁]
    have hh₂' : ⟪z₂, h⟫ = 0 := by rw [real_inner_comm, hh₂]
    have hg' : ⟪z₂, z₁⟫ = ⟪z₁, z₂⟫ := real_inner_comm _ _
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hh, h₁, h₂, hh₁, hh₂, hh₁', hh₂', hg', one_pow, mul_zero, mul_one,
      add_zero, zero_add, inner_zero_right] at eh e₁ e₂
    have hdiff : (c 1 - c 2) * (1 - ⟪z₁, z₂⟫) = 0 := by linarith
    have heq : c 1 = c 2 := by
      rcases mul_eq_zero.mp hdiff with ha | ha
      · linarith
      · exact (hg₁ (by linarith)).elim
    have hsum : c 1 * (1 + ⟪z₁, z₂⟫) = 0 := by rw [heq]; linarith
    have hc₁ : c 1 = 0 := (mul_eq_zero.mp hsum).resolve_right (fun he => hg₂ (by linarith))
    intro i
    fin_cases i <;> simp_all
  have hspan : Submodule.span ℝ (Set.range ![h, z₁, z₂]) =
      Submodule.span ℝ ({h, z₁, z₂} : Set E) := by
    congr 1
    ext x
    simp [Set.mem_range, Fin.exists_fin_succ, or_comm, or_left_comm]
  have hdim := finrank_span_eq_card hli
  rw [hspan] at hdim
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simpa [hS] using hdim

/-- The actual parent offset splits into its antiprism axis and the plane
of the two prism rays. All coefficients are consequences of the Gram data. -/
theorem three_ray_decomposition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : Submodule ℝ E) (hS : Module.finrank ℝ S = 3)
    {h z₁ z₂ W : E} {t : ℝ} (hm : h ∈ S) (h₁m : z₁ ∈ S) (h₂m : z₂ ∈ S)
    (hWm : W ∈ S) (hh : ‖h‖ = 1) (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1)
    (hh₁ : ⟪h, z₁⟫ = 0) (hh₂ : ⟪h, z₂⟫ = 0)
    (hg₁ : ⟪z₁, z₂⟫ ≠ 1) (hg₂ : ⟪z₁, z₂⟫ ≠ -1)
    (hWh : ⟪h, W⟫ = t) (hW₁ : ⟪z₁, W⟫ = 1 / 2) (hW₂ : ⟪z₂, W⟫ = 1 / 2) :
    ∃ w : E, (∃ α β : ℝ, w = α • z₁ + β • z₂) ∧
      ⟪w, z₁⟫ = 1 / 2 ∧ ⟪w, z₂⟫ = 1 / 2 ∧ ⟪h, w⟫ = 0 ∧ W = t • h + w := by
  rw [← three_ray_span S hS hm h₁m h₂m hh h₁ h₂ hh₁ hh₂ hg₁ hg₂,
    Submodule.mem_span_insert] at hWm
  obtain ⟨a, w, hw, he⟩ := hWm
  obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.mp hw
  have ho : ⟪h, b • z₁ + c • z₂⟫ = 0 := by
    simp [inner_add_right, real_inner_smul_right, hh₁, hh₂]
  have ha : a = t := by
    rw [he, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hh, ho] at hWh
    simpa using hWh
  subst a
  refine ⟨b • z₁ + c • z₂, ⟨b, c, rfl⟩, ?_, ?_, ho, he⟩
  · rw [he, inner_add_right, real_inner_smul_right, (show ⟪z₁, h⟫ = 0 from (real_inner_comm _ _).trans hh₁)] at hW₁
    simpa only [mul_zero, zero_add, real_inner_comm] using hW₁
  · rw [he, inner_add_right, real_inner_smul_right, (show ⟪z₂, h⟫ = 0 from (real_inner_comm _ _).trans hh₂)] at hW₂
    simpa only [mul_zero, zero_add, real_inner_comm] using hW₂

end Uniform5.Composition
