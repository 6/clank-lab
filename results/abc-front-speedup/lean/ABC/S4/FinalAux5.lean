import ABC.S4.Defs

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4.FinalAux

theorem isClosed_delta {n : ℕ} (τ α : ℝ) : IsClosed (ABC.Poschel2001.Delta (n := n) τ α) := by
  have : ABC.Poschel2001.Delta (n := n) τ α =
      ⋂ k : Fin n → ℤ, ⋂ (_ : k ≠ 0),
        {ω | α / ABC.Poschel2001.l1norm k ^ τ ≤ |ABC.Poschel2001.pairZ k ω|} := by
    ext ω; simp [ABC.Poschel2001.Delta]
  rw [this]
  refine isClosed_iInter fun k => isClosed_iInter fun _ => ?_
  refine isClosed_le continuous_const (continuous_abs.comp ?_)
  unfold ABC.Poschel2001.pairZ
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

theorem isClosed_omegaAlpha {n : ℕ} {τ α : ℝ} {Ω : Set (Fin n → ℝ)} (hα : 0 < α)
    (hΩ : IsOpen Ω) : IsClosed (OmegaAlpha τ Ω α) := by
  set A : Set (Fin n → ℝ) :=
    ABC.Poschel2001.Delta τ α ∩ {ω | ∀ y ∈ frontier Ω, α ≤ dist ω y} with hA
  have hAc : IsClosed A := by
    refine (isClosed_delta τ α).inter ?_
    have : {ω : Fin n → ℝ | ∀ y ∈ frontier Ω, α ≤ dist ω y} =
        ⋂ y ∈ frontier Ω, {ω | α ≤ dist ω y} := by
      ext ω; simp
    rw [this]
    exact isClosed_biInter fun y _ => isClosed_le continuous_const
      (continuous_id.dist continuous_const)
  have hEq : OmegaAlpha τ Ω α = Ω ∩ A := by
    ext ω; exact Iff.rfl
  rw [hEq]
  refine isClosed_of_closure_subset fun ω hω => ?_
  have hωΩ : ω ∈ closure Ω := closure_mono inter_subset_left hω
  have hωA : ω ∈ A := hAc.closure_subset (closure_mono inter_subset_right hω)
  refine ⟨?_, hωA⟩
  by_contra hn
  have hfr : ω ∈ frontier Ω := by
    rw [frontier, hΩ.interior_eq]
    exact ⟨hωΩ, hn⟩
  have := hωA.2 ω hfr
  rw [dist_self] at this
  linarith

theorem continuous_vec_one : Continuous fun σ : ℝ => (![σ, 1] : Fin 2 → ℝ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_id
  · exact continuous_const

theorem K_isCompact {ν b ε α : ℝ} (hα : 0 < α) (hΩ : IsOpen (OmegaE ν b ε)) :
    IsCompact {σ : ℝ | ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α} := by
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_omegaAlpha hα hΩ).preimage continuous_vec_one) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := |ν| + 2 * |b| * |ε|)).subset ?_
  intro σ hσ
  obtain ⟨⟨-, P, ⟨hP1, hP2⟩, hPeq⟩, -, -⟩ := hσ
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_one] at hPeq
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, hPeq]
  have hε : 0 < ε := by linarith
  have hP0 : 0 < P := by linarith
  calc |ν + 2 * b * P| ≤ |ν| + |2 * b * P| := abs_add_le _ _
    _ = |ν| + 2 * |b| * P := by rw [abs_mul, abs_mul, abs_two, abs_of_pos hP0]
    _ ≤ |ν| + 2 * |b| * |ε| := by
      rw [abs_of_pos hε]; gcongr

theorem K_mem {ν b ε α σ : ℝ} (hb : b ≠ 0) (h : ![σ, 1] ∈ OmegaAlpha 2 (OmegaE ν b ε) α) :
    ε / 2 < (σ - ν) / (2 * b) ∧ (σ - ν) / (2 * b) < ε := by
  obtain ⟨⟨-, P, ⟨hP1, hP2⟩, hPeq⟩, -, -⟩ := h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_one] at hPeq
  have : (σ - ν) / (2 * b) = P := by
    rw [hPeq]; field_simp; ring
  rw [this]
  exact ⟨hP1, hP2⟩

end ABC.S4.FinalAux
