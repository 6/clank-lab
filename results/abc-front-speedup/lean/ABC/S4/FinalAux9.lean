import Mathlib

/-! Final, part 4: choice of the small parameter `e = ε^{1/8}`. -/

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.FinalAux

lemma pow8_rpow {e : ℝ} (he : 0 ≤ e) (q : ℝ) (n : ℕ) (hq : 8 * q = n) :
    (e ^ 8) ^ q = e ^ n := by
  rw [← Real.rpow_natCast e 8, ← Real.rpow_mul he, ← Real.rpow_natCast]
  congr 1

lemma ev_small {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0) {k : ℝ} (hk : 0 < k) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), f e < k := by
  have : ∀ᶠ e in 𝓝 (0 : ℝ), f e < k :=
    (hf.tendsto 0).eventually (gt_mem_nhds (by rw [h0]; exact hk))
  exact this.filter_mono nhdsWithin_le_nhds

lemma small_e {ε₀ a₁ a₂ a₃ ρ₁ ρ₂ B N : ℝ} (hε₀ : 0 < ε₀) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hB : 0 < B) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧ e ^ 8 < ε₀ ∧ a₁ * e < 1 / 8 ∧ a₂ * e ^ 2 < 1 ∧
      a₃ * e ^ 2 + e ^ 2 < 1 / 2 ∧ 2 * (e ^ 8 + e ^ 10) < ρ₁ ^ 2 ∧
      2 * (e ^ 8 + a₃ * e ^ 10 + e ^ 10) < ρ₂ ^ 2 ∧ 8 * B * e ^ 9 + 16 * e * N < B := by
  have h1 := ev_small (f := fun e : ℝ => e) continuous_id rfl one_pos
  have h2 := ev_small (f := fun e : ℝ => e ^ 8) (by fun_prop) (by simp) hε₀
  have h3 := ev_small (f := fun e : ℝ => a₁ * e) (by fun_prop) (by simp)
    (by norm_num : (0 : ℝ) < 1 / 8)
  have h4 := ev_small (f := fun e : ℝ => a₂ * e ^ 2) (by fun_prop) (by simp) one_pos
  have h5 := ev_small (f := fun e : ℝ => a₃ * e ^ 2 + e ^ 2) (by fun_prop) (by simp)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have h6 := ev_small (f := fun e : ℝ => 2 * (e ^ 8 + e ^ 10)) (by fun_prop) (by simp)
    (pow_pos hρ₁ 2)
  have h7 := ev_small (f := fun e : ℝ => 2 * (e ^ 8 + a₃ * e ^ 10 + e ^ 10)) (by fun_prop)
    (by simp) (pow_pos hρ₂ 2)
  have h8 := ev_small (f := fun e : ℝ => 8 * B * e ^ 9 + 16 * e * N) (by fun_prop) (by simp) hB
  have h0 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
  obtain ⟨e, he⟩ := (h0.and (h1.and (h2.and (h3.and (h4.and (h5.and (h6.and (h7.and h8)))))))).exists
  exact ⟨e, he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2.1,
    he.2.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2⟩

end ABC.S4.FinalAux
