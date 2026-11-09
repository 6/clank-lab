import ABC.S4.FlowHolo
import ABC.S4.FlowComplexAux

/-! L0b: complex time. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real
open ABC.Poschel2001 (Pt Ph DO OmegaAlpha ofRe ham Conclusion IsRealAnalyticOn)

noncomputable section

namespace ABC.S4

theorem flow_complex_time {n : ℕ} {F : Cn n → Cn n} {U : Set (Cn n)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {γ : ℝ → Cn n} {T : ℝ} (hT : 0 < T)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t ∧ γ t ∈ U) :
    ∃ s > 0, ∃ r > 0, ∃ φ : ℂ → Cn n → Cn n,
      DifferentiableOn ℂ (fun q : ℂ × Cn n => φ q.1 q.2)
        ({t | t.re ∈ Ioo (-s) (T + s) ∧ |t.im| < s} ×ˢ ball (γ 0) r) ∧
      ∀ x ∈ ball (γ 0) r, φ 0 x = x ∧ ∀ t : ℂ, t.re ∈ Ioo (-s) (T + s) → |t.im| < s →
        HasDerivAt (φ · x) (F (φ t x)) t ∧ φ t x ∈ U := by
  open ABC.S4.FlowComplexAux in
  obtain ⟨R, Φ, hΦ⟩ := exists_augFlow hU hF hγ
  -- the base points `(c, γ 0)`, `c ∈ [0, T]`, and a uniform neighbourhood of them
  have hK : IsCompact ((fun c : ℝ => aug (c : ℂ) (γ 0)) '' Icc 0 T) :=
    isCompact_Icc.image (differentiable_aug.continuous.comp
      (Complex.continuous_ofReal.prodMk continuous_const))
  have hKO : (fun c : ℝ => aug (c : ℂ) (γ 0)) '' Icc 0 T ⊆ augO γ T R := by
    rintro _ ⟨c, hc, rfl⟩
    exact mem_iUnion₂.2 ⟨c, hc, mem_ball_self (hΦ c hc).1⟩
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_thickening_subset_open isOpen_augO hKO
  set s := δ / 4 with hsdef
  have hs : 0 < s := by positivity
  set rect : Set ℂ := {t | t.re ∈ Ioo (-s) (T + s) ∧ |t.im| < s} with hrect
  have hrect_open : IsOpen rect :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hdom : ∀ t ∈ rect, ∀ x ∈ ball (γ 0) s, aug t x ∈ augO γ T R := by
    rintro t ⟨hre, him⟩ x hx
    apply hδO
    rw [mem_thickening_iff]
    set c := max 0 (min t.re T) with hcdef
    have hc : c ∈ Icc 0 T := ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
    refine ⟨aug (c : ℂ) (γ 0), ⟨c, hc, rfl⟩, ?_⟩
    rw [dist_aug_lt hδ]
    refine ⟨?_, (mem_ball.1 hx).trans (by linarith)⟩
    have hc1 : t.re - s < c :=
      lt_of_lt_of_le (lt_min (by linarith) (by linarith [hre.2])) (le_max_right _ _)
    have hc2 : c < t.re + s :=
      max_lt (by linarith [hre.1]) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hrc : |t.re - c| < s := abs_lt.2 ⟨by linarith, by linarith⟩
    rw [Complex.dist_eq]
    calc ‖t - c‖ ≤ |(t - c).re| + |(t - c).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |t.re - c| + |t.im| := by simp
      _ < δ := by linarith
  have hstar : ∀ t ∈ rect, ∀ σ ∈ Icc (0 : ℝ) 1, (σ : ℂ) * t ∈ rect := by
    rintro t ⟨hre, him⟩ σ hσ
    refine ⟨?_, ?_⟩
    · rw [Complex.re_ofReal_mul]
      rcases le_total 0 t.re with h | h
      · constructor <;> nlinarith [hre.1, hre.2, hσ.1, hσ.2]
      · constructor <;> nlinarith [hre.1, hre.2, hσ.1, hσ.2]
    · rw [Complex.im_ofReal_mul, abs_mul, abs_of_nonneg hσ.1]
      nlinarith [abs_nonneg t.im, hσ.1, hσ.2]
  set φ : ℂ → Cn n → Cn n := fun t x => Matrix.vecTail (Psi γ T R Φ 1 (aug t x)) with hφ
  have hdiff : DifferentiableOn ℂ (fun q : ℂ × Cn n => φ q.1 q.2) (rect ×ˢ ball (γ 0) s) :=
    differentiable_tail.comp_differentiableOn ((Psi_diff hU hF hΦ).comp
      differentiable_aug.differentiableOn (fun q hq => hdom q.1 hq.1 q.2 hq.2))
  refine ⟨s, hs, s, hs, φ, hdiff, fun x hx => ?_⟩
  -- scaling along segments `σ ↦ σ t`
  have hscal : ∀ t ∈ rect, ∃ c0 ∈ Icc 0 T, ∃ hv : aug t x ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0),
      ∀ σ ∈ Icc (0 : ℝ) 1, φ ((σ : ℂ) * t) x = Matrix.vecTail (Φ c0 σ (aug t x)) := by
    intro t ht
    obtain ⟨c0, hc0, hv⟩ : ∃ c0 ∈ Icc 0 T, aug t x ∈ ball (aug (c0 : ℂ) (γ 0)) (R c0) := by
      simpa [augO] using hdom t ht x hx
    exact ⟨c0, hc0, hv, scaling hU hF hΦ (fun σ hσ => hdom _ (hstar t ht σ hσ) x hx) hc0 hv⟩
  have h0rect : (0 : ℂ) ∈ rect := ⟨⟨by simp; linarith, by simp; linarith⟩, by simpa using hs⟩
  have hφ0 : φ 0 x = x := by
    obtain ⟨c0, hc0, hv, h⟩ := hscal 0 h0rect
    have := h 0 ⟨le_rfl, zero_le_one⟩
    rw [((hΦ c0 hc0).2.2 _ hv).1] at this
    simpa using this
  -- the real derivative along `σ ↦ σ t`
  have hal : ∀ t ∈ rect, ∀ σ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun σ : ℝ => φ ((σ : ℂ) * t) x)
      (t • F (φ ((σ : ℂ) * t) x)) (Icc 0 1) σ := by
    intro t ht σ hσ
    obtain ⟨c0, hc0, hv, h⟩ := hscal t ht
    have hv' := (hΦ c0 hc0).2.2 _ hv
    have hfc := first_coord hΦ hc0 hv
    have hd : HasDerivWithinAt (fun σ : ℝ => Matrix.vecTail (Φ c0 σ (aug t x)))
        (t • F (Matrix.vecTail (Φ c0 σ (aug t x)))) (Icc 0 1) σ := by
      refine hasDerivWithinAt_pi.2 fun j => ?_
      have := hasDerivWithinAt_pi.1 (hv'.2 σ hσ).1 j.succ
      rw [augF_succ, hfc σ hσ] at this
      simpa [Matrix.vecTail, aug] using this
    rw [h σ hσ]
    exact hd.congr (fun σ' hσ' => h σ' hσ') (h σ hσ)
  -- holomorphy in `t`
  have hhol : ∀ u ∈ rect, HasDerivAt (fun u => φ u x) (deriv (fun u => φ u x) u) u := by
    intro u hu
    have hJ : DifferentiableAt ℂ (fun q : ℂ × Cn n => φ q.1 q.2) (u, x) :=
      hdiff.differentiableAt ((hrect_open.prod isOpen_ball).mem_nhds ⟨hu, hx⟩)
    exact (hJ.comp u (differentiableAt_id.prodMk (differentiableAt_const x))).hasDerivAt
  have hkey : ∀ t ∈ rect, ∀ σ ∈ Icc (0 : ℝ) 1,
      t • deriv (fun u => φ u x) ((σ : ℂ) * t) = t • F (φ ((σ : ℂ) * t) x) := by
    intro t ht σ hσ
    have hh : HasDerivAt (fun σ : ℝ => (σ : ℂ) * t) t σ := by
      simpa using ((hasDerivAt_id σ).ofReal_comp).mul_const t
    have hc := (hhol _ (hstar t ht σ hσ)).scomp σ hh
    exact (uniqueDiffOn_Icc zero_lt_one σ hσ).eq_deriv _ hc.hasDerivWithinAt (hal t ht σ hσ)
  refine ⟨hφ0, fun t hre him => ?_⟩
  have ht : t ∈ rect := ⟨hre, him⟩
  refine ⟨?_, Psi_mem hU hF hΦ (hdom t ht x hx)⟩
  by_cases ht0 : t = 0
  · subst ht0
    set t' : ℂ := ((s / 2 : ℝ) : ℂ) with ht'
    have ht'r : t' ∈ rect := ⟨⟨by simp [ht']; linarith, by simp [ht']; linarith⟩,
      by simp [ht']; linarith⟩
    have ht'0 : t' ≠ 0 := by simp [ht']; exact hs.ne'
    have := hkey t' ht'r 0 ⟨le_rfl, zero_le_one⟩
    simp only [Complex.ofReal_zero, zero_mul] at this
    have h := smul_right_injective (Cn n) ht'0 this
    simpa [h] using hhol 0 h0rect
  · have := hkey t ht 1 ⟨zero_le_one, le_rfl⟩
    simp only [Complex.ofReal_one, one_mul] at this
    have h := smul_right_injective (Cn n) ht0 this
    simpa [h] using hhol t ht

end ABC.S4
