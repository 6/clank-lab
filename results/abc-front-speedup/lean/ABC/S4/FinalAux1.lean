import Mathlib

open Set Metric Filter Topology Real

noncomputable section

namespace ABC.S4.FinalAux

/-- A bounded holomorphic function on the strip `|Im z| < w` is Lipschitz on `ℝ`. -/
theorem strip_lip {f : ℂ → ℂ} {w M : ℝ} (hw : 0 < w)
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < w})
    (hM : ∀ z : ℂ, |z.im| < w → ‖f z‖ ≤ M) (a b : ℝ) :
    ‖f a - f b‖ ≤ 2 * M / w * |a - b| := by
  have hopen : IsOpen {z : ℂ | |z.im| < w} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hw2 : 0 < w / 2 := by positivity
  have hsub : ∀ x : ℝ, closedBall (x : ℂ) (w / 2) ⊆ {z : ℂ | |z.im| < w} := by
    intro x z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - (x : ℂ)).im| ≤ ‖z - (x : ℂ)‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
    show |z.im| < w
    linarith
  have hderiv : ∀ x : ℝ, ‖deriv f (x : ℂ)‖ ≤ 2 * M / w := by
    intro x
    have hd : DiffContOnCl ℂ f (ball (x : ℂ) (w / 2)) :=
      (hf.mono (hsub x)).diffContOnCl_ball subset_rfl
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hw2 hd
      (C := M) (fun z hz => hM z (hsub x (sphere_subset_closedBall hz)))
    calc ‖deriv f (x : ℂ)‖ ≤ M / (w / 2) := this
      _ = 2 * M / w := by field_simp
  have hhas : ∀ x : ℝ, HasDerivAt (fun t : ℝ => f (t : ℂ)) (deriv f (x : ℂ)) x := by
    intro x
    have hx : (x : ℂ) ∈ {z : ℂ | |z.im| < w} := by
      show |(x : ℂ).im| < w
      simpa using hw
    have := ((hf (x : ℂ) hx).differentiableAt (hopen.mem_nhds hx)).hasDerivAt
    exact this.comp_ofReal
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := univ)
    (f := fun t : ℝ => f (t : ℂ)) (C := 2 * M / w)
    (fun x _ => (hhas x).differentiableAt)
    (fun x _ => by rw [(hhas x).deriv]; exact hderiv x) convex_univ
    (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using hmv

end ABC.S4.FinalAux
