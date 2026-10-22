/- Ported from root-parameter/project/N10Root/Calculus.lean (our earlier N10 root proof, Lean 4.33). -/
import ThomsonN10.Param.Definitions
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ThomsonN10.Param
noncomputable section

/-- Project-local differentiation rule, positive affine square-root denominator. -/
theorem affine_inv_sqrt_deriv (b c k a : ℝ) (hp : 0 < b + c*a) :
    HasDerivAt (fun x : ℝ => k / Real.sqrt (b + c*x))
      (-k*c / (2*(b+c*a)*Real.sqrt (b+c*a))) a := by
  have hs := Real.sqrt_pos.2 hp
  have h : HasDerivAt (fun x : ℝ => b + c*x) c a := by
    simpa using ((hasDerivAt_id a).const_mul c).const_add b
  have hd := (hasDerivAt_const a k).div (h.sqrt hp.ne') hs.ne'
  convert! hd using 1
  try dsimp only [Pi.mul_apply]
  field_simp [hs.ne', hp.ne']
  rw [Real.sq_sqrt hp.le]
  ring

/-- Differentiate the first derivative summands independently of E. -/
theorem affine_inv_three_halves_deriv (b c k a : ℝ) (hp : 0 < b+c*a) :
    HasDerivAt (fun x : ℝ => k / ((b+c*x)*Real.sqrt (b+c*x)))
      (-3*k*c / (2*(b+c*a)^2*Real.sqrt (b+c*a))) a := by
  have hs := Real.sqrt_pos.2 hp
  have h : HasDerivAt (fun x : ℝ => b + c*x) c a := by
    simpa using ((hasDerivAt_id a).const_mul c).const_add b
  have hd := (hasDerivAt_const a k).div (h.mul (h.sqrt hp.ne')) (mul_pos hp hs).ne'
  convert! hd using 1
  try dsimp only [Pi.mul_apply]
  field_simp [hs.ne', hp.ne']
  rw [Real.sq_sqrt hp.le]
  ring

theorem square_hasDerivAt (h : ℝ) : HasDerivAt (fun x : ℝ => x^2) (2*h) h := by
  convert! (hasDerivAt_id h).pow 2 using 1 <;> simp

theorem quadratic_linear_over_three_halves_deriv (b c k h : ℝ) (hp : 0 < b+c*h^2) :
    HasDerivAt (fun x : ℝ => k*x/((b+c*x^2)*Real.sqrt (b+c*x^2)))
      (k*(b-2*c*h^2)/((b+c*h^2)^2*Real.sqrt (b+c*h^2))) h := by
  have hs := Real.sqrt_pos.2 hp
  have d := (affine_inv_three_halves_deriv b c k (h^2) hp).comp h (h := fun x : ℝ => x^2) (square_hasDerivAt h)
  convert! (hasDerivAt_id h).mul d using 1
  · funext x
    dsimp only [Function.comp_def,id_eq,Pi.mul_apply]
    ring
  · dsimp only [Function.comp_def,id_eq,Pi.mul_apply]
    field_simp [hp.ne',hs.ne']
    ring

theorem energy_hasDerivAt {h : ℝ} (hh : h ∈ Set.Icc left right) :
    HasDerivAt energy (first h) h := by
  obtain ⟨h0,hc,hd,hm,hp⟩ := domains hh
  have hz : 0 < 1+(-1)*h^2 := by simpa [z] using h0
  have d0 := (affine_inv_sqrt_deriv 1 (-1) (4*r+2) (h^2) hz).comp h (h := fun x : ℝ => x^2) (square_hasDerivAt h)
  have d1 := (affine_inv_sqrt_deriv (2-r) (2+r) 8 (h^2) hc).comp h (h := fun x : ℝ => x^2) (square_hasDerivAt h)
  have d2 := (affine_inv_sqrt_deriv (2+r) (2-r) 8 (h^2) hd).comp h (h := fun x : ℝ => x^2) (square_hasDerivAt h)
  have d3 := affine_inv_sqrt_deriv 2 (-2) 8 h (by simpa [capMinus] using hm)
  have d4 := affine_inv_sqrt_deriv 2 2 8 h hp
  convert! (((((hasDerivAt_const h (1/2 : ℝ)).add d0).add d1).add d2).add d3).add d4 using 1
  · funext x
    simp [energy,z,dc,dd,capMinus,capPlus,Function.comp_def,sub_eq_add_neg]
  · dsimp [first,z,dc,dd,capMinus,capPlus,sub_eq_add_neg]
    simp only [neg_mul,one_mul,← sub_eq_add_neg]
    field_simp
    ring

theorem energy_derivative {h : ℝ} (hh : h ∈ Set.Icc left right) :
    deriv energy h = first h := (energy_hasDerivAt hh).deriv

theorem first_hasDerivAt {h : ℝ} (hh : h ∈ Set.Icc left right) :
    HasDerivAt first (second h) h := by
  obtain ⟨h0,hc,hd,hm,hp⟩ := domains hh
  have hz : 0 < 1+(-1)*h^2 := by simpa [z] using h0
  have d0 := quadratic_linear_over_three_halves_deriv 1 (-1) (4*r+2) h hz
  have d1 := quadratic_linear_over_three_halves_deriv (2-r) (2+r) (8*(2+r)) h hc
  have d2 := quadratic_linear_over_three_halves_deriv (2+r) (2-r) (8*(2-r)) h hd
  have d3 := affine_inv_three_halves_deriv 2 (-2) 8 h (by simpa [capMinus] using hm)
  have d4 := affine_inv_three_halves_deriv 2 2 8 h hp
  convert! ((((d0.sub d1).sub d2).add d3).sub d4) using 1
  · funext x
    simp [first,z,dc,dd,capMinus,capPlus,sub_eq_add_neg]
  · dsimp [second,z,dc,dd,capMinus,capPlus]
    simp only [neg_mul,one_mul,← sub_eq_add_neg]
    field_simp
    ring

theorem first_derivative {h : ℝ} (hh : h ∈ Set.Icc left right) :
    deriv first h = second h := (first_hasDerivAt hh).deriv
end
end ThomsonN10.Param
