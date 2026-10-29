import LabelTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section

def affineKernel {𝕜 : Type*} [Field 𝕜] {d : ℕ}
    (K : Matrix (Fin d) (Fin (d + 1)) 𝕜) : Fin (d + 1) → 𝕜 :=
  Fin.cons 1 (-((K.submatrix id Fin.succ)⁻¹ *ᵥ (fun i => K i 0)))

theorem affineKernel_equation {𝕜 : Type*} [Field 𝕜] {d : ℕ}
    (K : Matrix (Fin d) (Fin (d + 1)) 𝕜)
    (hd : (K.submatrix id Fin.succ).det ≠ 0) :
    K *ᵥ affineKernel K = 0 := by
  let B := K.submatrix id Fin.succ
  have hi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hd)
  have hv : B *ᵥ (-(B⁻¹ *ᵥ (fun i => K i 0))) = -(fun i => K i 0) := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec]
  ext i
  have he := congrFun hv i
  change ∑ j, K i j.succ * (-(B⁻¹ *ᵥ (fun k => K k 0))) j = -K i 0 at he
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, affineKernel,
    Fin.cons_zero, Fin.cons_succ, mul_one, Pi.zero_apply]
  change K i 0 + (∑ j, K i j.succ * (-(B⁻¹ *ᵥ (fun k => K k 0))) j) = 0
  rw [he, add_neg_cancel]

theorem affineKernel_unique {𝕜 : Type*} [Field 𝕜] {d : ℕ}
    (K : Matrix (Fin d) (Fin (d + 1)) 𝕜)
    (hd : (K.submatrix id Fin.succ).det ≠ 0)
    (v w : Fin (d + 1) → 𝕜) (hv0 : v 0 = 1) (hw0 : w 0 = 1)
    (hv : K *ᵥ v = 0) (hw : K *ᵥ w = 0) : v = w := by
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have ht : (fun j : Fin d => v j.succ) = (fun j : Fin d => w j.succ) := by
    apply hinj
    ext i
    have h1 := congrFun hv i
    have h2 := congrFun hw i
    change K i ⬝ᵥ v = 0 at h1
    change K i ⬝ᵥ w = 0 at h2
    simp only [dotProduct, Fin.sum_univ_succ, hv0, hw0, mul_one] at h1 h2
    change (∑ j : Fin d, K i j.succ * v j.succ) = ∑ j : Fin d, K i j.succ * w j.succ
    exact add_left_cancel (h1.trans h2.symm)
  ext i
  refine Fin.cases (hv0.trans hw0.symm) (fun j => congrFun ht j) i

/-- A real chart-normalized vertex on a rational nonsingular active basis
    is exactly the canonical rational kernel. Thus subsequent finite label
    reasoning covers real covectors too, not merely supplied rational rays. -/
theorem real_chart_kernel_rational {d : ℕ}
    (K : Matrix (Fin d) (Fin (d + 1)) ℚ)
    (hd : (K.submatrix id Fin.succ).det ≠ 0)
    (v : Fin (d + 1) → ℝ) (hv0 : v 0 = 1)
    (hv : (K.map (Rat.castHom ℝ)) *ᵥ v = 0) :
    v = fun j => ((affineKernel K j : ℚ) : ℝ) := by
  let R := K.map (Rat.castHom ℝ)
  have hr : (R.submatrix id Fin.succ).det ≠ 0 := by
    have he := Rat.cast_det (F := ℝ) (K.submatrix id Fin.succ)
    change (((K.submatrix id Fin.succ).det : ℚ) : ℝ) = (R.submatrix id Fin.succ).det at he
    rw [← he]
    exact Rat.cast_ne_zero.mpr hd
  have hq := affineKernel_equation K hd
  have hw : R *ᵥ (fun j => ((affineKernel K j : ℚ) : ℝ)) = 0 := by
    ext i
    have h := congrFun hq i
    change ∑ j, (K i j : ℝ) * ((affineKernel K j : ℚ) : ℝ) = 0
    change ∑ j, K i j * affineKernel K j = 0 at h
    exact_mod_cast h
  exact affineKernel_unique R hr v _ hv0 (by simp [affineKernel]) hv hw

#print axioms affineKernel_equation
#print axioms affineKernel_unique
#print axioms real_chart_kernel_rational
end
end ADKZPricing
