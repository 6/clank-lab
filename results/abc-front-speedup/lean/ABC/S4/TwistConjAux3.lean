import ABC.S4.TwistConjAux2

/-! T1 helpers: the coordinate `x = p + v w + v̄ w̄`. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

set_option linter.unusedSimpArgs false

noncomputable section

namespace ABC.S4.TwistConjAux

open ABC

/-- the determinant of `(v, v̄)` -/
def dv (v : C2) : ℂ := v 0 * conj (v 1) - v 1 * conj (v 0)

theorem dv_ne {v : C2} (hv : (v 0 * conj (v 1)).im ≠ 0) : dv v ≠ 0 := by
  intro h
  apply hv
  have h' : v 0 * conj (v 1) - conj (v 0 * conj (v 1)) = 0 := by
    rw [map_mul, Complex.conj_conj, ← h, dv]; ring
  have := congrArg Complex.im h'
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith

theorem conj_dv (v : C2) : conj (dv v) = -dv v := by
  simp only [dv, map_sub, map_mul, Complex.conj_conj]; ring

theorem ofW_apply (v : C2) (w : ℂ) (i : Fin 2) :
    (ofW v w i : ℂ) = v i * w + conj (v i) * conj w := by
  fin_cases i <;>
  · simp only [ofW, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.re_eq_add_conj, map_mul]
    ring

theorem toW_eq (v : C2) (x : E 2) :
    toW v x = ((x 0 : ℂ) * conj (v 1) - (x 1 : ℂ) * conj (v 0)) / dv v := rfl

theorem toW_ofW {v : C2} (hv : (v 0 * conj (v 1)).im ≠ 0) (w : ℂ) : toW v (ofW v w) = w := by
  rw [toW_eq, ofW_apply, ofW_apply, div_eq_iff (dv_ne hv), dv]; ring

theorem ofW_toW {v : C2} (hv : (v 0 * conj (v 1)).im ≠ 0) (x : E 2) : ofW v (toW v x) = x := by
  have hd := dv_ne hv
  have hc := conj_dv v
  ext i
  apply Complex.ofReal_injective
  rw [ofW_apply, toW_eq, map_div₀, hc]
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  field_simp
  fin_cases i <;> simp [dv] <;> ring

theorem ofW_add (v : C2) (w z : ℂ) : ofW v (w + z) = ofW v w + ofW v z := by
  ext i; apply Complex.ofReal_injective
  simp only [ofW_apply, PiLp.add_apply, Complex.ofReal_add, map_add]; ring

theorem ofW_smul (v : C2) (r : ℝ) (w : ℂ) : ofW v (r • w) = r • ofW v w := by
  ext i; apply Complex.ofReal_injective
  simp only [ofW_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul,
    map_mul, Complex.conj_ofReal]; ring

/-- `ofW v` as a real linear equivalence -/
def ofWE (v : C2) (hv : (v 0 * conj (v 1)).im ≠ 0) : ℂ ≃ₗ[ℝ] E 2 where
  toFun := ofW v
  invFun := toW v
  map_add' := ofW_add v
  map_smul' := ofW_smul v
  left_inv := toW_ofW hv
  right_inv := ofW_toW hv

/-- the same as a continuous linear equivalence -/
def ofWC (v : C2) (hv : (v 0 * conj (v 1)).im ≠ 0) : ℂ ≃L[ℝ] E 2 :=
  (ofWE v hv).toContinuousLinearEquiv

@[simp] theorem ofWC_apply {v : C2} (hv : (v 0 * conj (v 1)).im ≠ 0) (w : ℂ) :
    ofWC v hv w = ofW v w := rfl

@[simp] theorem ofWC_symm_apply {v : C2} (hv : (v 0 * conj (v 1)).im ≠ 0) (x : E 2) :
    (ofWC v hv).symm x = toW v x := rfl


/-! ### the algebra of `β` -/

theorem normsq_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `β` is invariant under a tangent-to-identity conjugacy `η` when `|λ| = 1` -/
theorem beta_tangent {a b η : ℕ → ℕ → ℂ} (hη0 : η 0 0 = 0) (hη1 : η 0 1 = 0) (hη10 : η 1 0 = 1)
    (hL : a 1 0 * conj (a 1 0) = 1) (hnr : (a 1 0).im ≠ 0)
    (hnres : a 1 0 ^ 2 ≠ a 1 0 ∧ a 1 0 ^ 2 ≠ conj (a 1 0))
    (h : comp b η 0 0 = comp η a 0 0 ∧ comp b η 1 0 = comp η a 1 0 ∧
      comp b η 0 1 = comp η a 0 1 ∧ comp b η 2 0 = comp η a 2 0 ∧
      comp b η 1 1 = comp η a 1 1 ∧ comp b η 0 2 = comp η a 0 2 ∧
      comp b η 3 0 = comp η a 3 0 ∧ comp b η 2 1 = comp η a 2 1 ∧
      comp b η 1 2 = comp η a 1 2 ∧ comp b η 0 3 = comp η a 0 3) :
    b 0 0 = 0 ∧ b 1 0 = a 1 0 ∧ b 0 1 = 0 ∧ birkhoffBeta b = birkhoffBeta a := by
  obtain ⟨e00, e10, e01, e20, e11, e02, -, e21, -, -⟩ := h
  simp only [comp, hη0, hη1, hη10, map_one, map_zero, one_pow, mul_one, one_mul,
    mul_zero, zero_mul, add_zero, zero_add] at e00 e10 e01 e20 e11 e02 e21
  set l := a 1 0 with hl
  have hb10 : b 1 0 = l := e10
  have hb01 : b 0 1 = 0 := e01
  rw [hb10, hb01] at e20 e11 e02 e21
  simp only [mul_zero, zero_mul, add_zero, zero_add] at e20 e11 e02 e21
  have hb20 : b 2 0 = a 2 0 + η 2 0 * (l ^ 2 - l) := by linear_combination e20
  have hb11 : b 1 1 = a 1 1 + η 1 1 * (l * conj l - l) := by linear_combination e11
  have hb02 : b 0 2 = a 0 2 + η 0 2 * (conj l ^ 2 - l) := by linear_combination e02
  rw [hb20, hb11, hb02] at e21
  have hb21 : b 2 1 = η 2 1 * l ^ 2 * conj l + 2 * η 2 0 * l * a 1 1
      + η 1 1 * l * conj (a 1 1) + η 1 1 * a 2 0 * conj l + a 2 1
      + 2 * η 0 2 * conj (a 0 2) * conj l - (2 * (a 2 0 + η 2 0 * (l ^ 2 - l)) * η 1 1
      + (a 1 1 + η 1 1 * (l * conj l - l)) * conj (η 1 1)
      + (a 1 1 + η 1 1 * (l * conj l - l)) * η 2 0 + l * η 2 1
      + 2 * (a 0 2 + η 0 2 * (conj l ^ 2 - l)) * conj (η 0 2)) := by
    linear_combination e21
  refine ⟨e00, hb10, hb01, ?_⟩
  have hl0 : l ≠ 0 := by rintro h0; rw [h0] at hL; simp at hL
  have hcl : conj l = l⁻¹ := eq_inv_of_mul_eq_one_right hL
  have hl1 : l - 1 ≠ 0 := by
    intro h1; apply hnr; rw [sub_eq_zero.1 h1]; simp
  have h1l : 1 - l ≠ 0 := by intro h1; apply hl1; linear_combination -h1
  have hl2 : l ^ 2 - l ≠ 0 := sub_ne_zero.2 hnres.1
  have hl3 : l ^ 3 - 1 ≠ 0 := by
    intro h3; apply hnres.2; rw [hcl]; field_simp; linear_combination h3
  have hl2' : l ^ 2 - l⁻¹ ≠ 0 := by rw [← hcl]; exact sub_ne_zero.2 hnres.2
  have h1l' : 1 - l⁻¹ ≠ 0 := by
    rw [show 1 - l⁻¹ = (l - 1) / l by field_simp]; exact div_ne_zero hl1 hl0
  have hm : ((‖l‖ ^ 2 : ℝ) : ℂ) = 1 := by rw [normsq_eq]; exact hL
  unfold birkhoffBeta
  simp only [normsq_eq, hb10, hb20, hb11, hb02, hb21, ← hl]
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, Complex.conj_conj, hL]
  simp only [hcl, map_one]
  field_simp
  ring

end ABC.S4.TwistConjAux
