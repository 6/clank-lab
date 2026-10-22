/- Adapted from the contact_bounds and exterior_gap bridges in
   proof/lean/ThomsonN9/Bernstein/Minorant.lean and
   proof/lean/ClaudeL2b/RefinedWindows.lean,
   aravindkarthigeyan/thomson-n9-lean, MIT, commit
   168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import ThomsonN10.Scalar.CertificateData
namespace ThomsonN10.Scalar

/-- The seven contacts in increasing order. -/
def contactOrder : Fin 7 → Fin 7 := ![0, 6, 4, 2, 3, 5, 1]

/-- Exact rational enclosures valid throughout the height box. -/
theorem contact_bounds (h : CandidateParameter) (j : Fin 7) :
    (contactLo j : ℝ) ≤ contact h (contactOrder j) ∧
      contact h (contactOrder j) ≤ (contactHi j : ℝ) := by
  have hhl : (coarseHL : ℝ) ≤ (h : ℝ) := by
    have : (coarseHL : ℝ) ≤ (heightLower : ℝ) := by
      norm_num [coarseHL, heightLower]
    exact this.trans h.property.1
  have hhu : (h : ℝ) ≤ (coarseHU : ℝ) := by
    have : (heightUpper : ℝ) ≤ (coarseHU : ℝ) := by
      norm_num [coarseHU, heightUpper]
    exact h.property.2.1.trans this
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by
    have : (0 : ℝ) ≤ coarseHL := by norm_num [coarseHL]
    linarith
  have hsqlo : (coarseHL : ℝ)^2 ≤ (h : ℝ)^2 := by
    have : (0 : ℝ) ≤ coarseHL := by norm_num [coarseHL]
    nlinarith
  have hsqhi : (h : ℝ)^2 ≤ (coarseHU : ℝ)^2 := by
    have : (0 : ℝ) ≤ coarseHU := by norm_num [coarseHU]
    nlinarith
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hslo : (sqrtLo : ℝ) ≤ Real.sqrt 2 := by
    have hl : (0 : ℝ) ≤ sqrtLo := by norm_num [sqrtLo]
    have hb : (sqrtLo : ℝ)^2 ≤ 2 := by norm_num [sqrtLo]
    nlinarith
  have hshi : Real.sqrt 2 ≤ (sqrtHi : ℝ) := by
    have hl : (0 : ℝ) ≤ sqrtHi := by norm_num [sqrtHi]
    have hb : (2 : ℝ) ≤ (sqrtHi : ℝ)^2 := by norm_num [sqrtHi]
    nlinarith
  have hprodlo : (1-(coarseHU : ℝ)^2)*(sqrtLo : ℝ) ≤
      (1-(h : ℝ)^2)*Real.sqrt 2 := by
    exact mul_le_mul (by linarith) hslo
      (by norm_num [sqrtLo]) (by
        have : (coarseHU : ℝ)^2 ≤ 1 := by norm_num [coarseHU]
        linarith)
  have hprodhi : (1-(h : ℝ)^2)*Real.sqrt 2 ≤
      (1-(coarseHL : ℝ)^2)*(sqrtHi : ℝ) := by
    exact mul_le_mul (by linarith) hshi hs0 (by norm_num [coarseHL])
  have hdiv : (1-(h : ℝ)^2)/Real.sqrt 2 = (1-(h : ℝ)^2)*Real.sqrt 2/2 := by
    have hsne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  norm_num [coarseHL, coarseHU] at hhl hhu hsqlo hsqhi hprodlo hprodhi
  norm_num [sqrtLo, sqrtHi] at hprodlo hprodhi
  fin_cases j <;>
    simp only [contactOrder, contactLo, contactHi, contact, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.head_cons, neg_div, hdiv] <;>
    norm_num <;> constructor <;> nlinarith

end ThomsonN10.Scalar
