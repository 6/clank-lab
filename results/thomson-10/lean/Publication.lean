import Solution
import ThomsonN10.Admissible

/-! Packaging checks: the original statements and proofs are unchanged. -/

example : ThomsonN10.Challenge.CompleteTarget := ThomsonN10.thomson_ten_complete

example : ∀ h : ThomsonN10.CandidateParameter,
    ThomsonN10.IsSphereConfiguration (ThomsonN10.candidate h) :=
  ThomsonN10.candidate_admissible

/-- info: 'ThomsonN10.thomson_ten_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThomsonN10.thomson_ten_complete

/-- info: 'ThomsonN10.candidate_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThomsonN10.candidate_admissible

example : (10 : ℕ).choose 2 = 45 := by decide
example : (ThomsonN10.heightLower : ℚ) < ThomsonN10.heightUpper := by norm_num [ThomsonN10.heightLower, ThomsonN10.heightUpper]

/-- info: 'ThomsonN10.Cert.L1.Data.residual_agrees_JSON' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThomsonN10.Cert.L1.Data.residual_agrees_JSON
