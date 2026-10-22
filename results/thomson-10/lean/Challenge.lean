import ThomsonN10.Candidate

/-! Independent targets. These are propositions, not asserted theorems.
Same shape as the MIT N=9 Challenge.lean (aravindkarthigeyan/thomson-n9-lean @ 168ff0c). -/

namespace ThomsonN10.Challenge

def ParameterExistsUnique : Prop :=
  ∃! h : ℝ, (heightLower : ℝ) ≤ h ∧ h ≤ (heightUpper : ℝ) ∧ stationarity h = 0

def GlobalOptimality : Prop :=
  ∀ h : CandidateParameter, ∀ x : Configuration,
    IsSphereConfiguration x → coulombEnergy (candidate h) ≤ coulombEnergy x

def GlobalUniqueness : Prop :=
  ∀ h : CandidateParameter, ∀ x : Configuration,
    IsSphereConfiguration x →
    (coulombEnergy x = coulombEnergy (candidate h) ↔ Congruent x (candidate h))

def CompleteTarget : Prop := ParameterExistsUnique ∧ GlobalOptimality ∧ GlobalUniqueness

end ThomsonN10.Challenge
