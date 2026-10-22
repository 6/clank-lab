import ThomsonN10.Cert.CandidateEnergy
import ThomsonN10.Cert.Upper

namespace ThomsonN10.Cert

theorem CandidateUpper_holds : ThomsonN10.Interfaces.CandidateUpper := by
  constructor
  · intro h
    have hh : 0 < (h : ℝ) ∧ (h : ℝ) < 1 := by
      have hl := h.property.1
      have hu := h.property.2.1
      have hL : (0 : ℝ) < heightLower := by norm_num [heightLower]
      have hU : (heightUpper : ℝ) < 1 := by norm_num [heightUpper]
      exact ⟨hL.trans_le hl, hu.trans_lt hU⟩
    change coulombEnergy (candidateAt h) ≤ _
    rw [CE.energy_eq hh]
    exact Upper.familyEnergy_upper h
  · norm_num [certU, energyCap]

end ThomsonN10.Cert
#print axioms ThomsonN10.Cert.CandidateUpper_holds
