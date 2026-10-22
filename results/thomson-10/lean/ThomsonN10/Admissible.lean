import ThomsonN10.Cert.CandidateEnergy

/-! The candidate is admissible: for every parameter in the set, it is ten distinct unit
vectors. (`Challenge.CompleteTarget` does not assert this separately; it is proved here so
that the optimality statement is about an actual competitor.) -/

namespace ThomsonN10

theorem candidate_admissible (h : CandidateParameter) : IsSphereConfiguration (candidate h) := by
  have hh : 0 < (h : ℝ) ∧ (h : ℝ) < 1 := by
    have hl := h.property.1
    have hu := h.property.2.1
    have hL : (0 : ℝ) < heightLower := by norm_num [heightLower]
    have hU : (heightUpper : ℝ) < 1 := by norm_num [heightUpper]
    exact ⟨hL.trans_le hl, hu.trans_lt hU⟩
  exact ⟨fun i => Cert.CE.unit_norm hh i, Cert.CE.cand_injective hh⟩

#print axioms candidate_admissible

end ThomsonN10
