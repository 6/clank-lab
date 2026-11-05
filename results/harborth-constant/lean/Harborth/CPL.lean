import Harborth.SLC

/-! Concentrated Profile Lemma, assembled from `shape_lemma`, `slc` and `exceptional_cpl`. -/

namespace Harborth

/-- Concentrated Profile Lemma. -/
theorem cpl {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p) (v : ZMod p → ℕ)
    (hv : ∀ g, v g ≤ p - 1) (hsum : ∑ g, v g = 2 * p - 1)
    (hconc : 2 * p - 4 ≤ ∑ g, (v g).choose 2) :
    ∃ t : ZMod p → ℕ, (∀ g, t g ≤ v g) ∧ ∑ g, t g = p ∧
      ∑ g, (t g : ZMod p) * g = 0 ∧ p - 1 ≤ ∑ g, t g * (v g - t g) := by
  rcases shape_lemma hp v hv hsum hconc with ⟨r, hr⟩ | he
  · exact slc (by omega) v r hsum hr
  · exact exceptional_cpl (by omega) v hsum he

end Harborth
