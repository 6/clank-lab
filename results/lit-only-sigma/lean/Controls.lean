import LitOnlySigma

namespace LitOnlySigma

/-- The existing corruption removes state 45 from the closure certificate. -/
def corruptCodes : Fin 9 → ℕ := ![27, 54, 63, 71, 78, 92, 99, 113, 120]

/-- Kernel rejection of the same corruption rejected by the independent checkers. -/
theorem rejects_deleted_state : ¬ (∀ i : Fin 9, ∀ v : Fin 7, ∃ j : Fin 9,
    litOnlyMove graph (decode (corruptCodes i)) v = decode (corruptCodes j)) := by
  decide

/-- Concretely, state 78 played at the lit vertex 3 reaches the deleted state 45. -/
theorem missing_successor : litOnlyMove graph (decode 78) 3 = decode 45 ∧
    ∀ i : Fin 9, decode (corruptCodes i) ≠ decode 45 := by decide

end LitOnlySigma
