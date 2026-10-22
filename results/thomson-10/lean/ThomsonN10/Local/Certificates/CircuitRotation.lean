/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitRotation.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitDifferences

/-! The three rotation columns are checked signed coordinate copies. -/

namespace ThomsonN10.Local.Certificates.IntervalCircuit

def RotationCheck (nodes : ℕ → Node) (point : Fin 10 → Fin 3 → ℕ)
    (output : Fin 10 → Fin 3 → Fin 3 → ℕ) : Prop :=
  ∀ i : Fin 10,
    ZeroAt nodes (output i 0 0) ∧ output i 0 1 = point i 2 ∧
    ExtendedSmartNegCheck nodes (point i 1) (output i 0 2) ∧
    ExtendedSmartNegCheck nodes (point i 2) (output i 1 0) ∧
    ZeroAt nodes (output i 1 1) ∧ output i 1 2 = point i 0 ∧
    output i 2 0 = point i 1 ∧
    ExtendedSmartNegCheck nodes (point i 0) (output i 2 1) ∧
    ZeroAt nodes (output i 2 2)

instance (nodes : ℕ → Node) (point : Fin 10 → Fin 3 → ℕ)
    (output : Fin 10 → Fin 3 → Fin 3 → ℕ) :
    Decidable (RotationCheck nodes point output) := by
  unfold RotationCheck ZeroAt
  infer_instance

theorem rotation_recipe_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node)
    (point : Fin 10 → Fin 3 → ℕ) (output : Fin 10 → Fin 3 → Fin 3 → ℕ)
    (h : RotationCheck nodes point output) (p : Configuration)
    (hp : ∀ i a, value inputs nodes (point i a) = p i a)
    (i : Fin 10) (a k : Fin 3) :
    value inputs nodes (output i a k) = rotationColumns p (i,a) k := by
  obtain ⟨h00,h01,h02,h10,h11,h12,h20,h21,h22⟩ := h i
  have v00 := zeroAt_sound inputs nodes _ h00
  have v02 := extendedSmartNeg_sound inputs nodes _ _ h02
  have v10 := extendedSmartNeg_sound inputs nodes _ _ h10
  have v11 := zeroAt_sound inputs nodes _ h11
  have v21 := extendedSmartNeg_sound inputs nodes _ _ h21
  have v22 := zeroAt_sound inputs nodes _ h22
  fin_cases a <;> fin_cases k <;>
    simp_all [rotationColumns]

#print axioms rotation_recipe_sound

end ThomsonN10.Local.Certificates.IntervalCircuit
