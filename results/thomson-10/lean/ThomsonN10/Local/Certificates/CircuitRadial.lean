/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitRadial.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitDifferences

/-! Checked inverse-distance contributions to the constrained Hessian diagonal. -/

namespace ThomsonN10.Local.Certificates.IntervalCircuit

structure HalfInverseRecipe where
  distance : DistanceRecipe
  two : ℕ
  twice : ℕ
  inverse : ℕ
  negative : ℕ

structure HalfInverseRecipe.Check (nodes : ℕ → Node) (recipe : HalfInverseRecipe) : Prop where
  distance : recipe.distance.Check nodes
  two : (nodes recipe.two).op = .constant 2 1
  twice : SmartMulCheck nodes recipe.distance.root recipe.two recipe.twice
  inverse : (nodes recipe.inverse).op = .inv recipe.twice
  before : recipe.twice < recipe.inverse
  negative : ExtendedSmartNegCheck nodes recipe.inverse recipe.negative

theorem HalfInverseRecipe.sound (inputs : ℕ → ℝ) (nodes : ℕ → Node)
    (recipe : HalfInverseRecipe) (h : recipe.Check nodes) (p q : R3)
    (hdiff : ∀ a : Fin 3,
      value inputs nodes (recipe.distance.difference a) = p a-q a) :
    value inputs nodes recipe.negative = -(‖p-q‖⁻¹/2) := by
  rw [extendedSmartNeg_sound inputs nodes _ _ h.negative,
    value_inv inputs nodes _ _ h.inverse h.before,
    smartMul_sound inputs nodes _ _ _ h.twice,
    value_constant inputs nodes _ 2 1 h.two,
    recipe.distance.root_sound inputs nodes h.distance p q hdiff]
  norm_num [mul_inv_rev, div_eq_mul_inv, mul_comm]

#print axioms HalfInverseRecipe.sound

end ThomsonN10.Local.Certificates.IntervalCircuit
