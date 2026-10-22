/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitDifferences.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitPairBlock
import ThomsonN10.Local.Certificates.CircuitCoordinates

/-! Checked constant negation and coordinate differences, independently of bounds. -/

namespace ThomsonN10.Local.Certificates.IntervalCircuit

def ConstantNegCheck (nodes : ℕ → Node) (a out : ℕ) : Prop :=
  let an := constantNum (nodes a).op
  let ad := constantDen (nodes a).op
  let cn := constantNum (nodes out).op
  let cd := constantDen (nodes out).op
  (nodes a).op = .constant an ad ∧ (nodes out).op = .constant cn cd ∧
    0 < ad ∧ 0 < cd ∧ cn*ad = -an*cd

instance (nodes : ℕ → Node) (a out : ℕ) : Decidable (ConstantNegCheck nodes a out) := by
  unfold ConstantNegCheck
  infer_instance

theorem constantNeg_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a out : ℕ)
    (h : ConstantNegCheck nodes a out) :
    value inputs nodes out = -value inputs nodes a := by
  rcases h with ⟨ha,hc,hda,hdc,hcross⟩
  rw [value_constant inputs nodes out _ _ hc, value_constant inputs nodes a _ _ ha]
  have ha' : (constantDen (nodes a).op : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hda)
  have hc' : (constantDen (nodes out).op : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hdc)
  have h' : (constantNum (nodes out).op : ℝ)*constantDen (nodes a).op =
      -(constantNum (nodes a).op : ℝ)*constantDen (nodes out).op := by
    exact_mod_cast hcross
  field_simp [ha',hc']
  nlinarith

def ExtendedSmartNegCheck (nodes : ℕ → Node) (a out : ℕ) : Prop :=
  SmartNegCheck nodes a out ∨ ConstantNegCheck nodes a out

instance (nodes : ℕ → Node) (a out : ℕ) :
    Decidable (ExtendedSmartNegCheck nodes a out) := by
  unfold ExtendedSmartNegCheck
  infer_instance

theorem extendedSmartNeg_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a out : ℕ)
    (h : ExtendedSmartNegCheck nodes a out) :
    value inputs nodes out = -value inputs nodes a := by
  rcases h with h | h
  · exact smartNeg_sound inputs nodes a out h
  · exact constantNeg_sound inputs nodes a out h

structure DifferenceRecipe where
  left : Fin 3 → ℕ
  right : Fin 3 → ℕ
  negative : Fin 3 → ℕ
  output : Fin 3 → ℕ

def DifferenceRecipe.Check (nodes : ℕ → Node) (recipe : DifferenceRecipe) : Prop :=
  ∀ a : Fin 3, ExtendedSmartNegCheck nodes (recipe.right a) (recipe.negative a) ∧
    ExtendedSmartAddCheck nodes (recipe.left a) (recipe.negative a) (recipe.output a)

instance (nodes : ℕ → Node) (recipe : DifferenceRecipe) : Decidable (recipe.Check nodes) := by
  unfold DifferenceRecipe.Check
  infer_instance

theorem DifferenceRecipe.sound (inputs : ℕ → ℝ) (nodes : ℕ → Node)
    (recipe : DifferenceRecipe) (h : recipe.Check nodes) (a : Fin 3) :
    value inputs nodes (recipe.output a) =
      value inputs nodes (recipe.left a)-value inputs nodes (recipe.right a) := by
  rw [extendedSmartAdd_sound inputs nodes _ _ _ (h a).2,
    extendedSmartNeg_sound inputs nodes _ _ (h a).1]
  rfl

theorem DifferenceRecipe.candidate_sound (r : ℝ) (nodes : ℕ → Node)
    (hcoords : CoordinateCheck nodes) (recipe : DifferenceRecipe)
    (h : recipe.Check nodes) (i j : Fin 10)
    (hl : ∀ a, recipe.left a = pointIndices i a)
    (hr : ∀ a, recipe.right a = pointIndices j a) (a : Fin 3) :
    value (parameterInputs r) nodes (recipe.output a) =
      candidateAt r i a-candidateAt r j a := by
  rw [recipe.sound _ _ h, hl, hr, coordinate_recipe_sound r nodes hcoords,
    coordinate_recipe_sound r nodes hcoords]

#print axioms extendedSmartNeg_sound
#print axioms DifferenceRecipe.candidate_sound

end ThomsonN10.Local.Certificates.IntervalCircuit
