/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitMatrices.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitConstants

/-! Work draft: exact finite dot-product recipes identify matrix multiplication. -/

namespace ThomsonN10.Local.Certificates.IntervalCircuit

open scoped BigOperators

instance (nodes : ℕ → Node) (i : ℕ) : Decidable (ZeroAt nodes i) := by
  unfold ZeroAt
  infer_instance

instance (nodes : ℕ → Node) (i : ℕ) : Decidable (OneAt nodes i) := by
  unfold OneAt
  infer_instance

def DotRecipe.checkBool (nodes : ℕ → Node) (n : ℕ) (recipe : DotRecipe) : Bool :=
  decide (ZeroAt nodes (recipe.accumulator 0)) && (List.range n).all (fun k =>
    decide (SmartMulCheck nodes (recipe.left k) (recipe.right k) (recipe.product k) ∧
      SmartAddCheck nodes (recipe.accumulator k) (recipe.product k) (recipe.accumulator (k+1))))

theorem DotRecipe.checkBool_sound (nodes : ℕ → Node) (n : ℕ) (recipe : DotRecipe)
    (h : recipe.checkBool nodes n = true) : recipe.Check nodes n := by
  rw [DotRecipe.checkBool, Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1, ?_⟩
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h.2 k (List.mem_range.mpr hk))

theorem DotRecipe.sound_fin (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (recipe : DotRecipe) (h : recipe.Check nodes n) :
    value inputs nodes (recipe.accumulator n) =
      ∑ k : Fin n, value inputs nodes (recipe.left k)*value inputs nodes (recipe.right k) :=
  (recipe.sound inputs nodes n h).trans
    (Finset.sum_range (fun k => value inputs nodes (recipe.left k)*value inputs nodes (recipe.right k)))

theorem DotRecipe.extended_sound_fin (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (recipe : DotRecipe) (h : recipe.ExtendedCheck nodes n) :
    value inputs nodes (recipe.accumulator n) =
      ∑ k : Fin n, value inputs nodes (recipe.left k)*value inputs nodes (recipe.right k) :=
  (recipe.extended_sound inputs nodes n h).trans
    (Finset.sum_range (fun k => value inputs nodes (recipe.left k)*value inputs nodes (recipe.right k)))

noncomputable def matrixValues (V : ℕ → ℝ) (n : ℕ) (indices : ℕ → ℕ → ℕ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => V (indices i j)

def OutputWithin (scale : ℤ) (a : ScaledInterval) (b : RatInterval) : Prop :=
  b.lo ≤ (a.rational scale).lo ∧ (a.rational scale).hi ≤ b.hi

instance (scale : ℤ) (a : ScaledInterval) (b : RatInterval) : Decidable (OutputWithin scale a b) := by
  unfold OutputWithin
  infer_instance

theorem outputWithin_sound {scale : ℤ} (hs : 0 < scale)
    {a : ScaledInterval} {b : RatInterval} {x : ℝ}
    (hx : ScaledInterval.Contains scale a x) (h : OutputWithin scale a b) :
    b.Contains x :=
  RatInterval.contains_widen (ScaledInterval.contains_rational hs hx) h.1 h.2

theorem matrix_product_recipe_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (left right out : ℕ → ℕ → ℕ) (recipes : ℕ → ℕ → DotRecipe)
    (hcheck : ∀ i : Fin n, ∀ j : Fin n, (recipes i j).Check nodes n)
    (hleft : ∀ i : Fin n, ∀ j : Fin n, ∀ k : Fin n,
      (recipes i j).left k = left i k)
    (hright : ∀ i : Fin n, ∀ j : Fin n, ∀ k : Fin n,
      (recipes i j).right k = right k j)
    (hout : ∀ i : Fin n, ∀ j : Fin n, (recipes i j).accumulator n = out i j) :
    matrixValues (value inputs nodes) n out =
      matrixValues (value inputs nodes) n left * matrixValues (value inputs nodes) n right := by
  ext i j
  change value inputs nodes (out i j) = _
  rw [← hout i j, DotRecipe.sound_fin inputs nodes n (recipes i j) (hcheck i j)]
  simp only [Matrix.mul_apply, matrixValues, hleft, hright]

#print axioms DotRecipe.checkBool_sound
#print axioms outputWithin_sound
#print axioms matrix_product_recipe_sound

end ThomsonN10.Local.Certificates.IntervalCircuit
