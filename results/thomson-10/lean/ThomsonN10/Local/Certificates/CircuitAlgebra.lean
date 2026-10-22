/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitAlgebra.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.IntervalCircuit

/-! Finite operation recipes preserve the real semantics of a shared circuit. -/

namespace ThomsonN10.Local.Certificates.IntervalCircuit

open scoped BigOperators

theorem value_input (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i j : ℕ)
    (h : (nodes i).op = .input j) : value inputs nodes i = inputs j := by
  rw [value_unfold, h]
  rfl

theorem value_constant (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i : ℕ)
    (num den : ℤ) (h : (nodes i).op = .constant num den) :
    value inputs nodes i = (num : ℝ)/den := by
  rw [value_unfold, h]
  rfl

theorem value_add (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i a b : ℕ)
    (h : (nodes i).op = .add a b) (ha : a < i) (hb : b < i) :
    value inputs nodes i = value inputs nodes a + value inputs nodes b := by
  rw [value_unfold, h]
  simp only [Op.eval, if_pos ha, if_pos hb]

theorem value_neg (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i a : ℕ)
    (h : (nodes i).op = .neg a) (ha : a < i) :
    value inputs nodes i = -value inputs nodes a := by
  rw [value_unfold, h]
  simp only [Op.eval, if_pos ha]

theorem value_sqrt (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i a : ℕ)
    (h : (nodes i).op = .sqrt a) (ha : a < i) :
    value inputs nodes i = Real.sqrt (value inputs nodes a) := by
  rw [value_unfold, h]
  simp only [Op.eval, if_pos ha]

theorem value_mul (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i a b : ℕ)
    (h : (nodes i).op = .mul a b) (ha : a < i) (hb : b < i) :
    value inputs nodes i = value inputs nodes a * value inputs nodes b := by
  rw [value_unfold, h]
  simp only [Op.eval, if_pos ha, if_pos hb]

def ZeroAt (nodes : ℕ → Node) (i : ℕ) : Prop := (nodes i).op = .constant 0 1
def OneAt (nodes : ℕ → Node) (i : ℕ) : Prop := (nodes i).op = .constant 1 1

def SmartAddCheck (nodes : ℕ → Node) (a b out : ℕ) : Prop :=
  (ZeroAt nodes a ∧ out = b) ∨ (ZeroAt nodes b ∧ out = a) ∨
    ((nodes out).op = .add a b ∧ a < out ∧ b < out)

def SmartMulCheck (nodes : ℕ → Node) (a b out : ℕ) : Prop :=
  (ZeroAt nodes a ∧ ZeroAt nodes out) ∨ (ZeroAt nodes b ∧ ZeroAt nodes out) ∨
    (OneAt nodes a ∧ out = b) ∨ (OneAt nodes b ∧ out = a) ∨
      ((nodes out).op = .mul a b ∧ a < out ∧ b < out)

instance (nodes : ℕ → Node) (a b out : ℕ) : Decidable (SmartAddCheck nodes a b out) := by
  unfold SmartAddCheck ZeroAt
  infer_instance

instance (nodes : ℕ → Node) (a b out : ℕ) : Decidable (SmartMulCheck nodes a b out) := by
  unfold SmartMulCheck ZeroAt OneAt
  infer_instance

theorem zeroAt_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i : ℕ)
    (h : ZeroAt nodes i) : value inputs nodes i = 0 := by
  simpa using value_constant inputs nodes i 0 1 h

theorem oneAt_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i : ℕ)
    (h : OneAt nodes i) : value inputs nodes i = 1 := by
  simpa using value_constant inputs nodes i 1 1 h

theorem smartAdd_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a b out : ℕ)
    (h : SmartAddCheck nodes a b out) :
    value inputs nodes out = value inputs nodes a + value inputs nodes b := by
  rcases h with ⟨hz,rfl⟩ | ⟨hz,rfl⟩ | ⟨hop,ha,hb⟩
  · rw [zeroAt_sound inputs nodes a hz, zero_add]
  · rw [zeroAt_sound inputs nodes b hz, add_zero]
  · exact value_add inputs nodes out a b hop ha hb

theorem smartMul_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a b out : ℕ)
    (h : SmartMulCheck nodes a b out) :
    value inputs nodes out = value inputs nodes a * value inputs nodes b := by
  rcases h with ⟨hz,ho⟩ | ⟨hz,ho⟩ | ⟨h1,rfl⟩ | ⟨h1,rfl⟩ | ⟨hop,ha,hb⟩
  · rw [zeroAt_sound inputs nodes out ho, zeroAt_sound inputs nodes a hz, zero_mul]
  · rw [zeroAt_sound inputs nodes out ho, zeroAt_sound inputs nodes b hz, mul_zero]
  · rw [oneAt_sound inputs nodes a h1, one_mul]
  · rw [oneAt_sound inputs nodes b h1, mul_one]
  · exact value_mul inputs nodes out a b hop ha hb

/-- A checked left-associated dot-product recipe; all indices refer to shared nodes. -/
structure DotRecipe where
  left : ℕ → ℕ
  right : ℕ → ℕ
  product : ℕ → ℕ
  accumulator : ℕ → ℕ

def DotRecipe.Check (nodes : ℕ → Node) (n : ℕ) (recipe : DotRecipe) : Prop :=
  ZeroAt nodes (recipe.accumulator 0) ∧
    ∀ k, k < n →
      SmartMulCheck nodes (recipe.left k) (recipe.right k) (recipe.product k) ∧
      SmartAddCheck nodes (recipe.accumulator k) (recipe.product k) (recipe.accumulator (k+1))

theorem DotRecipe.sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (recipe : DotRecipe) (h : recipe.Check nodes n) :
    value inputs nodes (recipe.accumulator n) =
      ∑ k ∈ Finset.range n, value inputs nodes (recipe.left k) *
        value inputs nodes (recipe.right k) := by
  have hprefix : ∀ k, k ≤ n → value inputs nodes (recipe.accumulator k) =
      ∑ j ∈ Finset.range k, value inputs nodes (recipe.left j) *
        value inputs nodes (recipe.right j) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using zeroAt_sound inputs nodes (recipe.accumulator 0) h.1
    | succ k ih =>
        intro hkn
        obtain ⟨hm,ha⟩ := h.2 k (by omega)
        rw [smartAdd_sound inputs nodes _ _ _ ha,
          smartMul_sound inputs nodes _ _ _ hm, ih (by omega), Finset.sum_range_succ]
  exact hprefix n le_rfl

#print axioms smartAdd_sound
#print axioms smartMul_sound
#print axioms DotRecipe.sound

end ThomsonN10.Local.Certificates.IntervalCircuit
