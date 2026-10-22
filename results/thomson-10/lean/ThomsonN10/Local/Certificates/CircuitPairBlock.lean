/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitPairBlock.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitConstants
import ThomsonN10.Local.HessianSymmetry

/-! Finite arithmetic recipes compute the actual Coulomb pair Hessian. -/

set_option autoImplicit false

namespace ThomsonN10.Local.Certificates.IntervalCircuit

theorem value_inv (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i a : ℕ)
    (h : (nodes i).op = .inv a) (ha : a < i) :
    value inputs nodes i = (value inputs nodes a)⁻¹ := by
  rw [value_unfold, h]
  simp only [Op.eval, if_pos ha]

def SmartNegCheck (nodes : ℕ → Node) (a out : ℕ) : Prop :=
  (ZeroAt nodes a ∧ ZeroAt nodes out) ∨
    ((nodes out).op = .neg a ∧ a < out)

instance (nodes : ℕ → Node) (a out : ℕ) : Decidable (SmartNegCheck nodes a out) := by
  unfold SmartNegCheck ZeroAt
  infer_instance

theorem smartNeg_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a out : ℕ)
    (h : SmartNegCheck nodes a out) :
    value inputs nodes out = -value inputs nodes a := by
  rcases h with ⟨ha, ho⟩ | ⟨hop, ha⟩
  · rw [zeroAt_sound inputs nodes a ha, zeroAt_sound inputs nodes out ho, neg_zero]
  · exact value_neg inputs nodes out a hop ha

structure PowerRecipe where
  base : ℕ
  accumulator : ℕ → ℕ

def PowerRecipe.Check (nodes : ℕ → Node) (n : ℕ) (recipe : PowerRecipe) : Prop :=
  OneAt nodes (recipe.accumulator 0) ∧
    ∀ k : Fin n, SmartMulCheck nodes (recipe.accumulator k) recipe.base
      (recipe.accumulator (k.val+1))

instance (nodes : ℕ → Node) (n : ℕ) (recipe : PowerRecipe) :
    Decidable (recipe.Check nodes n) := by
  unfold PowerRecipe.Check OneAt
  infer_instance

theorem PowerRecipe.sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (recipe : PowerRecipe) (h : recipe.Check nodes n) (k : ℕ) (hk : k ≤ n) :
    value inputs nodes (recipe.accumulator k) = (value inputs nodes recipe.base)^k := by
  induction k with
  | zero => simpa using oneAt_sound inputs nodes (recipe.accumulator 0) h.1
  | succ k ih =>
      rw [smartMul_sound inputs nodes _ _ _ (h.2 ⟨k, by omega⟩),
        ih (by omega), pow_succ]

structure DistanceRecipe where
  difference : Fin 3 → ℕ
  squares : DotRecipe
  root : ℕ
  inverse : ℕ

def DistanceRecipe.Check (nodes : ℕ → Node) (recipe : DistanceRecipe) : Prop :=
  recipe.squares.ExtendedCheck nodes 3 ∧
    (∀ a : Fin 3, recipe.squares.left a = recipe.difference a ∧
      recipe.squares.right a = recipe.difference a) ∧
    (nodes recipe.root).op = .sqrt (recipe.squares.accumulator 3) ∧
    recipe.squares.accumulator 3 < recipe.root ∧
    (nodes recipe.inverse).op = .inv recipe.root ∧ recipe.root < recipe.inverse

instance (nodes : ℕ → Node) (recipe : DistanceRecipe) :
    Decidable (recipe.Check nodes) := by
  unfold DistanceRecipe.Check
  infer_instance

theorem DistanceRecipe.square_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node)
    (recipe : DistanceRecipe) (h : recipe.Check nodes) :
    value inputs nodes (recipe.squares.accumulator 3) =
      ∑ a : Fin 3, (value inputs nodes (recipe.difference a))^2 := by
  rw [recipe.squares.extended_sound inputs nodes 3 h.1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Fin.sum_univ_three]
  have h0 : recipe.squares.left 0 = recipe.difference 0 ∧
      recipe.squares.right 0 = recipe.difference 0 := h.2.1 0
  have h1 : recipe.squares.left 1 = recipe.difference 1 ∧
      recipe.squares.right 1 = recipe.difference 1 := h.2.1 1
  have h2 : recipe.squares.left 2 = recipe.difference 2 ∧
      recipe.squares.right 2 = recipe.difference 2 := h.2.1 2
  rw [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
  ring

theorem DistanceRecipe.root_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node)
    (recipe : DistanceRecipe) (h : recipe.Check nodes) (p q : R3)
    (hdiff : ∀ a : Fin 3, value inputs nodes (recipe.difference a) = p a-q a) :
    value inputs nodes recipe.root = ‖p-q‖ := by
  rw [value_sqrt inputs nodes _ _ h.2.2.1 h.2.2.2.1,
    recipe.square_sound inputs nodes h]
  have hs : (∑ a : Fin 3, (value inputs nodes (recipe.difference a))^2) =
      ∑ a : Fin 3, ((p-q) a)^2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hdiff a]
    rfl
  rw [hs, sqrt_coordinate_squares_eq_norm]

theorem DistanceRecipe.inverse_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node)
    (recipe : DistanceRecipe) (h : recipe.Check nodes) (p q : R3)
    (hdiff : ∀ a : Fin 3, value inputs nodes (recipe.difference a) = p a-q a) :
    value inputs nodes recipe.inverse = ‖p-q‖⁻¹ := by
  rw [value_inv inputs nodes _ _ h.2.2.2.2.1 h.2.2.2.2.2,
    recipe.root_sound inputs nodes h p q hdiff]

structure PairBlockRecipe where
  distance : DistanceRecipe
  powers : PowerRecipe
  three : ℕ
  scaledFifth : ℕ
  timesFirst : Fin 3 → ℕ
  numerator : Fin 3 → Fin 3 → ℕ
  delta : Fin 3 → Fin 3 → ℕ
  diagonalTerm : Fin 3 → Fin 3 → ℕ
  negativeDiagonal : Fin 3 → Fin 3 → ℕ
  block : Fin 3 → Fin 3 → ℕ

structure PairBlockRecipe.Check (nodes : ℕ → Node) (recipe : PairBlockRecipe) : Prop where
  distance : recipe.distance.Check nodes
  powers : recipe.powers.Check nodes 5
  base : recipe.powers.base = recipe.distance.inverse
  three : (nodes recipe.three).op = .constant 3 1
  scaled : SmartMulCheck nodes (recipe.powers.accumulator 5) recipe.three recipe.scaledFifth
  first : ∀ a : Fin 3, SmartMulCheck nodes recipe.scaledFifth
    (recipe.distance.difference a) (recipe.timesFirst a)
  numerator : ∀ a b : Fin 3, SmartMulCheck nodes (recipe.timesFirst a)
    (recipe.distance.difference b) (recipe.numerator a b)
  delta : ∀ a b : Fin 3, if a=b then OneAt nodes (recipe.delta a b)
    else ZeroAt nodes (recipe.delta a b)
  diagonal : ∀ a b : Fin 3, SmartMulCheck nodes (recipe.powers.accumulator 3)
    (recipe.delta a b) (recipe.diagonalTerm a b)
  negative : ∀ a b : Fin 3,
    SmartNegCheck nodes (recipe.diagonalTerm a b) (recipe.negativeDiagonal a b)
  block : ∀ a b : Fin 3, SmartAddCheck nodes (recipe.numerator a b)
    (recipe.negativeDiagonal a b) (recipe.block a b)

theorem PairBlockRecipe.sound (inputs : ℕ → ℝ) (nodes : ℕ → Node)
    (recipe : PairBlockRecipe) (h : recipe.Check nodes) (p q : R3)
    (hdiff : ∀ a : Fin 3, value inputs nodes (recipe.distance.difference a) = p a-q a)
    (a b : Fin 3) :
    value inputs nodes (recipe.block a b) = coulombPairBlock (p-q) a b := by
  have hinv := recipe.distance.inverse_sound inputs nodes h.distance p q hdiff
  have hp3 := recipe.powers.sound inputs nodes 5 h.powers 3 (by decide)
  have hp5 := recipe.powers.sound inputs nodes 5 h.powers 5 le_rfl
  rw [h.base, hinv] at hp3 hp5
  have hthree : value inputs nodes recipe.three = 3 := by
    simpa using value_constant inputs nodes recipe.three 3 1 h.three
  have hdelta : value inputs nodes (recipe.delta a b) = (if a=b then 1 else 0 : ℝ) := by
    by_cases hab : a=b
    · rw [if_pos hab]
      exact oneAt_sound inputs nodes _ (by simpa only [if_pos hab] using h.delta a b)
    · rw [if_neg hab]
      exact zeroAt_sound inputs nodes _ (by simpa only [if_neg hab] using h.delta a b)
  rw [smartAdd_sound inputs nodes _ _ _ (h.block a b),
    smartNeg_sound inputs nodes _ _ (h.negative a b),
    smartMul_sound inputs nodes _ _ _ (h.diagonal a b),
    smartMul_sound inputs nodes _ _ _ (h.numerator a b),
    smartMul_sound inputs nodes _ _ _ (h.first a),
    smartMul_sound inputs nodes _ _ _ h.scaled,
    hthree, hp3, hp5, hdelta, hdiff a, hdiff b]
  simp only [coulombPairBlock, PiLp.sub_apply, div_eq_mul_inv, inv_pow]
  ring

#print axioms DistanceRecipe.root_sound
#print axioms PairBlockRecipe.sound

end ThomsonN10.Local.Certificates.IntervalCircuit
