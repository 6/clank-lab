/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitSums.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitConstants
import ThomsonN10.Local.HessianSymmetry

/-! Checked scalar accumulation and block-matrix assembly. -/

set_option autoImplicit false

namespace ThomsonN10.Local.Certificates.IntervalCircuit

structure SumRecipe where
  term : ℕ → ℕ
  accumulator : ℕ → ℕ

def SumRecipe.Check (nodes : ℕ → Node) (n : ℕ) (recipe : SumRecipe) : Prop :=
  ZeroAt nodes (recipe.accumulator 0) ∧
    ∀ k : Fin n, ExtendedSmartAddCheck nodes (recipe.accumulator k)
      (recipe.term k) (recipe.accumulator (k.val+1))

instance instDecidableSumRecipeCheck (nodes : ℕ → Node) (n : ℕ) (recipe : SumRecipe) :
    Decidable (recipe.Check nodes n) := by
  unfold SumRecipe.Check ZeroAt
  infer_instance

theorem SumRecipe.sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (recipe : SumRecipe) (h : recipe.Check nodes n) :
    value inputs nodes (recipe.accumulator n) =
      ∑ k ∈ Finset.range n, value inputs nodes (recipe.term k) := by
  have hprefix : ∀ k, k ≤ n → value inputs nodes (recipe.accumulator k) =
      ∑ j ∈ Finset.range k, value inputs nodes (recipe.term j) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using zeroAt_sound inputs nodes (recipe.accumulator 0) h.1
    | succ k ih =>
        intro hk
        rw [extendedSmartAdd_sound inputs nodes _ _ _ (h.2 ⟨k, by omega⟩),
          ih (by omega), Finset.sum_range_succ]
  exact hprefix n le_rfl

theorem SumRecipe.sound_fin (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (recipe : SumRecipe) (h : recipe.Check nodes n) :
    value inputs nodes (recipe.accumulator n) =
      ∑ k : Fin n, value inputs nodes (recipe.term k) := by
  exact (recipe.sound inputs nodes n h).trans
    (Finset.sum_range (fun k => value inputs nodes (recipe.term k)))

theorem blockLaplacian_of_entries
    (B : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) ℝ)
    (H : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)
    (hzero : ∀ i a b, B i i a b = 0)
    (hdiag : ∀ i a b, H (i,a) (i,b) = ∑ j, B i j a b)
    (hoff : ∀ i j a b, i ≠ j → H (i,a) (j,b) = -B i j a b) :
    H = blockLaplacian B := by
  apply Matrix.ext
  rintro ⟨i,a⟩ ⟨j,b⟩
  by_cases hij : i=j
  · subst j
    simp [blockLaplacian, hzero, hdiag]
  · simp only [blockLaplacian, if_neg hij, zero_sub, hoff i j a b hij]

theorem self_coulombPairBlock_zero (p : Configuration) (i : Fin 10) (a b : Fin 3) :
    coulombPairBlock (p i-p i) a b = 0 := by
  simp [coulombPairBlock]

theorem pair_hessian_of_entries (p : Configuration)
    (H : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)
    (hdiag : ∀ i a b, H (i,a) (i,b) = ∑ j, coulombPairBlock (p i-p j) a b)
    (hoff : ∀ i j a b, i ≠ j → H (i,a) (j,b) = -coulombPairBlock (p i-p j) a b) :
    H = blockLaplacian (fun i j => coulombPairBlock (p i-p j)) :=
  blockLaplacian_of_entries _ H (self_coulombPairBlock_zero p) hdiag hoff

#print axioms SumRecipe.sound
#print axioms pair_hessian_of_entries

end ThomsonN10.Local.Certificates.IntervalCircuit
