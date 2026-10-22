/- Adapted from proof/lean/ThomsonN9/BlockHessian.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.LocalEstimate
import Mathlib.Data.Matrix.Mul

/-! Checked ambient matrix semantics for the constrained second variation. -/

namespace ThomsonN10.Local

open Matrix

def blockLaplacian (B : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ :=
  fun ia jb => (if ia.1 = jb.1 then ∑ k, B ia.1 k ia.2 jb.2 else 0)-B ia.1 jb.1 ia.2 jb.2

def flattenCoordinates (v : Fin 10 → Fin 3 → ℝ) : Fin 10 × Fin 3 → ℝ :=
  fun ia => v ia.1 ia.2

theorem pair_block_quadratic_identity
    (B : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, B i j = B j i) (v : Fin 10 → Fin 3 → ℝ) :
    pairSum (fun i j => (v i-v j) ⬝ᵥ ((B i j) *ᵥ (v i-v j))) =
      ∑ i, v i ⬝ᵥ (∑ j, (B i j) *ᵥ (v i-v j)) := by
  let A : Fin 10 → Fin 10 → ℝ := fun i j => v i ⬝ᵥ ((B i j) *ᵥ (v i-v j))
  have hij (i j : Fin 10) :
      (v i-v j) ⬝ᵥ ((B i j) *ᵥ (v i-v j)) = A i j+A j i := by
    dsimp [A]
    rw [hB j i]
    have heq : v j-v i = -(v i-v j) := by abel
    rw [heq, Matrix.mulVec_neg, dotProduct_neg, sub_dotProduct]
    ring
  have hsym (i j : Fin 10) :
      (v i-v j) ⬝ᵥ ((B i j) *ᵥ (v i-v j)) =
        (v j-v i) ⬝ᵥ ((B j i) *ᵥ (v j-v i)) := by
    rw [hij i j, hij j i, add_comm]
  have ht := twice_pairSum (fun i j => (v i-v j) ⬝ᵥ ((B i j) *ᵥ (v i-v j)))
    hsym (fun i => by simp)
  simp_rw [hij] at ht ⊢
  have hswap : (∑ i, ∑ j, A j i) = ∑ i, ∑ j, A i j := Finset.sum_comm
  simp only [Finset.sum_add_distrib, hswap] at ht
  have hforce : (∑ i, v i ⬝ᵥ (∑ j, (B i j) *ᵥ (v i-v j))) = ∑ i, ∑ j, A i j := by
    simp only [dotProduct_sum, A]
  rw [hforce]
  linarith

theorem blockLaplacian_mulVec
    (B : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 10 → Fin 3 → ℝ) (i : Fin 10) (a : Fin 3) :
    (blockLaplacian B *ᵥ flattenCoordinates v) (i,a) =
      (∑ j, B i j *ᵥ (v i-v j)) a := by
  change Fin 10 → Fin 10 → Fin 3 → Fin 3 → ℝ at B
  change (∑ ia : Fin 10 × Fin 3,
    ((if i = ia.1 then ∑ k, B i k a ia.2 else 0)-B i ia.1 a ia.2)*v ia.1 ia.2) =
      ∑ j, ∑ b, B i j a b*(v i b-v j b)
  simp only [Fintype.sum_prod_type, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

theorem blockLaplacian_quadratic
    (B : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j, B i j = B j i) (v : Fin 10 → Fin 3 → ℝ) :
    flattenCoordinates v ⬝ᵥ (blockLaplacian B *ᵥ flattenCoordinates v) =
      pairSum (fun i j => (v i-v j) ⬝ᵥ ((B i j) *ᵥ (v i-v j))) := by
  rw [pair_block_quadratic_identity B hB v]
  simp only [dotProduct, Fintype.sum_prod_type, flattenCoordinates,
    blockLaplacian_mulVec]

noncomputable def coulombPairBlock (d : R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun a b => 3*d a*d b/‖d‖^5-(if a = b then 1 else 0)/‖d‖^3

theorem real_inner_eq_dotProduct (d w : R3) :
    inner ℝ d w = (fun a => d a) ⬝ᵥ (fun a => w a) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem coulombPairBlock_neg (d : R3) : coulombPairBlock (-d) = coulombPairBlock d := by
  ext a b
  simp only [coulombPairBlock, norm_neg, PiLp.neg_apply]
  ring

theorem coulombPairBlock_quadratic (d w : R3) :
    (fun a => w a) ⬝ᵥ (coulombPairBlock d *ᵥ (fun a => w a)) =
      (3*(inner ℝ d w)^2-‖d‖^2*‖w‖^2)/‖d‖^5 := by
  have hnorm : ‖w‖^2 = ∑ a : Fin 3, (w a)^2 := by
    simp [EuclideanSpace.norm_sq_eq]
  rw [real_inner_eq_dotProduct, hnorm]
  simp only [dotProduct, Matrix.mulVec, coulombPairBlock, Fin.sum_univ_three]
  norm_num
  by_cases hd : ‖d‖ = 0
  · simp [hd]
  · field_simp
    <;> ring

noncomputable def constrainedHessian (p : Configuration) :
    Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ :=
  blockLaplacian (fun i j => coulombPairBlock (p i-p j))-
    Matrix.diagonal (fun ia => radialCoefficient p ia.1)

def rotationColumns (p : Configuration) : Matrix (Fin 10 × Fin 3) (Fin 3) ℝ :=
  fun ia k => !![0, p ia.1 2, -p ia.1 1;
    -p ia.1 2, 0, p ia.1 0;
    p ia.1 1, -p ia.1 0, 0] ia.2 k

theorem rotationColumns_annihilate_skew (p : Configuration) (v : Fin 10 → Fin 3 → ℝ)
    (h : ∀ a b : Fin 3, (∑ i, (v i a*p i b-v i b*p i a)) = 0) :
    (rotationColumns p).transpose *ᵥ flattenCoordinates v = 0 := by
  ext k
  fin_cases k
  · simpa [rotationColumns, Matrix.mulVec, dotProduct, flattenCoordinates,
      Fintype.sum_prod_type, Fin.sum_univ_three, sub_eq_add_neg, mul_comm, add_comm] using h 2 1
  · simpa [rotationColumns, Matrix.mulVec, dotProduct, flattenCoordinates,
      Fintype.sum_prod_type, Fin.sum_univ_three, sub_eq_add_neg, mul_comm] using h 0 2
  · simpa [rotationColumns, Matrix.mulVec, dotProduct, flattenCoordinates,
      Fintype.sum_prod_type, Fin.sum_univ_three, sub_eq_add_neg, mul_comm, add_comm] using h 1 0

theorem constrainedHessian_quadratic (p b : Configuration) :
    flattenCoordinates (fun i a => b i a) ⬝ᵥ
        (constrainedHessian p *ᵥ flattenCoordinates (fun i a => b i a)) =
      constrainedSecondVariation p b := by
  have hB (i j : Fin 10) : coulombPairBlock (p i-p j) = coulombPairBlock (p j-p i) := by
    have heq : p i-p j = -(p j-p i) := by abel
    rw [heq, coulombPairBlock_neg]
  rw [constrainedHessian, Matrix.sub_mulVec, dotProduct_sub,
    blockLaplacian_quadratic _ hB]
  have hp (i j : Fin 10) :
      ((fun a => b i a)-(fun a => b j a)) ⬝ᵥ
        (coulombPairBlock (p i-p j) *ᵥ ((fun a => b i a)-(fun a => b j a))) =
          pairSecondVariation p b i j := by
    exact coulombPairBlock_quadratic (p i-p j) (b i-b j)
  simp_rw [hp]
  unfold constrainedSecondVariation
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal, flattenCoordinates, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Real.norm_eq_abs, sq_abs]
  ring

end ThomsonN10.Local
