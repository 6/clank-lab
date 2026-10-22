/- Adapted from proof/lean/ThomsonN9/HessianSymmetry.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.BlockHessian
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

namespace ThomsonN10.Local

/-! Symmetry and coordinate identities for the checked Hessian expression. -/

open Matrix

theorem sqrt_coordinate_squares_eq_norm (d : R3) :
    Real.sqrt (∑ a : Fin 3, (d a)^2) = ‖d‖ := by
  have h : ‖d‖^2 = ∑ a : Fin 3, (d a)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro a _
    rw [Real.norm_eq_abs, sq_abs]
  rw [← h, Real.sqrt_sq (norm_nonneg d)]

theorem coulombPairBlock_isHermitian (d : R3) : (coulombPairBlock d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [star_trivial, coulombPairBlock]
  by_cases h : a = b
  · subst b
    rfl
  · simp only [if_neg h, if_neg (Ne.symm h)]
    ring

theorem blockLaplacian_isHermitian
    (B : Fin 10 → Fin 10 → Matrix (Fin 3) (Fin 3) ℝ)
    (hswap : ∀ i j, B i j = B j i)
    (hblock : ∀ i j, (B i j).IsHermitian) : (blockLaplacian B).IsHermitian := by
  have hentry (i j : Fin 10) (a b : Fin 3) : B i j b a = B i j a b := by
    simpa only [star_trivial] using (hblock i j).apply a b
  apply Matrix.IsHermitian.ext
  rintro ⟨i, a⟩ ⟨j, b⟩
  simp only [star_trivial, blockLaplacian]
  by_cases h : i = j
  · subst j
    simp only [ite_true, hentry]
  · simp only [if_neg h, if_neg (Ne.symm h), zero_sub]
    rw [hswap j i, hentry]

theorem constrainedHessian_isHermitian (p : Configuration) :
    (constrainedHessian p).IsHermitian := by
  have hswap (i j : Fin 10) : coulombPairBlock (p i-p j) = coulombPairBlock (p j-p i) := by
    have h : p i-p j = -(p j-p i) := by abel
    rw [h, coulombPairBlock_neg]
  exact (blockLaplacian_isHermitian _ hswap (fun _ _ => coulombPairBlock_isHermitian _)).sub
    (Matrix.isHermitian_diagonal _)

theorem augmentedHessian_isHermitian (p : Configuration) (c : ℝ) :
    (constrainedHessian p+rotationColumns p*(rotationColumns p).transpose-
      c • (1 : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)).IsHermitian := by
  have hR : (rotationColumns p*(rotationColumns p).transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_conjTranspose_self (rotationColumns p)
  exact ((constrainedHessian_isHermitian p).add hR).sub
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all c))

end ThomsonN10.Local
