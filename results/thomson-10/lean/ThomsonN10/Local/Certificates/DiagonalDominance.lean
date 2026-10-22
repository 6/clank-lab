/- Adapted from proof/lean/ThomsonN9/Certificates/DiagonalDominance.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.Interval
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! Soundness of interval diagonal dominance and invertible congruences. -/

namespace ThomsonN10.Local.Certificates

open Matrix
open scoped BigOperators

namespace RatInterval

def absBound (a : RatInterval) : ℚ := max |a.lo| |a.hi|

theorem abs_le_absBound {a : RatInterval} {x : ℝ} (hx : a.Contains x) :
    |x| ≤ (a.absBound : ℝ) := by
  rw [abs_le]
  have hlo : |(a.lo : ℝ)| ≤ (a.absBound : ℝ) := by
    exact_mod_cast le_max_left |a.lo| |a.hi|
  have hhi : |(a.hi : ℝ)| ≤ (a.absBound : ℝ) := by
    exact_mod_cast le_max_right |a.lo| |a.hi|
  constructor
  · have h := neg_abs_le (a.lo : ℝ)
    linarith [hx.1]
  · exact hx.2.trans ((le_abs_self _).trans hhi)

def sum {ι : Type*} [Fintype ι] (a : ι → RatInterval) : RatInterval :=
  ⟨∑ i, (a i).lo, ∑ i, (a i).hi⟩

theorem contains_sum {ι : Type*} [Fintype ι] (a : ι → RatInterval) (x : ι → ℝ)
    (hx : ∀ i, (a i).Contains (x i)) : (sum a).Contains (∑ i, x i) := by
  constructor
  · simpa only [sum, Rat.cast_sum] using Finset.sum_le_sum (fun i _ => (hx i).1)
  · simpa only [sum, Rat.cast_sum] using Finset.sum_le_sum (fun i _ => (hx i).2)

end RatInterval

def intervalMatrixMul {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ RatInterval) (B : Matrix κ ν RatInterval) : Matrix ι ν RatInterval :=
  fun i j => RatInterval.sum fun k => RatInterval.mul (A i k) (B k j)

theorem contains_matrix_mul {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ RatInterval) (B : Matrix κ ν RatInterval)
    (a : Matrix ι κ ℝ) (b : Matrix κ ν ℝ)
    (ha : ∀ i j, (A i j).Contains (a i j)) (hb : ∀ i j, (B i j).Contains (b i j)) :
    ∀ i j, (intervalMatrixMul A B i j).Contains ((a*b) i j) := by
  intro i j
  exact RatInterval.contains_sum _ _ (fun k => RatInterval.contains_mul (ha i k) (hb k j))

def StrictDD {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bounds : Matrix ι ι RatInterval) : Prop :=
  ∀ i, (∑ j ∈ Finset.univ.erase i, (bounds i j).absBound) < (bounds i i).lo

instance {ι : Type*} [Fintype ι] [DecidableEq ι] (bounds : Matrix ι ι RatInterval) :
    Decidable (StrictDD bounds) := by
  unfold StrictDD
  infer_instance

theorem posDef_of_strictDD {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hdd : ∀ i, (∑ j ∈ Finset.univ.erase i, |A i j|) < A i i) : A.PosDef := by
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro k
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues k) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin']
    exact hA.eigenvalues_mem_spectrum_real k
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  simp only [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] at hi
  have h := (abs_le.mp hi).1
  linarith [hdd i]

theorem posDef_of_interval_strictDD {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (bounds : Matrix ι ι RatInterval) (hA : A.IsHermitian)
    (henclose : ∀ i j, (bounds i j).Contains (A i j))
    (hcheck : StrictDD bounds) : A.PosDef := by
  apply posDef_of_strictDD A hA
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i, |A i j|) ≤
      ((∑ j ∈ Finset.univ.erase i, (bounds i j).absBound : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum fun j _ => RatInterval.abs_le_absBound (henclose i j)
  exact lt_of_le_of_lt hsum (lt_of_lt_of_le (by exact_mod_cast hcheck i) (henclose i i).1)

theorem isUnit_of_unit_upper {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hupper : ∀ i j, j < i → C i j = 0) (hdiag : ∀ i, C i i = 1) : IsUnit C := by
  apply (Matrix.isUnit_iff_isUnit_det C).mpr
  have htri : C.IsUpperTriangular := fun {i j} hij => hupper i j hij
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [hdiag, Finset.prod_const_one, isUnit_one]

/-- Exact rational interval checks on a congruent matrix prove positivity of the original. -/
theorem posDef_of_unit_upper_interval_congruence {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ) (bounds : Matrix (Fin n) (Fin n) RatInterval)
    (hA : A.IsHermitian) (hupper : ∀ i j, j < i → C i j = 0)
    (hdiag : ∀ i, C i i = 1)
    (henclose : ∀ i j, (bounds i j).Contains ((star C*A*C) i j))
    (hcheck : StrictDD bounds) : A.PosDef := by
  apply (Matrix.IsUnit.posDef_star_left_conjugate_iff
    (isUnit_of_unit_upper C hupper hdiag)).mp
  apply posDef_of_interval_strictDD (star C*A*C) bounds _ henclose hcheck
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.isHermitian_conjTranspose_mul_mul C hA

/-- Coarse enclosures verified by the separate 18-dimensional local certificate replay. -/
def localCongruenceBounds : Matrix (Fin 18) (Fin 18) RatInterval :=
  fun i j => if i = j then ⟨1/100, 100⟩ else ⟨-1/100000, 1/100000⟩

theorem localCongruenceBounds_strictDD : StrictDD localCongruenceBounds := by
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i, (localCongruenceBounds i j).absBound) =
      (17 : ℚ) * (1/100000) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, (1/100000 : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        norm_num [localCongruenceBounds, hij, RatInterval.absBound]
      _ = _ := by simp
  rw [hsum]
  norm_num [localCongruenceBounds]

/-- This still requires the actual Hessian/congruence entry enclosures as hypotheses. -/
theorem local_posDef_of_congruence_enclosures
    (A C : Matrix (Fin 18) (Fin 18) ℝ)
    (hA : A.IsHermitian) (hupper : ∀ i j, j < i → C i j = 0)
    (hdiag : ∀ i, C i i = 1)
    (henclose : ∀ i j, (localCongruenceBounds i j).Contains ((star C*A*C) i j)) : A.PosDef :=
  posDef_of_unit_upper_interval_congruence A C localCongruenceBounds hA hupper hdiag
    henclose localCongruenceBounds_strictDD

def ambientCongruenceBounds : Matrix (Fin 27) (Fin 27) RatInterval :=
  fun i j => if i = j then ⟨1/20, 2000000⟩ else ⟨-1/100000, 1/100000⟩

theorem ambientCongruenceBounds_strictDD : StrictDD ambientCongruenceBounds := by
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i, (ambientCongruenceBounds i j).absBound) =
      (26 : ℚ) * (1/100000) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, (1/100000 : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        norm_num [ambientCongruenceBounds, hij, RatInterval.absBound]
      _ = _ := by simp
  rw [hsum]
  norm_num [ambientCongruenceBounds]

theorem ambient_posDef_of_congruence_enclosures
    (A C : Matrix (Fin 27) (Fin 27) ℝ)
    (hA : A.IsHermitian) (hupper : ∀ i j, j < i → C i j = 0)
    (hdiag : ∀ i, C i i = 1)
    (henclose : ∀ i j, (ambientCongruenceBounds i j).Contains ((star C*A*C) i j)) :
    A.PosDef :=
  posDef_of_unit_upper_interval_congruence A C ambientCongruenceBounds hA hupper hdiag
    henclose ambientCongruenceBounds_strictDD

/-- A positive augmented matrix bounds the original quadratic form on the augmentation kernel. -/
theorem quadratic_lower_on_augmentation_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H P : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ)
    (hpositive : (H+P-c • (1 : Matrix ι ι ℝ)).PosSemidef) (hkernel : P *ᵥ v = 0) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H *ᵥ v) := by
  have h := hpositive.dotProduct_mulVec_nonneg v
  simpa only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hkernel, add_zero, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    sub_nonneg] using h

theorem gram_augmentations_annihilate {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (R : Matrix ι κ ℝ) (N : Matrix ι ν ℝ) (penalty : ℝ) (v : ι → ℝ)
    (hR : R.transpose *ᵥ v = 0) (hN : N.transpose *ᵥ v = 0) :
    (R*R.transpose+penalty • (N*N.transpose)) *ᵥ v = 0 := by
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    hR, hN, Matrix.mulVec_zero, smul_zero, add_zero]

theorem quadratic_lower_with_orthogonal_augmentations {ι κ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ν]
    (H : Matrix ι ι ℝ) (R : Matrix ι κ ℝ) (N : Matrix ι ν ℝ)
    (penalty c : ℝ) (v : ι → ℝ)
    (hpositive : (H+(R*R.transpose+penalty • (N*N.transpose))-
      c • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hR : R.transpose *ᵥ v = 0) (hN : N.transpose *ᵥ v = 0) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H *ᵥ v) :=
  quadratic_lower_on_augmentation_kernel H _ c v hpositive
    (gram_augmentations_annihilate R N penalty v hR hN)

/-- One normal column for each point, on product-indexed ambient coordinates. -/
def normalColumns {ι κ : Type*} [DecidableEq ι] (p : ι → κ → ℝ) :
    Matrix (ι × κ) ι ℝ := fun ia j => if ia.1 = j then p ia.1 ia.2 else 0

theorem normalColumns_transpose_mulVec {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → κ → ℝ) (v : ι × κ → ℝ) (i : ι) :
    ((normalColumns p).transpose *ᵥ v) i = ∑ a, p i a * v (i,a) := by
  simp [normalColumns, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem normalColumns_annihilate_tangent {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p : ι → κ → ℝ) (v : ι × κ → ℝ)
    (htangent : ∀ i, ∑ a, p i a * v (i,a) = 0) :
    (normalColumns p).transpose *ᵥ v = 0 := by
  ext i
  rw [normalColumns_transpose_mulVec]
  exact htangent i

theorem normalColumns_gram {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → κ → ℝ) (i j : ι) (a b : κ) :
    (normalColumns p * (normalColumns p).transpose) (i,a) (j,b) =
      if i = j then p i a * p i b else 0 := by
  by_cases hij : i = j
  · subst j
    simp [normalColumns, Matrix.mul_apply, ite_mul]
  · simp [normalColumns, Matrix.mul_apply, ite_mul, hij]

#print axioms RatInterval.abs_le_absBound
#print axioms contains_matrix_mul
#print axioms posDef_of_interval_strictDD
#print axioms posDef_of_unit_upper_interval_congruence
#print axioms localCongruenceBounds_strictDD
#print axioms local_posDef_of_congruence_enclosures
#print axioms ambientCongruenceBounds_strictDD
#print axioms ambient_posDef_of_congruence_enclosures
#print axioms quadratic_lower_on_augmentation_kernel
#print axioms quadratic_lower_with_orthogonal_augmentations
#print axioms normalColumns_annihilate_tangent
#print axioms normalColumns_gram

end ThomsonN10.Local.Certificates
