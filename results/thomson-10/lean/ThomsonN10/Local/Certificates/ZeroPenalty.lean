/- Adapted from proof/lean/ThomsonN9/Certificates/ZeroPenalty.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.DiagonalDominance

/-! The unpenalized ambient certificate interface; actual entry enclosures are explicit premises. -/

namespace ThomsonN10.Local.Certificates

open Matrix
open scoped BigOperators

def zeroPenaltyCongruenceBounds : Matrix (Fin 30) (Fin 30) RatInterval :=
  fun i j => if i = j then ⟨1/1000, 100⟩ else ⟨-1/100000, 1/100000⟩

theorem zeroPenaltyCongruenceBounds_strictDD : StrictDD zeroPenaltyCongruenceBounds := by
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i, (zeroPenaltyCongruenceBounds i j).absBound) =
      (29 : ℚ)*(1/100000) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, (1/100000 : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        norm_num [zeroPenaltyCongruenceBounds, hij, RatInterval.absBound]
      _ = _ := by simp
  rw [hsum]
  norm_num [zeroPenaltyCongruenceBounds]

theorem zeroPenalty_posDef_of_congruence_enclosures
    (A C : Matrix (Fin 30) (Fin 30) ℝ)
    (hA : A.IsHermitian) (hupper : ∀ i j, j < i → C i j = 0)
    (hdiag : ∀ i, C i i = 1)
    (henclose : ∀ i j, (zeroPenaltyCongruenceBounds i j).Contains ((star C*A*C) i j)) :
    A.PosDef :=
  posDef_of_unit_upper_interval_congruence A C zeroPenaltyCongruenceBounds hA hupper hdiag
    henclose zeroPenaltyCongruenceBounds_strictDD

theorem quadratic_lower_on_rotations_perp {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : Matrix ι ι ℝ) (R : Matrix ι κ ℝ) (c : ℝ) (v : ι → ℝ)
    (hpositive : (H+R*R.transpose-c • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hR : R.transpose *ᵥ v = 0) : c*(v ⬝ᵥ v) ≤ v ⬝ᵥ (H *ᵥ v) := by
  apply quadratic_lower_on_augmentation_kernel H (R*R.transpose) c v hpositive
  rw [← Matrix.mulVec_mulVec, hR, Matrix.mulVec_zero]

#print axioms zeroPenaltyCongruenceBounds_strictDD
#print axioms zeroPenalty_posDef_of_congruence_enclosures
#print axioms quadratic_lower_on_rotations_perp

end ThomsonN10.Local.Certificates
