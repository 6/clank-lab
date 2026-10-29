import SecondPerturbation
import CofactorTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section

def starUnit {n : ℕ} (c : Option (Fin n)) (i : Fin n) : ℤˣ :=
  if c = some i then -1 else 1

theorem starUnit_value {n : ℕ} (c : Option (Fin n)) (i : Fin n) :
    (starUnit c i : ℤ) = starSign c i := by
  unfold starUnit starSign
  split_ifs <;> simp

theorem integralMatrix_signed_value {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℚ)
    (c : Option (Fin n)) (i : Fin n) (v : Fin r → ℤ) :
    (((starUnit c i : ℤ) * ∑ j, integralMatrix A i j * v j : ℤ) : ℚ) =
      (matrixDenominator A : ℚ) * (starSign c i * (A i ⬝ᵥ (fun j => (v j : ℚ)))) := by
  have hs : (((starUnit c i : ℤ) : ℚ)) = starSign c i := by
    rw [starUnit_value]
    unfold starSign
    split_ifs <;> norm_num
  push_cast
  simp only [hs, integralMatrix_value, dotProduct, Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem integralMatrix_subminor_nonzero {n m r : ℕ}
    (A : Matrix (Fin n) (Fin m) ℚ) (f : Fin r → Fin n) (g : Fin r → Fin m)
    (hf : (A.submatrix f g).det ≠ 0) :
    ((integralMatrix A).submatrix f g).det ≠ 0 := by
  have hS : (matrixDenominator A : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_positive (fun p : Fin n × Fin m => A p.1 p.2)).ne'
  have he : (((integralMatrix A).submatrix f g).map (Int.castRingHom ℚ)) =
      (matrixDenominator A : ℚ) • A.submatrix f g := by
    ext i j
    exact integralMatrix_value A (f i) (g j)
  have hd : ((((integralMatrix A).submatrix f g).det : ℤ) : ℚ) ≠ 0 := by
    rw [Int.cast_det]
    change (((integralMatrix A).submatrix f g).map (Int.castRingHom ℚ)).det ≠ 0
    rw [he, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hS) hf
  exact fun hz => hd (by rw [hz]; simp)

/-- Exact positive normalization transports the proved product regularity
    to the integer interface used by the cofactor-preservation theorem. -/
theorem integralMatrix_regularOrderedLabel {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (c : Option (Fin n))
    (f : Fin (d + 1) → Fin n)
    (hr : ∀ v : Fin (d + 1) → ℚ, v ≠ 0 → StarFeasible A c v →
      (∀ j : Fin d, A (f j.succ) ⬝ᵥ v = 0) →
      (A.submatrix (fun j : Fin d => f j.succ) Fin.succ).det ≠ 0 ∧
      ∀ i, i ∉ Set.range (fun j : Fin d => f j.succ) →
        0 < starSign c i * (A i ⬝ᵥ v)) :
    RegularOrderedLabel (integralMatrix A) (starUnit c) f := by
  intro v hv hfeas hactive
  have hS : (0 : ℚ) < matrixDenominator A := by
    exact_mod_cast (integralMatrix_positive_scaling A).1
  let q : Fin (d + 1) → ℚ := fun j => (v j : ℚ)
  have hq : q ≠ 0 := by
    obtain ⟨j, hj⟩ := hv
    intro hz
    have he : (v j : ℚ) = 0 := congrFun hz j
    exact hj (Int.cast_eq_zero.mp he)
  have hqfeas : StarFeasible A c q := by
    intro i
    have he : (0 : ℚ) ≤ ((starUnit c i : ℤ) * ∑ j, integralMatrix A i j * v j : ℤ) := by
      exact_mod_cast hfeas i
    rw [integralMatrix_signed_value] at he
    exact nonneg_of_mul_nonneg_right he hS
  have hqactive : ∀ k : Fin d, A (f k.succ) ⬝ᵥ q = 0 := by
    intro k
    have he : (∑ j, (integralMatrix A (f k.succ) j : ℚ) * (v j : ℚ)) = 0 := by
      exact_mod_cast hactive k
    simp only [integralMatrix_value, mul_assoc, ← Finset.mul_sum] at he
    exact (mul_eq_zero.mp he).resolve_left hS.ne'
  obtain ⟨hd, hs⟩ := hr q hq hqfeas hqactive
  refine ⟨integralMatrix_subminor_nonzero A _ _ hd, ?_⟩
  intro i hi
  have he : (0 : ℚ) < ((starUnit c i : ℤ) * ∑ j, integralMatrix A i j * v j : ℤ) := by
    rw [integralMatrix_signed_value]
    exact mul_pos hS (hs i hi)
  exact_mod_cast he

/-- Instantiated for the actual two copies of the first perturbation:
    no product regularity or strict-chart hypothesis is left to supply. -/
theorem secondIntegral_regularity {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (f : Fin (d + d + 1) → Fin (n + n))
    (hf : Function.Injective (fun j : Fin (d + d) => f j.succ)) :
    RegularOrderedLabel (secondIntegralMatrix A C) (starUnit c) f := by
  apply integralMatrix_regularOrderedLabel (firstProduct A C) c f
  intro v hv hfeas hactive
  exact (constructed_product_regularity A C h0 hn c v hfeas hv _ hf hactive).2

/-- The SECOND perturbation's cofactor equivalence now has its regularity,
    all coefficient bounds, and nonzero minor polynomial discharged from
    the constructed product and its original finite chart input. -/
theorem second_cofactor_preservation {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (f : Fin (d + d + 1) → Fin (n + n))
    (hf : Function.Injective f) (u : ℤˣ) :
    let P := secondIntegralMatrix A C
    let D : Matrix (Fin (n + n)) (Fin (d + d + 1)) ℤ := integerVandermonde
    let B := starEnvelope P D (secondIntegralChart A C h0)
    let Z := fun j => u •
      (linearMatrix (fun i j => P (f i) j) (fun i j => D (f i) j)).adjugate j 0
    ((∃ j, (Z j).coeff 0 ≠ 0) ∧
      (∀ i, 0 ≤ (starUnit c i : ℤ) * ∑ j, P i j * (Z j).coeff 0)) ↔
      (∀ i, 0 ≤ (starUnit c i • rowPolynomial P D Z i).eval₂
        (Int.castRingHom ℚ) (commonParameter (d + d + 1) B)) := by
  let P := secondIntegralMatrix A C
  let D : Matrix (Fin (n + n)) (Fin (d + d + 1)) ℤ := integerVandermonde
  have hb := starEnvelope_bounds P D (secondIntegralChart A C h0)
  exact regular_cofactor_feasibility_iff P D f (starUnit c) u _ hb.1 hb.2.1 hb.2.2.1
    (integer_minor_nonzero P f hf)
    (secondIntegral_regularity A C h0 hn c f (hf.comp (Fin.succ_injective _)))

#print axioms second_cofactor_preservation
#print axioms secondIntegral_regularity
end
end ADKZPricing
