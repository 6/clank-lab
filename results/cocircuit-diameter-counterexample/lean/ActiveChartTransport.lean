import SecondLabelEquivalence

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Existence on ORIGINAL active rows, with a nonzero feasible ray.
    The label list is not a quotient of a shared face. -/
def ActiveRay {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n d k : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (c : Option (Fin n))
    (label : Fin k → Fin n) : Prop :=
  ∃ v, v ≠ 0 ∧ StarFeasible A c v ∧ ∀ j, A (label j) ⬝ᵥ v = 0

def IntegralActiveRay {n r k : ℕ} (A : Matrix (Fin n) (Fin r) ℤ)
    (c : Option (Fin n)) (label : Fin k → Fin n) : Prop :=
  ∃ v : Fin r → ℤ, (∃ j, v j ≠ 0) ∧
    (∀ i, 0 ≤ (starUnit c i : ℤ) * ∑ j, A i j * v j) ∧
    ∀ j, ∑ k, A (label j) k * v k = 0

theorem integral_ray_field_iff {n d k : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (c : Option (Fin n)) (label : Fin k → Fin n) :
    IntegralActiveRay A c label ↔ ActiveRay (A.map (Int.castRingHom ℚ)) c label := by
  have hs (i : Fin n) : ((starUnit c i : ℤ) : ℚ) = starSign c i := by
    unfold starUnit starSign
    split_ifs <;> norm_num
  constructor
  · rintro ⟨v, ⟨j, hj⟩, hf, ha⟩
    refine ⟨fun l => (v l : ℚ), ?_, ?_, ?_⟩
    · intro hz
      have he := congrFun hz j
      change (v j : ℚ) = 0 at he
      exact hj (by exact_mod_cast he)
    · intro i
      have he : (0 : ℚ) ≤ ((starUnit c i : ℤ) : ℚ) *
          ∑ j, (A i j : ℚ) * (v j : ℚ) := by exact_mod_cast hf i
      simpa only [hs, dotProduct, Matrix.map_apply, Int.coe_castRingHom] using he
    · intro j
      change ∑ l, (A (label j) l : ℚ) * (v l : ℚ) = 0
      exact_mod_cast ha j
  · rintro ⟨v, hv, hf, ha⟩
    let w := integralNumerator v
    have hp : (0 : ℚ) < commonDenominator v := by
      exact_mod_cast commonDenominator_positive v
    have he (i : Fin n) : ((∑ j, A i j * w j : ℤ) : ℚ) =
        (commonDenominator v : ℚ) * ((A.map (Int.castRingHom ℚ)) i ⬝ᵥ v) := by
      simp only [Int.cast_sum, Int.cast_mul, w, integralNumerator_value,
        dotProduct, Matrix.map_apply, Int.coe_castRingHom, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨w, ?_, ?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      push_neg at hn
      apply hv
      ext j
      have hz : (commonDenominator v : ℚ) * v j = 0 := by
        rw [← integralNumerator_value v j]
        simp only [show integralNumerator v j = 0 from hn j, Int.cast_zero]
      exact (mul_eq_zero.mp hz).resolve_left hp.ne'
    · intro i
      have hz : (0 : ℚ) ≤ ((starUnit c i : ℤ) : ℚ) * (∑ j, A i j * w j : ℤ) := by
        rw [he, hs, mul_left_comm]
        exact mul_nonneg hp.le (hf i)
      exact_mod_cast hz
    · intro j
      have hz : ((∑ l, A (label j) l * w l : ℤ) : ℚ) = 0 := by
        rw [he, ha j, mul_zero]
      exact_mod_cast hz

/-- Both the matrix and ray denominators are cleared positively. No
    decimal expansion, rationality assumption on a real ray, or label
    relabelling is smuggled into this equivalence. -/
theorem integral_matrix_active_iff {n d k : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℚ) (c : Option (Fin n))
    (label : Fin k → Fin n) :
    IntegralActiveRay (integralMatrix A) c label ↔ ActiveRay A c label := by
  rw [integral_ray_field_iff]
  have hp : (0 : ℚ) < matrixDenominator A := by
    exact_mod_cast (integralMatrix_positive_scaling A).1
  have he (i : Fin n) (v : Fin (d + 1) → ℚ) :
      ((integralMatrix A).map (Int.castRingHom ℚ)) i ⬝ᵥ v =
        (matrixDenominator A : ℚ) * (A i ⬝ᵥ v) := by
    simp only [dotProduct, Matrix.map_apply, Int.coe_castRingHom, integralMatrix_value,
      Finset.mul_sum, mul_assoc]
  constructor <;> rintro ⟨v, hv, hf, ha⟩
  · refine ⟨v, hv, (integralMatrix_star_iff A c v).mp hf, ?_⟩
    intro j
    exact (mul_eq_zero.mp ((he (label j) v).symm.trans (ha j))).resolve_left hp.ne'
  · refine ⟨v, hv, (integralMatrix_star_iff A c v).mpr hf, ?_⟩
    intro j
    rw [he, ha j, mul_zero]

/-- Inverse chart maps preserve nonzero rays and every original row.
    This holds for an arbitrary active list, including common faces. -/
theorem chart_active_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n d k : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (h : Fin (d + 1) → K)
    (hh : 0 < h 0) (c : Option (Fin n)) (label : Fin k → Fin n) :
    ActiveRay (chartRebased A h) c label ↔ ActiveRay A c label := by
  have hz : chartCoordinates h 0 = 0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [chartCoordinates]
  constructor
  · rintro ⟨u, hu, hf, ha⟩
    let v := chartCoordinatesInv h u
    have he : chartCoordinates h v = u := chartCoordinates_right_inverse h hh.ne' u
    have ht := chartRebased_signed_slacks A h v hh (starSign c)
    refine ⟨v, ?_, ?_, ?_⟩
    · intro hv
      rw [hv, hz] at he
      exact hu he.symm
    · intro i
      apply (ht.1 i).mp
      rw [he]
      exact hf i
    · intro j
      apply (ht.2 (label j)).mp
      rw [he]
      exact ha j
  · rintro ⟨v, hv, hf, ha⟩
    have ht := chartRebased_signed_slacks A h v hh (starSign c)
    refine ⟨chartCoordinates h v, ?_, fun i => (ht.1 i).mpr (hf i),
      fun j => (ht.2 (label j)).mpr (ha j)⟩
    intro he
    have hv' := chartCoordinates_left_inverse h hh.ne' v
    have hzero : chartCoordinatesInv h 0 = 0 := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [chartCoordinatesInv]
    rw [he, hzero] at hv'
    exact hv hv'.symm

/-- The actual second perturbation preserves active labels in both
    directions from the ORIGINAL rational product through BOTH exact
    normalizations and the final chart, for ALL shared star signs. -/
theorem second_product_active_iff {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (f : Fin (d + d + 1) → Fin (n + n))
    (hf : Function.Injective f) :
    ActiveRay (secondPerturbedMatrix A C h0) c (fun j => f j.succ) ↔
      ActiveRay (firstProduct A C) c (fun j => f j.succ) := by
  unfold secondPerturbedMatrix chartedGenericFactor
  rw [chart_active_iff _ _ (by exact_mod_cast secondIntegralChart_pivot A C h0)]
  have hs (i : Fin (n + n)) : ((starUnit c i : ℤ) : ℚ) = starSign c i := by
    unfold starUnit starSign
    split_ifs <;> norm_num
  have he := second_active_label_equivalence A C h0 hn c f hf
  change IntegralActiveRay (secondIntegralMatrix A C) c (fun j => f j.succ) ↔ _ at he
  simp only [hs] at he
  exact he.symm.trans (integral_matrix_active_iff (firstProduct A C) c _)

#print axioms integral_matrix_active_iff
#print axioms chart_active_iff
#print axioms second_product_active_iff
end
end ADKZPricing
