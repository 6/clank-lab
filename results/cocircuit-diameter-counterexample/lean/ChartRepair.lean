import UniformSpecialization

namespace ADKZPricing
open Polynomial Finset Matrix
noncomputable section

def chartNumerator {r : ℕ} (K : Matrix (Fin r) (Fin r) (Polynomial ℤ))
    (l : ℤ) (q : Fin r → ℤ) (j : Fin r) : Polynomial ℤ :=
  C l * K.det - X * ∑ k, C (q k) * K.adjugate k j

theorem constant_linear_determinant {r : ℕ} (A D : Matrix (Fin r) (Fin r) ℤ) :
    (linearMatrix A D).det.coeff 0 = A.det := by
  have h := RingHom.map_det (Polynomial.constantCoeff : Polynomial ℤ →+* ℤ) (linearMatrix A D)
  have heq : (linearMatrix A D).map Polynomial.constantCoeff = A := by
    ext i j
    simp [Matrix.map_apply, linearMatrix, linearEntry]
  change (linearMatrix A D).det.coeff 0 = ((linearMatrix A D).map Polynomial.constantCoeff).det at h
  rw [heq] at h
  exact h

theorem chartNumerator_constant {r : ℕ} (A D : Matrix (Fin r) (Fin r) ℤ)
    (l : ℤ) (q : Fin r → ℤ) (j : Fin r) :
    (chartNumerator (linearMatrix A D) l q j).coeff 0 = l * A.det := by
  simp [chartNumerator, constant_linear_determinant]

theorem chartNumerator_envelope {r : ℕ} (hr : 0 < r) (A D : Matrix (Fin r) (Fin r) ℤ)
    (l : ℤ) (q : Fin r → ℤ) (j : Fin r) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i k, |A i k| ≤ B) (hd : ∀ i k, |D i k| ≤ B)
    (hl : |l| ≤ B) (hq : ∀ k, |q k| ≤ B) :
    CoeffEnvelope (chartNumerator (linearMatrix A D) l q j) (r + 1) (2 * slackBound r B) := by
  have hH := cofactorBound_nonnegative r B (by omega)
  have hdet := envelope_determinant A D B (by omega) ha hd
  have hfirst : CoeffEnvelope (C l * (linearMatrix A D).det) (r + 1)
      (2 * B * cofactorBound r B) := by
    simpa [linearEntry] using envelope_linear_mul l 0 _ r B _ (by omega) hH hl
      (by simpa using (show (0 : ℤ) ≤ B by omega)) hdet
  have hsecond : CoeffEnvelope (∑ k, linearEntry 0 (-q k) * (linearMatrix A D).adjugate k j)
      (r + 1) (slackBound r B) := by
    exact envelope_slack (fun _ => 0) (fun k => -q k) _ r B _ (by omega) hH
      (fun _ => by simpa using (show (0 : ℤ) ≤ B by omega))
      (fun k => by simpa using hq k)
      (fun k => envelope_adjugate A D B hB ha hd k j)
  have heq : chartNumerator (linearMatrix A D) l q j =
      C l * (linearMatrix A D).det +
        ∑ k, linearEntry 0 (-q k) * (linearMatrix A D).adjugate k j := by
    simp [chartNumerator, linearEntry, sub_eq_add_neg, Finset.mul_sum, mul_assoc]
  rw [heq]
  apply envelope_weaken _ _ _ _ (envelope_add _ _ _ _ _ hfirst hsecond)
  have hri : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hc : 0 ≤ 2 * B * cofactorBound r B := by positivity
  unfold slackBound
  nlinarith

/-- Exact adjugate identity behind correcting the coefficients on a
    fixed full-rank subsystem, with the chart functional held fixed. -/
theorem cofactor_correction_identity {r : ℕ}
    (K : Matrix (Fin r) (Fin r) (Polynomial ℤ)) (q : Fin r → Polynomial ℤ) (j : Fin r) :
    ∑ i, (∑ k, q k * K.adjugate k i) * K i j = K.det * q j := by
  have h := congrArg (fun v : Fin r → Polynomial ℤ => v j) (Matrix.vecMul_vecMul q K.adjugate K)
  rw [Matrix.adjugate_mul] at h
  simpa [Matrix.vecMul, dotProduct, Matrix.one_apply, mul_comm] using h

def repairedWeights {n r : ℕ} (N : Matrix (Fin n) (Fin r) (Polynomial ℤ))
    (f : Fin r → Fin n) (l : Fin n → Polynomial ℤ) (q : Fin r → Polynomial ℤ) :
    Fin n → Polynomial ℤ :=
  fun i => l i * (N.submatrix f id).det -
    X * ∑ a, if f a = i then (∑ k, q k * (N.submatrix f id).adjugate k a) else 0

theorem repairedWeights_identity {n r : ℕ}
    (N : Matrix (Fin n) (Fin r) (Polynomial ℤ)) (f : Fin r → Fin n)
    (l : Fin n → Polynomial ℤ) (q h : Fin r → Polynomial ℤ)
    (hrep : ∀ j, ∑ i, l i * N i j = h j + X * q j) :
    ∀ j, ∑ i, repairedWeights N f l q i * N i j = (N.submatrix f id).det * h j := by
  intro j
  let K := N.submatrix f id
  have hc := cofactor_correction_identity K q j
  have hsum : (∑ i, (∑ a, if f a = i then (∑ k, q k * K.adjugate k a) else 0) * N i j) =
      ∑ a, (∑ k, q k * K.adjugate k a) * N (f a) j := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [Finset.sum_mul]
  change (∑ i, (l i * K.det - X * ∑ a,
    if f a = i then (∑ k, q k * K.adjugate k a) else 0) * N i j) = K.det * h j
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
  rw [← Finset.mul_sum]
  have hmain : (∑ i, l i * (K.det * N i j)) = K.det * ∑ i, l i * N i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmain, hrep j]
  have hsum' : (∑ i, (∑ a, if f a = i then (∑ k, q k * K.adjugate k a) else 0) * N i j) =
      K.det * q j := by
    rw [hsum]
    exact hc
  rw [hsum']
  ring

theorem repairedWeights_selected {n r : ℕ}
    (N : Matrix (Fin n) (Fin r) (Polynomial ℤ)) (f : Fin r → Fin n) (hf : Function.Injective f)
    (l : Fin n → Polynomial ℤ) (q : Fin r → Polynomial ℤ) (a : Fin r) :
    repairedWeights N f l q (f a) = l (f a) * (N.submatrix f id).det -
      X * ∑ k, q k * (N.submatrix f id).adjugate k a := by
  simp [repairedWeights, hf.eq_iff]

theorem linear_weighted_representation {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (l : Fin n → ℤ) (j : Fin r) :
    (∑ i, C (l i) * linearMatrix A D i j) =
      C (∑ i, l i * A i j) + X * C (∑ i, l i * D i j) := by
  simp [linearMatrix, linearEntry, Finset.sum_add_distrib, Finset.mul_sum,
    mul_add, mul_left_comm, mul_assoc]

theorem repairedWeights_fixed_chart {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (l : Fin n → ℤ) :
    ∀ j, ∑ i, repairedWeights (linearMatrix A D) f (fun i => C (l i))
      (fun k => C (∑ i, l i * D i k)) i * linearMatrix A D i j =
      ((linearMatrix A D).submatrix f id).det * C (∑ i, l i * A i j) :=
  repairedWeights_identity _ _ _ _ _ (linear_weighted_representation A D l)

theorem positive_weighted_chart {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) 𝕜) (l : Fin n → 𝕜) (h : Fin r → 𝕜)
    (hl : ∀ i, 0 < l i) (hrep : ∀ j, h j = ∑ i, l i * A i j)
    (v : Fin r → 𝕜) (hfeas : ∀ i, 0 ≤ ∑ j, A i j * v j)
    (hne : ∃ i, (∑ j, A i j * v j) ≠ 0) : 0 < ∑ j, h j * v j := by
  have heq : (∑ j, h j * v j) = ∑ i, l i * (∑ j, A i j * v j) := by
    simp only [hrep, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  obtain ⟨i, hi⟩ := hne
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hl k).le (hfeas k))
    ⟨i, Finset.mem_univ _, mul_pos (hl i) (lt_of_le_of_ne (hfeas i) (Ne.symm hi))⟩

theorem full_rank_detects_nonzero {𝕜 : Type*} [Field 𝕜] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) 𝕜) (f : Fin r → Fin n)
    (hdet : (A.submatrix f id).det ≠ 0) (v : Fin r → 𝕜) (hv : v ≠ 0) :
    ∃ i, (∑ j, A i j * v j) ≠ 0 := by
  by_contra hn
  push_neg at hn
  let K := A.submatrix f id
  have hk : K *ᵥ v = 0 := by
    ext i
    exact hn (f i)
  have hid : K.adjugate *ᵥ (K *ᵥ v) = K.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  rw [hk, Matrix.mulVec_zero] at hid
  apply hv
  ext j
  have hj := congrArg (fun w : Fin r → 𝕜 => w j) hid
  change 0 = K.det * v j at hj
  exact (mul_eq_zero.mp hj.symm).resolve_left hdet

theorem evaluated_chart_representation {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (l : Fin n → ℤ) (t : ℚ)
    (hden : ((linearMatrix A D).submatrix f id).det.eval₂ (Int.castRingHom ℚ) t ≠ 0) :
    ∀ j, ∑ i,
      ((repairedWeights (linearMatrix A D) f (fun i => C (l i))
        (fun k => C (∑ i, l i * D i k)) i).eval₂ (Int.castRingHom ℚ) t /
          ((linearMatrix A D).submatrix f id).det.eval₂ (Int.castRingHom ℚ) t) *
      specializedMatrix A D t i j = ((∑ i, l i * A i j : ℤ) : ℚ) := by
  intro j
  let E := Polynomial.eval₂RingHom (Int.castRingHom ℚ) t
  let N := linearMatrix A D
  let K := N.submatrix f id
  let w := repairedWeights N f (fun i => C (l i)) (fun k => C (∑ i, l i * D i k))
  have he (i : Fin n) : E (N i j) = specializedMatrix A D t i j := by
    change (C (A i j) + X * C (D i j)).eval₂ (Int.castRingHom ℚ) t = _
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rfl
  have heq := congrArg E (repairedWeights_fixed_chart A D f l j)
  change E (∑ i, w i * N i j) = E (K.det * C (∑ i, l i * A i j)) at heq
  simp only [map_sum, map_mul] at heq
  change (∑ i, E (w i) / E K.det * specializedMatrix A D t i j) = _
  calc
    (∑ i, E (w i) / E K.det * specializedMatrix A D t i j) =
        (∑ i, E (w i) * E (N i j)) / E K.det := by
      simp only [he, Finset.sum_div, div_mul_eq_mul_div]
    _ = (E K.det * E (C (∑ i, l i * A i j))) / E K.det := by
      rw [heq]
      simp only [map_sum, map_mul]
    _ = E (C (∑ i, l i * A i j)) := mul_div_cancel_left₀ _ hden
    _ = ((∑ i, l i * A i j : ℤ) : ℚ) := by
      change (C (∑ i, l i * A i j)).eval₂ (Int.castRingHom ℚ) t = _
      simp only [Polynomial.eval₂_C, Int.castRingHom]
      rfl

theorem repairedWeights_envelope {n r : ℕ} (hr : 0 < r)
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (hf : Function.Injective f)
    (l : Fin n → ℤ) (q : Fin r → ℤ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hl : ∀ i, |l i| ≤ B) (hq : ∀ j, |q j| ≤ B) (i : Fin n) :
    CoeffEnvelope (repairedWeights (linearMatrix A D) f (fun i => C (l i)) (fun j => C (q j)) i)
      (r + 1) (2 * slackBound r B) := by
  by_cases hi : ∃ a, f a = i
  · obtain ⟨a, rfl⟩ := hi
    rw [repairedWeights_selected _ _ hf]
    exact chartNumerator_envelope hr (A.submatrix f id) (D.submatrix f id) (l (f a)) q a B hB
      (fun i j => ha (f i) j) (fun i j => hd (f i) j) (hl (f a)) hq
  · push_neg at hi
    simp only [repairedWeights, if_neg (hi _), sum_const_zero, mul_zero, sub_zero]
    have hH := cofactorBound_nonnegative r B (by omega)
    have hdet := envelope_determinant (A.submatrix f id) (D.submatrix f id) B (by omega)
      (fun i j => ha (f i) j) (fun i j => hd (f i) j)
    have hfirst : CoeffEnvelope (C (l i) * ((linearMatrix A D).submatrix f id).det) (r + 1)
        (2 * B * cofactorBound r B) := by
      simpa [linearEntry] using envelope_linear_mul (l i) 0 _ r B _ (by omega) hH
        (hl i) (by simpa using (show (0 : ℤ) ≤ B by omega)) hdet
    apply envelope_weaken _ _ _ _ hfirst
    have hri : (1 : ℤ) ≤ r := by exact_mod_cast hr
    have hc : 0 ≤ 2 * B * cofactorBound r B := by positivity
    unfold slackBound
    nlinarith

theorem repairedWeights_constant {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n)
    (l : Fin n → ℤ) (q : Fin r → ℤ) (i : Fin n) :
    (repairedWeights (linearMatrix A D) f (fun i => C (l i)) (fun j => C (q j)) i).coeff 0 =
      l i * (A.submatrix f id).det := by
  simp only [repairedWeights, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul_zero, sub_zero]
  rw [show (linearMatrix A D).submatrix f id = linearMatrix (A.submatrix f id) (D.submatrix f id) by rfl]
  rw [constant_linear_determinant]

theorem common_ratio_positive (r : ℕ) (hr : 0 < r) (B : ℤ) (hB : 1 ≤ B)
    (p q : Polynomial ℤ) (l : ℤ) (hl : 0 < l)
    (hp : CoeffEnvelope p (r + 1) (2 * slackBound r B))
    (hq : CoeffEnvelope q r (cofactorBound r B))
    (hc : p.coeff 0 = l * q.coeff 0) (hq0 : q.coeff 0 ≠ 0) :
    0 < p.eval₂ (Int.castRingHom ℚ) (commonParameter r B) /
      q.eval₂ (Int.castRingHom ℚ) (commonParameter r B) := by
  have hH := cofactorBound_nonnegative r B (by omega)
  have hS : 0 ≤ 2 * slackBound r B := mul_nonneg (by norm_num) (slackBound_nonnegative r B (by omega))
  have hsize : ((r + 1 : ℕ) : ℤ) * (2 * slackBound r B) ≤ commonMassBound r B := by
    simp [commonMassBound]
  have hqsize := common_mass_covers_cofactor r hr B hB
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · have hpneg : 0 < (-p).coeff 0 := by simp only [Polynomial.coeff_neg, hc]; nlinarith
    have hqneg : 0 < (-q).coeff 0 := by simpa using hneg
    have hep := common_positive_eval r B (by omega) (-p) _ _ hS
      (envelope_neg _ _ _ hp) hsize hpneg
    have heq := common_positive_eval r B (by omega) (-q) _ _ hH
      (envelope_neg _ _ _ hq) hqsize hqneg
    simp only [Polynomial.eval₂_neg] at hep heq
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · apply div_pos
    · exact common_positive_eval r B (by omega) p _ _ hS hp hsize (by rw [hc]; exact mul_pos hl hpos)
    · exact common_positive_eval r B (by omega) q _ _ hH hq hqsize hpos

theorem repairedWeights_positive {n r : ℕ} (hr : 0 < r)
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (hf : Function.Injective f)
    (l : Fin n → ℤ) (q : Fin r → ℤ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hl : ∀ i, |l i| ≤ B) (hq : ∀ j, |q j| ≤ B) (hlpos : ∀ i, 0 < l i)
    (hdet : (A.submatrix f id).det ≠ 0) :
    ∀ i, 0 <
      (repairedWeights (linearMatrix A D) f (fun i => C (l i)) (fun j => C (q j)) i).eval₂
        (Int.castRingHom ℚ) (commonParameter r B) /
      ((linearMatrix A D).submatrix f id).det.eval₂ (Int.castRingHom ℚ) (commonParameter r B) := by
  intro i
  apply common_ratio_positive r hr B hB _ _ (l i) (hlpos i)
    (repairedWeights_envelope hr A D f hf l q B hB ha hd hl hq i)
    (envelope_determinant (A.submatrix f id) (D.submatrix f id) B (by omega)
      (fun i j => ha (f i) j) (fun i j => hd (f i) j))
  · rw [repairedWeights_constant]
    congr 1
    exact (constant_linear_determinant (A.submatrix f id) (D.submatrix f id)).symm
  · exact (constant_linear_determinant (A.submatrix f id) (D.submatrix f id)).trans_ne hdet

/-- The chart itself is fixed. Only its strictly positive coefficients
    change, at the SAME explicit parameter used by the kernel bounds.
    The finite input certificate consists of l, f, the old identities,
    positivity, and bounds including the computed weighted D-row sums. -/
theorem strict_chart_certificate_persistence {n r : ℕ} (hr : 0 < r)
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (hf : Function.Injective f)
    (l : Fin n → ℤ) (h : Fin r → ℤ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hl : ∀ i, |l i| ≤ B) (hq : ∀ j, |∑ i, l i * D i j| ≤ B)
    (hlpos : ∀ i, 0 < l i) (hrep : ∀ j, h j = ∑ i, l i * A i j)
    (hdet : (A.submatrix f id).det ≠ 0) :
    ∃ θ : Fin n → ℚ,
      (∀ i, 0 < θ i) ∧
      (∀ j, (h j : ℚ) = ∑ i, θ i * specializedMatrix A D (commonParameter r B) i j) ∧
      ((specializedMatrix A D (commonParameter r B)).submatrix f id).det ≠ 0 := by
  let t := commonParameter r B
  let N := linearMatrix A D
  let K := N.submatrix f id
  let q : Fin r → ℤ := fun j => ∑ i, l i * D i j
  let w := repairedWeights N f (fun i => C (l i)) (fun j => C (q j))
  let θ : Fin n → ℚ := fun i => (w i).eval₂ (Int.castRingHom ℚ) t /
    K.det.eval₂ (Int.castRingHom ℚ) t
  have hden : K.det.eval₂ (Int.castRingHom ℚ) t ≠ 0 := by
    apply common_eval_nonzero r B (by omega) K.det r (cofactorBound r B)
      (cofactorBound_nonnegative r B (by omega))
      (envelope_determinant (A.submatrix f id) (D.submatrix f id) B (by omega)
        (fun i j => ha (f i) j) (fun i j => hd (f i) j))
      (common_mass_covers_cofactor r hr B hB)
    exact (constant_linear_determinant (A.submatrix f id) (D.submatrix f id)).trans_ne hdet
  refine ⟨θ, ?_, ?_, ?_⟩
  · exact repairedWeights_positive hr A D f hf l q B hB ha hd hl hq hlpos hdet
  · intro j
    rw [hrep j]
    exact (evaluated_chart_representation A D f l t hden j).symm
  · change Matrix.det (fun i j => specializedMatrix A D t (f i) j) ≠ 0
    rw [← eval_integer_minor A D f t]
    exact hden

#print axioms chartNumerator_envelope
#print axioms repairedWeights_identity
#print axioms repairedWeights_positive
#print axioms evaluated_chart_representation
#print axioms positive_weighted_chart
#print axioms full_rank_detects_nonzero
#print axioms strict_chart_certificate_persistence
end
end ADKZPricing
