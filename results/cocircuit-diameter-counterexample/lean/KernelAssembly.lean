import SignControl
import CoefficientEnvelope

namespace ADKZPricing
open Polynomial Finset Matrix
noncomputable section

def cofactorBound (r : ℕ) (B : ℤ) : ℤ := Nat.factorial r * (2 * B) ^ r
def slackBound (r : ℕ) (B : ℤ) : ℤ := r * (2 * B * cofactorBound r B)
/- The factor two also covers corrected positive chart representations:
   one determinant term plus r cofactor terms, for r >= 1. -/
def commonMassBound (r : ℕ) (B : ℤ) : ℤ := (r + 1) * (2 * slackBound r B)
def commonParameter (r : ℕ) (B : ℤ) : ℚ := 1 / ((commonMassBound r B : ℚ) + 2)

theorem cofactorBound_nonnegative (r : ℕ) (B : ℤ) (hB : 0 ≤ B) :
    0 ≤ cofactorBound r B := by
  unfold cofactorBound
  positivity

theorem slackBound_nonnegative (r : ℕ) (B : ℤ) (hB : 0 ≤ B) :
    0 ≤ slackBound r B := by
  unfold slackBound
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by omega) (cofactorBound_nonnegative r B hB))

theorem commonMassBound_nonnegative (r : ℕ) (B : ℤ) (hB : 0 ≤ B) :
    0 ≤ commonMassBound r B :=
  mul_nonneg (by positivity) (mul_nonneg (by norm_num) (slackBound_nonnegative r B hB))

theorem commonParameter_bounds (r : ℕ) (B : ℤ) (hB : 0 ≤ B) :
    0 < commonParameter r B ∧ commonParameter r B ≤ 1 ∧
      commonParameter r B * commonMassBound r B < 1 := by
  have hm : (0 : ℚ) ≤ commonMassBound r B := by
    exact_mod_cast commonMassBound_nonnegative r B hB
  have hd : (0 : ℚ) < commonMassBound r B + 2 := by linarith
  unfold commonParameter
  refine ⟨one_div_pos.mpr hd, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith
  · rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ hd).mpr
    linarith

theorem common_tail_bound (r : ℕ) (B : ℤ) (hB : 0 ≤ B)
    (p : Polynomial ℤ) (N : ℕ) (H : ℤ) (hH : 0 ≤ H)
    (hp : CoeffEnvelope p N H) (hsize : (N : ℤ) * H ≤ commonMassBound r B) :
    commonParameter r B * tailMass (range p.natDegree) (fun k => p.coeff (k + 1)) < 1 := by
  have ht := commonParameter_bounds r B hB
  have hm : tailMass (range p.natDegree) (fun k => p.coeff (k + 1)) ≤
      (commonMassBound r B : ℚ) := by
    apply (envelope_tail_mass p N H hH hp).trans
    exact_mod_cast hsize
  exact (mul_le_mul_of_nonneg_left hm ht.1.le).trans_lt ht.2.2

theorem common_constant_nonnegative (r : ℕ) (B : ℤ) (hB : 0 ≤ B)
    (p : Polynomial ℤ) (N : ℕ) (H : ℤ) (hH : 0 ≤ H)
    (hp : CoeffEnvelope p N H) (hsize : (N : ℤ) * H ≤ commonMassBound r B)
    (heval : 0 ≤ p.eval₂ (Int.castRingHom ℚ) (commonParameter r B)) :
    0 ≤ p.coeff 0 :=
  polynomial_constant_nonnegative p _ (commonParameter_bounds r B hB).1.le
    (commonParameter_bounds r B hB).2.1
    (common_tail_bound r B hB p N H hH hp hsize) heval

theorem common_positive_eval (r : ℕ) (B : ℤ) (hB : 0 ≤ B)
    (p : Polynomial ℤ) (N : ℕ) (H : ℤ) (hH : 0 ≤ H)
    (hp : CoeffEnvelope p N H) (hsize : (N : ℤ) * H ≤ commonMassBound r B)
    (hc : 0 < p.coeff 0) : 0 < p.eval₂ (Int.castRingHom ℚ) (commonParameter r B) := by
  have h := positive_eval_of_positive_constant (range p.natDegree)
    (fun k => p.coeff (k + 1)) (p.coeff 0) (commonParameter r B)
    (commonParameter_bounds r B hB).1.le (commonParameter_bounds r B hB).2.1
    (common_tail_bound r B hB p N H hH hp hsize) hc
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ']
  simpa [integerTail, add_comm] using h

theorem common_eval_nonzero (r : ℕ) (B : ℤ) (hB : 0 ≤ B)
    (p : Polynomial ℤ) (N : ℕ) (H : ℤ) (hH : 0 ≤ H)
    (hp : CoeffEnvelope p N H) (hsize : (N : ℤ) * H ≤ commonMassBound r B)
    (hc : p.coeff 0 ≠ 0) : p.eval₂ (Int.castRingHom ℚ) (commonParameter r B) ≠ 0 := by
  intro heq
  have hpos := common_constant_nonnegative r B hB p N H hH hp hsize (by rw [heq])
  have hneg := common_constant_nonnegative r B hB (-p) N H hH (envelope_neg p N H hp)
    hsize (by simp [heq])
  simp only [Polynomial.coeff_neg] at hneg
  exact hc (by omega)

theorem common_mass_covers_cofactor (r : ℕ) (hr : 0 < r) (B : ℤ) (hB : 1 ≤ B) :
    (r : ℤ) * cofactorBound r B ≤ commonMassBound r B := by
  have hH := cofactorBound_nonnegative r B (by omega)
  have hS := slackBound_nonnegative r B (by omega)
  have hri : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hHS : cofactorBound r B ≤ slackBound r B := by
    unfold slackBound
    calc
      cofactorBound r B ≤ 2 * B * cofactorBound r B := by nlinarith
      _ ≤ (r : ℤ) * (2 * B * cofactorBound r B) := by
        have ht : 0 ≤ 2 * B * cofactorBound r B := by positivity
        nlinarith
  unfold commonMassBound
  exact (mul_le_mul_of_nonneg_left hHS (by positivity)).trans
    (by nlinarith)

/-- Zero constant terms are handled by factoring a common power, so this
    applies to every nonzero minor, including initially singular ones. -/
theorem common_nonzero_polynomial (r : ℕ) (B : ℤ) (hB : 0 ≤ B)
    (p : Polynomial ℤ) (N : ℕ) (H : ℤ) (hH : 0 ≤ H)
    (hp : CoeffEnvelope p N H) (hsize : (N : ℤ) * H ≤ commonMassBound r B)
    (hne : p ≠ 0) : p.eval₂ (Int.castRingHom ℚ) (commonParameter r B) ≠ 0 := by
  obtain ⟨m, W, hf, j, hj⟩ := normalize_polynomial_vector (fun _ : Fin 1 => p) ⟨0, hne⟩
  have hw := envelope_remove_common_power p (W j) m N H (hf j) hp
  have hn := common_eval_nonzero r B hB (W j) N H hH hw hsize hj
  rw [hf j, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  exact mul_ne_zero (pow_ne_zero _ (commonParameter_bounds r B hB).1.ne') hn

theorem rowPolynomial_unit {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ)
    (W : Fin r → Polynomial ℤ) (u : ℤˣ) (i : Fin n) :
    rowPolynomial A D (fun j => u • W j) i = u • rowPolynomial A D W i := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp [rowPolynomial, Units.smul_def, Finset.sum_neg_distrib]

theorem oriented_cofactor_equation {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (b : Fin r)
    (hdet : (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det ≠ 0)
    (u : ℤˣ) (i : Fin r) (hi : i ≠ b) :
    rowPolynomial A D (fun j => u •
      (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).adjugate j b) (f i) = 0 := by
  rw [rowPolynomial_unit]
  have hk := (cofactor_kernel _ b hdet).1 i hi
  have heq : rowPolynomial A D (fun j =>
      (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).adjugate j b) (f i) = 0 := by
    simpa only [rowPolynomial, linearMatrix, linearEntry] using hk
  rw [heq, smul_zero]

/-- Chart coordinates count in the SAME entry bound as arrangement rows.
    All signs/orientations are covered by the unit action, without cases
    over bases or cells. This is an algebraic envelope, not preservation. -/
theorem normalized_cofactor_envelopes {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (b : Fin r)
    (h : Fin r → ℤ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hh : ∀ j, |h j| ≤ B)
    (hdet : (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det ≠ 0)
    (u : ℤˣ) :
    let K := linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)
    ∃ m : ℕ, ∃ W : Fin r → Polynomial ℤ,
      (∀ j, u • K.adjugate j b = X ^ m * W j) ∧
      (∃ j, (W j).coeff 0 ≠ 0) ∧
      (∀ j, CoeffEnvelope (W j) r (cofactorBound r B)) ∧
      (∀ i, ∀ s : ℤˣ, CoeffEnvelope (s • rowPolynomial A D W i) (r + 1) (slackBound r B)) ∧
      (∀ s : ℤˣ, CoeffEnvelope (s • ∑ j, C (h j) * W j) (r + 1) (slackBound r B)) := by
  dsimp only
  let K := linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)
  let Z : Fin r → Polynomial ℤ := fun j => u • K.adjugate j b
  have hZ : ∃ j, Z j ≠ 0 := by
    obtain ⟨j, hj⟩ := (cofactor_kernel K b hdet).2
    refine ⟨j, ?_⟩
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      simpa [Z, Units.smul_def] using hj
  obtain ⟨m, W, hf, hw⟩ := normalize_polynomial_vector Z hZ
  have hH : 0 ≤ cofactorBound r B := cofactorBound_nonnegative r B (by omega)
  have henv : ∀ j, CoeffEnvelope (W j) r (cofactorBound r B) := by
    intro j
    apply envelope_remove_common_power (Z j) (W j) m r _ (hf j)
    apply envelope_signed
    exact envelope_adjugate _ _ B hB (fun i j => ha (f i) j) (fun i j => hd (f i) j) j b
  refine ⟨m, W, hf, hw, henv, ?_, ?_⟩
  · intro i s
    apply envelope_signed
    exact envelope_slack (A i) (D i) W r B _ (by omega) hH (ha i) (hd i) henv
  · intro s
    apply envelope_signed
    simpa [linearEntry] using envelope_slack h (fun _ => 0) W r B _ (by omega)
      hH hh (fun _ => by simpa using (show (0 : ℤ) ≤ B by omega)) henv

theorem normalized_cofactor_specialization {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (b : Fin r)
    (h : Fin r → ℤ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B) (hh : ∀ j, |h j| ≤ B)
    (hdet : (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det ≠ 0)
    (u : ℤˣ) :
    let K := linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)
    ∃ m : ℕ, ∃ W : Fin r → Polynomial ℤ,
      (∀ j, u • K.adjugate j b = X ^ m * W j) ∧
      (∃ j, (W j).coeff 0 ≠ 0) ∧
      (∃ j, (W j).eval₂ (Int.castRingHom ℚ) (commonParameter r B) ≠ 0) ∧
      (∀ i, i ≠ b → rowPolynomial A D W (f i) = 0) ∧
      (∀ i, ∀ s : ℤˣ,
        0 ≤ (s • rowPolynomial A D W i).eval₂ (Int.castRingHom ℚ) (commonParameter r B) →
        0 ≤ (s : ℤ) * ∑ j, A i j * (W j).coeff 0) ∧
      (∀ s : ℤˣ,
        0 ≤ (s • ∑ j, C (h j) * W j).eval₂ (Int.castRingHom ℚ) (commonParameter r B) →
        0 ≤ (s : ℤ) * ∑ j, h j * (W j).coeff 0) := by
  dsimp only
  obtain ⟨m, W, hf, hw, henv, hslack, hchart⟩ :=
    normalized_cofactor_envelopes A D f b h B hB ha hd hh hdet u
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le b.val) b.isLt
  have hH := cofactorBound_nonnegative r B (by omega)
  have hS := slackBound_nonnegative r B (by omega)
  have hsize : ((r + 1 : ℕ) : ℤ) * slackBound r B ≤ commonMassBound r B := by
    simp only [Nat.cast_add, Nat.cast_one, commonMassBound]
    nlinarith
  refine ⟨m, W, hf, hw, ?_, ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hw
    exact ⟨j, common_eval_nonzero r B (by omega) (W j) r _ hH (henv j)
      (common_mass_covers_cofactor r hr B hB) hj⟩
  · intro i hi
    exact normalized_kernel_equation A D _ W m hf (f i)
      (oriented_cofactor_equation A D f b hdet u i hi)
  · intro i s hs
    have hc := common_constant_nonnegative r B (by omega) _ (r + 1) _ hS (hslack i s) hsize hs
    simpa only [Polynomial.coeff_smul, rowPolynomial_constant, Units.smul_def, smul_eq_mul] using hc
  · intro s hs
    have hc := common_constant_nonnegative r B (by omega) _ (r + 1) _ hS (hchart s) hsize hs
    simpa [Polynomial.coeff_smul, Units.smul_def, smul_eq_mul] using hc

#print axioms common_nonzero_polynomial
#print axioms normalized_cofactor_envelopes
#print axioms normalized_cofactor_specialization
end
end ADKZPricing
