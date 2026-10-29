import LabelTransport

namespace ADKZPricing
open Polynomial Finset Matrix
noncomputable section

theorem constant_linear_adjugate {r : ℕ} (A D : Matrix (Fin r) (Fin r) ℤ)
    (i j : Fin r) : ((linearMatrix A D).adjugate i j).coeff 0 = A.adjugate i j := by
  have h := (Polynomial.constantCoeff : Polynomial ℤ →+* ℤ).map_adjugate (linearMatrix A D)
  have heq : (linearMatrix A D).map Polynomial.constantCoeff = A := by
    ext k l
    simp [Matrix.map_apply, linearMatrix, linearEntry]
  change (linearMatrix A D).adjugate.map Polynomial.constantCoeff =
    ((linearMatrix A D).map Polynomial.constantCoeff).adjugate at h
  rw [heq] at h
  exact congrArg (fun K : Matrix (Fin r) (Fin r) ℤ => K i j) h

/-- The chart coordinate of the cofactor IS the active spatial minor,
    also when the arbitrary extra row makes the old full minor singular. -/
theorem cofactor_chart_constant {d : ℕ}
    (A D : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ) :
    ((linearMatrix A D).adjugate 0 0).coeff 0 =
      (A.submatrix Fin.succ Fin.succ).det := by
  rw [constant_linear_adjugate, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp

/-- The regularity interface required at an ordered active label. It
    includes all original rows, not merely facets of a simplified graph.
    Source/product certificate instantiation remains a separate step. -/
def RegularOrderedLabel {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℤ)
    (s : Fin n → ℤˣ) (f : Fin (d + 1) → Fin n) : Prop :=
  ∀ v : Fin (d + 1) → ℤ, (∃ j, v j ≠ 0) →
    (∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * v j) →
    (∀ k : Fin d, ∑ j, A (f k.succ) j * v j = 0) →
    (A.submatrix (fun k : Fin d => f k.succ) Fin.succ).det ≠ 0 ∧
    (∀ i, i ∉ Set.range (fun k : Fin d => f k.succ) →
      0 < (s i : ℤ) * ∑ j, A i j * v j)

/-- Two-way feasible-cofactor transport. The old regularity interface is
    explicit; its actual source/product instances,
    common-chart and graph semantics are discharged. -/
theorem regular_cofactor_feasibility_iff {n d : ℕ}
    (A D : Matrix (Fin n) (Fin (d + 1)) ℤ) (f : Fin (d + 1) → Fin n)
    (s : Fin n → ℤˣ) (u : ℤˣ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hdet : (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det ≠ 0)
    (hreg : RegularOrderedLabel A s f) :
    let Z := fun j => u •
      (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).adjugate j 0
    ((∃ j, (Z j).coeff 0 ≠ 0) ∧
      (∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * (Z j).coeff 0)) ↔
      (∀ i, 0 ≤ (s i • rowPolynomial A D Z i).eval₂
        (Int.castRingHom ℚ) (commonParameter (d + 1) B)) := by
  dsimp only
  let Z := fun j => u •
    (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).adjugate j 0
  have hkernel : ∀ k : Fin d, rowPolynomial A D Z (f k.succ) = 0 := by
    intro k
    exact oriented_cofactor_equation A D f 0 hdet u k.succ (Fin.succ_ne_zero k)
  have hconst : ∀ k : Fin d, ∑ j, A (f k.succ) j * (Z j).coeff 0 = 0 := by
    intro k
    rw [← rowPolynomial_constant A D Z (f k.succ), hkernel k]
    simp
  obtain ⟨m, W, hf, hw, henv, hslack, _⟩ :=
    normalized_cofactor_envelopes A D f 0 (fun _ => 0) B hB ha hd
      (fun _ => by simpa using (show (0 : ℤ) ≤ B by omega)) hdet u
  have hm_of_nonzero (hc : ∃ j, (Z j).coeff 0 ≠ 0) : m = 0 :=
    common_power_zero_of_constant Z W m hf hc
  have hZW (hm : m = 0) : Z = W := by
    funext j
    simpa [hm] using hf j
  constructor
  · rintro ⟨hc, hfeas⟩
    have hr := hreg (fun j => (Z j).coeff 0) hc hfeas hconst
    have heq := hZW (hm_of_nonzero hc)
    let J := univ.image (fun k : Fin d => f k.succ)
    have hz : ∀ i ∈ J, rowPolynomial A D W i = 0 := by
      intro i hi
      obtain ⟨k, _, rfl⟩ := mem_image.mp hi
      rw [← heq]
      exact hkernel k
    have hs : ∀ i, i ∉ J → 0 < (s i : ℤ) * ∑ j, A i j * (W j).coeff 0 := by
      intro i hi
      rw [← heq]
      exact hr.2 i (by simpa [J] using hi)
    have hp := (kernel_strict_labels_persist A D W s J B hB (fun i => hslack i (s i)) hz hs).1
    simpa only [← heq] using hp
  · intro hfeas
    have ht := (commonParameter_bounds (d + 1) B (by omega)).1
    have hWfeas : ∀ i, 0 ≤ (s i • rowPolynomial A D W i).eval₂
        (Int.castRingHom ℚ) (commonParameter (d + 1) B) := by
      intro i
      have h := hfeas i
      rw [signed_factor A D Z W m hf i (s i)] at h
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
      exact nonneg_of_mul_nonneg_right h (pow_pos ht m)
    have hS := slackBound_nonnegative (d + 1) B (by omega)
    have hsize : (((d + 1) + 1 : ℕ) : ℤ) * slackBound (d + 1) B ≤
        commonMassBound (d + 1) B := by
      simp only [Nat.cast_add, Nat.cast_one, commonMassBound]
      nlinarith
    have hWold : ∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * (W j).coeff 0 := by
      intro i
      have h := common_constant_nonnegative (d + 1) B (by omega) _ _ _ hS
        (hslack i (s i)) hsize (hWfeas i)
      simpa only [Polynomial.coeff_smul, rowPolynomial_constant, Units.smul_def, smul_eq_mul] using h
    have hWactive : ∀ k : Fin d, ∑ j, A (f k.succ) j * (W j).coeff 0 = 0 := by
      intro k
      rw [← rowPolynomial_constant A D W (f k.succ),
        normalized_kernel_equation A D Z W m hf (f k.succ) (hkernel k)]
      simp
    have hr := hreg (fun j => (W j).coeff 0) hw hWold hWactive
    have hc : ∃ j, (Z j).coeff 0 ≠ 0 := by
      refine ⟨0, ?_⟩
      have he : ((linearMatrix (fun i j => A (f i) j)
          (fun i j => D (f i) j)).adjugate 0 0).coeff 0 ≠ 0 := by
        rw [cofactor_chart_constant]
        exact hr.1
      rcases Int.units_eq_one_or u with rfl | rfl <;>
        simpa [Z, Polynomial.coeff_smul, Units.smul_def] using he
    refine ⟨hc, ?_⟩
    have heq := hZW (hm_of_nonzero hc)
    change ∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * (Z j).coeff 0
    simpa only [heq] using hWold

#print axioms constant_linear_adjugate
#print axioms cofactor_chart_constant
#print axioms regular_cofactor_feasibility_iff
end
end ADKZPricing
