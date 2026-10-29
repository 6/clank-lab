import PolynomialRay

namespace ADKZPricing
open Matrix Polynomial Finset
noncomputable section

/-- A feasible actual specialized ray on the original active labels
    supplies an oriented polynomial cofactor. The checked coefficient
    theorem then recovers an actual nonzero old integer ray, with every
    inactive signed slack strict. No abstract graph is substituted. -/
theorem specialized_ray_has_old_label {n d : ℕ}
    (A D : Matrix (Fin n) (Fin (d + 1)) ℤ) (f : Fin (d + 1) → Fin n)
    (s : Fin n → ℤˣ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hpoly : (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det ≠ 0)
    (hreg : RegularOrderedLabel A s f)
    (hnew : ((specializedMatrix A D (commonParameter (d + 1) B)).submatrix f id).det ≠ 0)
    (v : Fin (d + 1) → ℚ) (hv : v ≠ 0)
    (hfeas : ∀ i, 0 ≤ (s i : ℤ) *
      (specializedMatrix A D (commonParameter (d + 1) B) i ⬝ᵥ v))
    (hactive : ∀ j : Fin d,
      specializedMatrix A D (commonParameter (d + 1) B) (f j.succ) ⬝ᵥ v = 0) :
    ∃ w : Fin (d + 1) → ℤ, (∃ j, w j ≠ 0) ∧
      (∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * w j) ∧
      (∀ j : Fin d, ∑ k, A (f j.succ) k * w k = 0) ∧
      (∀ i, i ∉ Set.range (fun j : Fin d => f j.succ) →
        0 < (s i : ℤ) * ∑ j, A i j * w j) := by
  let t := commonParameter (d + 1) B
  let K := (specializedMatrix A D t).submatrix f id
  let b := (K *ᵥ v) 0 / K.det
  have hvcof : v = b • cofactorRay K := full_kernel_cofactor K hnew v hactive
  have hb : b ≠ 0 := by
    intro hz
    apply hv
    rw [hvcof, hz, zero_smul]
  obtain ⟨u, a, ha0, hba⟩ := nonzero_scalar_orientation b hb
  let Z := fun j => u •
    (linearMatrix (fun i k => A (f i) k) (fun i k => D (f i) k)).adjugate j 0
  let z : Fin (d + 1) → ℚ := fun j => (Z j).eval₂ (Int.castRingHom ℚ) t
  have hze (j : Fin (d + 1)) : z j = (u : ℤ) * cofactorRay K j :=
    oriented_adjugate_eval A D f t u j
  have hvz : v = a • z := by
    rw [hvcof, hba]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, hze]
    ring
  have heval : ∀ i, 0 ≤ (s i • rowPolynomial A D Z i).eval₂ (Int.castRingHom ℚ) t := by
    intro i
    rw [signed_rowPolynomial_evaluation]
    have he := hfeas i
    rw [hvz, dotProduct_smul] at he
    change 0 ≤ (s i : ℤ) * (a * (specializedMatrix A D t i ⬝ᵥ z)) at he
    rw [mul_left_comm] at he
    exact nonneg_of_mul_nonneg_right he ha0
  have hold := (regular_cofactor_feasibility_iff A D f s u B hB ha hd hpoly hreg).mpr heval
  have hzactive : ∀ j : Fin d, ∑ k, A (f j.succ) k * (Z k).coeff 0 = 0 := by
    intro j
    rw [← rowPolynomial_constant A D Z (f j.succ),
      oriented_cofactor_equation A D f 0 hpoly u j.succ (Fin.succ_ne_zero j)]
    simp
  exact ⟨fun j => (Z j).coeff 0, hold.1, hold.2, hzactive,
    (hreg (fun j => (Z j).coeff 0) hold.1 hold.2 hzactive).2⟩

/-- Reverse label existence: an old feasible integer ray supplies a
    feasible nonzero specialized rational ray on the SAME active rows. -/
theorem old_ray_has_specialized_label {n d : ℕ}
    (A D : Matrix (Fin n) (Fin (d + 1)) ℤ) (f : Fin (d + 1) → Fin n)
    (s : Fin n → ℤˣ) (B : ℤ) (hB : 1 ≤ B)
    (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hpoly : (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det ≠ 0)
    (hreg : RegularOrderedLabel A s f)
    (hnew : ((specializedMatrix A D (commonParameter (d + 1) B)).submatrix f id).det ≠ 0)
    (v : Fin (d + 1) → ℤ) (hv : ∃ j, v j ≠ 0)
    (hfeas : ∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * v j)
    (hactive : ∀ j : Fin d, ∑ k, A (f j.succ) k * v k = 0) :
    ∃ z : Fin (d + 1) → ℚ, z ≠ 0 ∧
      (∀ i, 0 ≤ (s i : ℤ) *
        (specializedMatrix A D (commonParameter (d + 1) B) i ⬝ᵥ z)) ∧
      (∀ j : Fin d,
        specializedMatrix A D (commonParameter (d + 1) B) (f j.succ) ⬝ᵥ z = 0) := by
  let t := commonParameter (d + 1) B
  let K := (A.map (Int.castRingHom ℚ)).submatrix f id
  let q : Fin (d + 1) → ℚ := fun j => (v j : ℚ)
  have hq : q ≠ 0 := by
    obtain ⟨j, hj⟩ := hv
    intro hz
    exact hj (Int.cast_eq_zero.mp (congrFun hz j))
  have hminor := (hreg v hv hfeas hactive).1
  have hm : (K.submatrix Fin.succ Fin.succ).det ≠ 0 := by
    have he := Int.cast_det (R := ℚ) (A.submatrix (fun j : Fin d => f j.succ) Fin.succ)
    change (((A.submatrix (fun j : Fin d => f j.succ) Fin.succ).det : ℤ) : ℚ) =
      (K.submatrix Fin.succ Fin.succ).det at he
    rw [← he]
    exact_mod_cast hminor
  have hqc : (K.submatrix Fin.succ id) *ᵥ q = 0 := by
    ext j
    change ∑ k, (A (f j.succ) k : ℚ) * (v k : ℚ) = 0
    exact_mod_cast hactive j
  have hw0 : cofactorRay K 0 ≠ 0 := by rw [cofactorRay_chart]; exact hm
  let b := q 0 / cofactorRay K 0
  have hqcof : q = b • cofactorRay K :=
    active_kernel_proportional (K.submatrix Fin.succ id) hm q _ hqc (cofactorRay_tail K) hw0
  have hb : b ≠ 0 := by
    intro hz
    apply hq
    rw [hqcof, hz, zero_smul]
  obtain ⟨u, a, ha0, hba⟩ := nonzero_scalar_orientation b hb
  let Z := fun j => u •
    (linearMatrix (fun i k => A (f i) k) (fun i k => D (f i) k)).adjugate j 0
  let w : Fin (d + 1) → ℤ := fun j => (Z j).coeff 0
  have hwe (j : Fin (d + 1)) : (w j : ℚ) = (u : ℤ) * cofactorRay K j :=
    oriented_adjugate_constant A D f u j
  have hqw : q = a • (fun j => (w j : ℚ)) := by
    rw [hqcof, hba]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, hwe]
    ring
  have hwn : ∃ j, w j ≠ 0 := by
    by_contra hz
    push_neg at hz
    apply hq
    rw [hqw]
    ext j
    simp [hz]
  have hwf : ∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * w j := by
    intro i
    have he : (0 : ℚ) ≤ (s i : ℤ) * ((A.map (Int.castRingHom ℚ)) i ⬝ᵥ q) := by
      change 0 ≤ (s i : ℤ) * ∑ j, (A i j : ℚ) * (v j : ℚ)
      exact_mod_cast hfeas i
    rw [hqw, dotProduct_smul] at he
    change 0 ≤ (s i : ℤ) * (a * ((A.map (Int.castRingHom ℚ)) i ⬝ᵥ (fun j => (w j : ℚ)))) at he
    rw [mul_left_comm] at he
    have hp := nonneg_of_mul_nonneg_right he ha0
    change 0 ≤ (s i : ℤ) * ∑ j, (A i j : ℚ) * (w j : ℚ) at hp
    exact_mod_cast hp
  have heval := (regular_cofactor_feasibility_iff A D f s u B hB ha hd hpoly hreg).mp ⟨hwn, hwf⟩
  let z : Fin (d + 1) → ℚ := fun j => (Z j).eval₂ (Int.castRingHom ℚ) t
  let N := (specializedMatrix A D t).submatrix f id
  have hze (j : Fin (d + 1)) : z j = (u : ℤ) * cofactorRay N j :=
    oriented_adjugate_eval A D f t u j
  have hz : z ≠ 0 := by
    intro hz0
    have hu : ((u : ℤ) : ℚ) ≠ 0 := by exact_mod_cast u.ne_zero
    have hc : cofactorRay N = 0 := by
      ext j
      have he := congrFun hz0 j
      rw [hze] at he
      exact (mul_eq_zero.mp he).resolve_left hu
    have he := congrFun (cofactorRay_image N) 0
    rw [hc, Matrix.mulVec_zero] at he
    exact hnew (by simpa using he.symm)
  refine ⟨z, hz, ?_, ?_⟩
  · intro i
    have he := heval i
    rw [signed_rowPolynomial_evaluation] at he
    exact he
  · intro j
    have he := congrArg (fun p : Polynomial ℤ => p.eval₂ (Int.castRingHom ℚ) t)
      (oriented_cofactor_equation A D f 0 hpoly u j.succ (Fin.succ_ne_zero j))
    change (rowPolynomial A D Z (f j.succ)).eval₂ (Int.castRingHom ℚ) t =
      (0 : Polynomial ℤ).eval₂ (Int.castRingHom ℚ) t at he
    rw [rowPolynomial_evaluation] at he
    simpa only [Polynomial.eval₂_zero] using he

#print axioms old_ray_has_specialized_label
#print axioms specialized_ray_has_old_label
end
end ADKZPricing
