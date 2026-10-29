import KernelAssembly

/- Algebraic label transport. Source/product regularity and edge transport
   are separate obligations, not conclusions of this file. -/
namespace ADKZPricing
open Polynomial Finset Matrix
noncomputable section

theorem signed_factor {n r : ℕ} (A D : Matrix (Fin n) (Fin r) ℤ)
    (Z W : Fin r → Polynomial ℤ) (m : ℕ)
    (hf : ∀ j, Z j = X ^ m * W j) (i : Fin n) (s : ℤˣ) :
    s • rowPolynomial A D Z i = X ^ m * (s • rowPolynomial A D W i) := by
  rw [rowPolynomial_factor A D Z W m hf i]
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

/-- A feasible specialized cofactor yields a nonzero old feasible integer
    vector annihilating every designated label, even for singular old labels. -/
theorem cofactor_feasible_old_label {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (f : Fin r → Fin n) (b : Fin r)
    (B : ℤ) (hB : 1 ≤ B) (ha : ∀ i j, |A i j| ≤ B) (hd : ∀ i j, |D i j| ≤ B)
    (hdet : (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).det ≠ 0)
    (u : ℤˣ) (s : Fin n → ℤˣ)
    (hfeas : ∀ i, 0 ≤ (s i • rowPolynomial A D (fun j => u •
      (linearMatrix (fun i j => A (f i) j) (fun i j => D (f i) j)).adjugate j b) i).eval₂ (Int.castRingHom ℚ) (commonParameter r B)) :
    ∃ v : Fin r → ℤ, (∃ j, v j ≠ 0) ∧
      (∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * v j) ∧
      (∀ i, i ≠ b → ∑ j, A (f i) j * v j = 0) := by
  obtain ⟨m, W, hf, hw, _, hk, hs, _⟩ :=
    normalized_cofactor_specialization A D f b (fun _ => 0) B hB ha hd
      (fun _ => by simpa using (show (0 : ℤ) ≤ B by omega)) hdet u
  refine ⟨fun j => (W j).coeff 0, hw, ?_, ?_⟩
  · intro i
    apply hs i (s i)
    have h := hfeas i
    rw [signed_factor A D _ W m hf i (s i)] at h
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
    exact nonneg_of_mul_nonneg_right h (pow_pos (commonParameter_bounds r B (by omega)).1 m)
  · intro i hi
    rw [← rowPolynomial_constant A D W (f i), hk i hi]
    simp

/-- Finite-cardinality step of no-new-label completeness. The explicit
    regularity premise still needs source/product instantiation. -/
theorem exact_labels_of_regular_limit {n r d : ℕ}
    (A : Matrix (Fin n) (Fin r) ℤ) (s : Fin n → ℤˣ) (J : Finset (Fin n))
    (hcard : J.card = d)
    (hregular : ∀ v : Fin r → ℤ, (∃ j, v j ≠ 0) →
      (∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * v j) →
      d ≤ (univ.filter (fun i => ∑ j, A i j * v j = 0)).card →
      (univ.filter (fun i => ∑ j, A i j * v j = 0)).card = d)
    (v : Fin r → ℤ) (hne : ∃ j, v j ≠ 0)
    (hfeas : ∀ i, 0 ≤ (s i : ℤ) * ∑ j, A i j * v j)
    (hzero : ∀ i ∈ J, ∑ j, A i j * v j = 0) :
    ∀ i, (∑ j, A i j * v j = 0) ↔ i ∈ J := by
  classical
  let T := univ.filter (fun i => ∑ j, A i j * v j = 0)
  have hsub : J ⊆ T := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, hzero i hi⟩
  have hcount : T.card = d := hregular v hne hfeas (by
    rw [← hcard]
    exact card_le_card hsub)
  have heq : J = T := eq_of_subset_of_card_le hsub (by omega)
  intro i
  rw [heq]
  simp [T]

/-- Old strict signed slacks persist at the parameter already used for
    every minor. All designated active labels stay identically zero. -/
theorem kernel_strict_labels_persist {n r : ℕ}
    (A D : Matrix (Fin n) (Fin r) ℤ) (W : Fin r → Polynomial ℤ)
    (s : Fin n → ℤˣ) (J : Finset (Fin n)) (B : ℤ) (hB : 1 ≤ B)
    (henv : ∀ i, CoeffEnvelope (s i • rowPolynomial A D W i) (r + 1) (slackBound r B))
    (hzero : ∀ i ∈ J, rowPolynomial A D W i = 0)
    (hstrict : ∀ i, i ∉ J → 0 < (s i : ℤ) * ∑ j, A i j * (W j).coeff 0) :
    (∀ i, 0 ≤ (s i • rowPolynomial A D W i).eval₂
      (Int.castRingHom ℚ) (commonParameter r B)) ∧
    (∀ i, (s i • rowPolynomial A D W i).eval₂
      (Int.castRingHom ℚ) (commonParameter r B) = 0 ↔ i ∈ J) := by
  have hS := slackBound_nonnegative r B (by omega)
  have hsize : ((r + 1 : ℕ) : ℤ) * slackBound r B ≤ commonMassBound r B := by
    simp only [Nat.cast_add, Nat.cast_one, commonMassBound]
    nlinarith
  have hp (i : Fin n) (hi : i ∉ J) : 0 < (s i • rowPolynomial A D W i).eval₂
      (Int.castRingHom ℚ) (commonParameter r B) := by
    apply common_positive_eval r B (by omega) _ (r + 1) _ hS (henv i) hsize
    simpa only [Polynomial.coeff_smul, rowPolynomial_constant, Units.smul_def, smul_eq_mul]
      using hstrict i hi
  have hz (i : Fin n) (hi : i ∈ J) : (s i • rowPolynomial A D W i).eval₂
      (Int.castRingHom ℚ) (commonParameter r B) = 0 := by simp [hzero i hi]
  constructor
  · intro i
    by_cases hi : i ∈ J
    · rw [hz i hi]
    · exact (hp i hi).le
  · intro i
    constructor
    · intro he
      by_contra hi
      exact (hp i hi).ne' he
    · exact hz i

/-- Rank-to-cofactor transport is separate from this normalization fact. -/
theorem common_power_zero_of_constant {r : ℕ}
    (Z W : Fin r → Polynomial ℤ) (m : ℕ)
    (hf : ∀ j, Z j = X ^ m * W j) (hc : ∃ j, (Z j).coeff 0 ≠ 0) : m = 0 := by
  obtain ⟨j, hj⟩ := hc
  by_contra hm
  rw [hf j, Polynomial.coeff_X_pow_mul'] at hj
  simp [hm] at hj

/-- A nonsingular completion makes the common kernel of all other rows
    one-dimensional. This statement is independent of a cell sign vector. -/
theorem completed_kernel_proportional {𝕜 : Type*} [Field 𝕜] {r : ℕ}
    (K : Matrix (Fin r) (Fin r) 𝕜) (b : Fin r) (hK : K.det ≠ 0)
    (v w : Fin r → 𝕜)
    (hv : ∀ i, i ≠ b → K.mulVec v i = 0)
    (hw : ∀ i, i ≠ b → K.mulVec w i = 0) :
    K.mulVec v b • w = K.mulVec w b • v := by
  have hk : IsUnit K := (Matrix.isUnit_iff_isUnit_det K).mpr (isUnit_iff_ne_zero.mpr hK)
  apply Matrix.mulVec_injective_iff_isUnit.mpr hk
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  ext i
  by_cases hi : i = b
  · subst i
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
  · simp [hv i hi, hw i hi]

/-- Identical original row labels and the same chart give IDENTICAL
    normalized rays across cells, rather than unrelated isomorphisms. -/
theorem shared_label_chart_unique {𝕜 : Type*} [Field 𝕜] {r : ℕ}
    (K : Matrix (Fin r) (Fin r) 𝕜) (b : Fin r) (hK : K.det ≠ 0)
    (v w h : Fin r → 𝕜)
    (hv : ∀ i, i ≠ b → K.mulVec v i = 0)
    (hw : ∀ i, i ≠ b → K.mulVec w i = 0)
    (hcv : h ⬝ᵥ v = 1) (hcw : h ⬝ᵥ w = 1) : v = w := by
  have hp := completed_kernel_proportional K b hK v w hv hw
  have hn : K.mulVec v b ≠ 0 := by
    intro hz
    have hk : IsUnit K := (Matrix.isUnit_iff_isUnit_det K).mpr (isUnit_iff_ne_zero.mpr hK)
    have hzv : K.mulVec v = 0 := by
      ext i
      by_cases hi : i = b
      · subst i; exact hz
      · exact hv i hi
    have hv0 : v = 0 := Matrix.mulVec_injective_iff_isUnit.mpr hk (by simpa using hzv)
    rw [hv0, dotProduct_zero] at hcv
    exact zero_ne_one hcv
  have he := congrArg (fun x => h ⬝ᵥ x) hp
  simp only [dotProduct_smul, hcv, hcw, smul_eq_mul, mul_one] at he
  rw [← he] at hp
  ext j
  have hj := congrArg (fun x : Fin r → 𝕜 => x j) hp
  exact (mul_left_cancel₀ hn hj).symm

theorem kernel_zero_of_chart_zero {𝕜 : Type*} [Field 𝕜] {r : ℕ}
    (K : Matrix (Fin r) (Fin r) 𝕜) (b : Fin r) (hK : K.det ≠ 0)
    (v w h : Fin r → 𝕜)
    (hv : ∀ i, i ≠ b → K.mulVec v i = 0)
    (hw : ∀ i, i ≠ b → K.mulVec w i = 0)
    (hcv : h ⬝ᵥ v = 1) (hcw : h ⬝ᵥ w = 0) : w = 0 := by
  have hsum : ∀ i, i ≠ b → K.mulVec (v + w) i = 0 := by
    intro i hi
    simp [Matrix.mulVec_add, hv i hi, hw i hi]
  have heq := shared_label_chart_unique K b hK v (v + w) h hv hsum hcv
    (by rw [dotProduct_add, hcv, hcw, add_zero])
  ext j
  have hj := congrArg (fun x : Fin r → 𝕜 => x j) heq
  change w j = 0
  change v j = v j + w j at hj
  exact (add_eq_left.mp hj.symm)

/-- In a charted one-dimensional kernel, the selected active spatial
    rows are independent. This closes the homogeneous-to-affine rank
    step once a nonsingular completion is supplied by uniformity. -/
theorem charted_spatial_minor {𝕜 : Type*} [Field 𝕜] {d : ℕ}
    (K : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜) (hK : K.det ≠ 0)
    (v : Fin (d + 1) → 𝕜) (hv : v 0 = 1)
    (hk : ∀ i : Fin d, K.mulVec v i.succ = 0) :
    (K.submatrix Fin.succ Fin.succ).det ≠ 0 := by
  have hinj : Function.Injective (K.submatrix Fin.succ Fin.succ).mulVec := by
    intro x y hxy
    let w : Fin (d + 1) → 𝕜 := Fin.cons 0 (x - y)
    have hw : ∀ i, i ≠ 0 → K.mulVec w i = 0 := by
      intro i hi
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
      have hj := congrArg (fun z : Fin d → 𝕜 => z j) hxy
      change (K.submatrix Fin.succ Fin.succ).mulVec x j =
        (K.submatrix Fin.succ Fin.succ).mulVec y j at hj
      have hz : (K.submatrix Fin.succ Fin.succ).mulVec (x - y) j = 0 := by
        simp only [Matrix.mulVec_sub, Pi.sub_apply, hj, sub_self]
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, w, Matrix.submatrix] using hz
    have hkv : ∀ i, i ≠ 0 → K.mulVec v i = 0 := by
      intro i hi
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
      exact hk j
    have hz := kernel_zero_of_chart_zero K 0 hK v w (Pi.single 0 1) hkv hw
      (by simpa using hv) (by simp [w])
    ext j
    have hj := congrArg (fun z : Fin (d + 1) → 𝕜 => z j.succ) hz
    simpa [w, sub_eq_zero] using hj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

#print axioms kernel_zero_of_chart_zero
#print axioms charted_spatial_minor
#print axioms completed_kernel_proportional
#print axioms shared_label_chart_unique
#print axioms cofactor_feasible_old_label
#print axioms exact_labels_of_regular_limit
#print axioms kernel_strict_labels_persist
#print axioms common_power_zero_of_constant
end
end ADKZPricing
