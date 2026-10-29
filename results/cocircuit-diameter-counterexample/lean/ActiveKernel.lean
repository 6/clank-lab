import KernelRayTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜]

/-- A nonsingular active spatial basis fixes the entire homogeneous ray,
    even when the extra completion row is singular before perturbation. -/
theorem active_kernel_proportional {d : ℕ}
    (K : Matrix (Fin d) (Fin (d + 1)) 𝕜)
    (hd : (K.submatrix id Fin.succ).det ≠ 0)
    (v w : Fin (d + 1) → 𝕜) (hv : K *ᵥ v = 0) (hw : K *ᵥ w = 0)
    (hw0 : w 0 ≠ 0) : v = (v 0 / w 0) • w := by
  let z := v - (v 0 / w 0) • w
  have hz0 : z 0 = 0 := by simp [z, hw0]
  have hzk : K *ᵥ z = 0 := by
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, hv, hw, smul_zero, sub_self]
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  have htail : (fun j : Fin d => z j.succ) = 0 := by
    apply hinj
    ext i
    have he := congrFun hzk i
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hz0, mul_zero,
      zero_add, Matrix.submatrix, Matrix.of_apply, id_eq, Matrix.mulVec_zero, Pi.zero_apply,
      sum_const_zero] using he
  have hz : z = 0 := by
    ext i
    refine Fin.cases hz0 (fun j => congrFun htail j) i
  exact sub_eq_zero.mp hz

def cofactorRay {d : ℕ} (K : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜) : Fin (d + 1) → 𝕜 :=
  fun j => K.adjugate j 0

theorem cofactorRay_image {d : ℕ} (K : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜) :
    K *ᵥ cofactorRay K = fun i => if i = 0 then K.det else 0 := by
  ext i
  change (K * K.adjugate) i 0 = _
  rw [Matrix.mul_adjugate]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem cofactorRay_tail {d : ℕ} (K : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜) :
    (K.submatrix Fin.succ id) *ᵥ cofactorRay K = 0 := by
  ext i
  have he := congrFun (cofactorRay_image K) i.succ
  simpa only [Fin.succ_ne_zero, ↓reduceIte] using he

theorem cofactorRay_chart {d : ℕ} (K : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜) :
    cofactorRay K 0 = (K.submatrix Fin.succ Fin.succ).det := by
  simp [cofactorRay, Matrix.adjugate_fin_succ_eq_det_submatrix]

theorem full_kernel_cofactor {d : ℕ} (K : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜)
    (hd : K.det ≠ 0) (v : Fin (d + 1) → 𝕜)
    (hv : ∀ i : Fin d, (K *ᵥ v) i.succ = 0) :
    v = ((K *ᵥ v) 0 / K.det) • cofactorRay K := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  rw [Matrix.mulVec_smul, cofactorRay_image]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hd]
  · simp [hv j]

theorem full_kernel_cofactor_chart_nonzero {d : ℕ}
    (K : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜)
    (hd : K.det ≠ 0) (v : Fin (d + 1) → 𝕜) (h0 : v 0 ≠ 0)
    (hv : ∀ i : Fin d, (K *ᵥ v) i.succ = 0) : cofactorRay K 0 ≠ 0 := by
  have he := congrFun (full_kernel_cofactor K hd v hv) 0
  intro hz
  apply h0
  simpa [hz] using he

/-- The only orientation choice is ±1. It is shared by the full vector,
    so no cell gets a different label-specific orientation convention. -/
theorem nonzero_scalar_orientation [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (t : 𝕜) (ht : t ≠ 0) :
    ∃ u : ℤˣ, ∃ a : 𝕜, 0 < a ∧ t = a * (u : ℤ) := by
  by_cases hp : 0 < t
  · exact ⟨1, t, hp, by simp⟩
  · refine ⟨-1, -t, neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) ht), ?_⟩
    simp

#print axioms active_kernel_proportional
#print axioms full_kernel_cofactor
#print axioms nonzero_scalar_orientation
end
end ADKZPricing
