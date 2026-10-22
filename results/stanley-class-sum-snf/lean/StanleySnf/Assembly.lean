import StanleySnf.Core

/-!
# Assembly: linear algebra over `ℤ`
-/

namespace StanleySnf

namespace As

/-- A unimodular square matrix acts surjectively. -/
theorem mulVec_surjective_of_isUnit {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ)
    (hV : IsUnit V.det) : Function.Surjective V.mulVec := fun y =>
  ⟨V⁻¹.mulVec y, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hV, Matrix.one_mulVec]⟩

/-- Right multiplication by a matrix acting surjectively doesn't change the column space. -/
theorem range_mul_of_surjective {ι κ μ : Type} [Fintype κ] [Fintype μ]
    (P : Matrix ι κ ℤ) (Q : Matrix κ μ ℤ) (hQ : Function.Surjective Q.mulVec) :
    LinearMap.range (P * Q).mulVecLin = LinearMap.range P.mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hQ)

/-- If `g ∘ f = id`, then `M × ker g ≃ N` via `(x, k) ↦ f x + k`. -/
noncomputable def sumEquiv {R M N : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : ∀ x, g (f x) = x) :
    (M × LinearMap.ker g) ≃ₗ[R] N where
  toFun p := f p.1 + p.2
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
    abel
  map_smul' c p := by
    simp [smul_add]
  invFun v := (g v, ⟨v - f (g v), by simp [h]⟩)
  left_inv p := by
    obtain ⟨x, k, hk⟩ := p
    rw [LinearMap.mem_ker] at hk
    ext <;> simp [h, hk]
  right_inv v := by simp

theorem sumEquiv_apply {R M N : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : ∀ x, g (f x) = x)
    (p : M × LinearMap.ker g) : sumEquiv f g h p = f p.1 + p.2 := rfl

end As

/-- An integer square matrix that is anti-triangular (`V r s = 0` for `r + s > n - 1`)
with `±1` on the anti-diagonal is unimodular. -/
theorem antitriangular_isUnit_det {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ)
    (h0 : ∀ r s : Fin n, n - 1 < (r : ℕ) + s → V r s = 0)
    (h1 : ∀ r s : Fin n, (r : ℕ) + s = n - 1 → V r s = 1 ∨ V r s = -1) :
    IsUnit V.det := by
  set V' := V.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) with hV'
  have hdet : V'.det = Equiv.Perm.sign Fin.revPerm * V.det := Matrix.det_permute' _ _
  have htri : V'.BlockTriangular id := by
    intro r s hsr
    simp only [hV', Matrix.submatrix_apply, id, Fin.revPerm_apply]
    apply h0
    simp only [Fin.val_rev]
    have := s.isLt
    have : (s : ℕ) < r := hsr
    omega
  have hV'u : IsUnit V'.det := by
    rw [Matrix.det_of_upperTriangular htri, IsUnit.prod_univ_iff]
    intro r
    simp only [hV', Matrix.submatrix_apply, id, Fin.revPerm_apply]
    have := r.isLt
    rcases h1 r r.rev (by simp only [Fin.val_rev]; omega) with h | h <;> rw [h] <;> simp
  rw [hdet] at hV'u
  exact isUnit_of_mul_isUnit_right hV'u

/-- The column space of `E X diag(D) V α`, with `E` an involution, `W X = 1`, `V`
unimodular and `α` surjective, is spanned by `D r • b (inl r)` for a basis `b` of `ℤ^ι`. -/
theorem range_of_factor {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A E : Matrix ι ι ℤ) (hE : E * E = 1)
    (X : Matrix ι (Fin n) ℤ) (W : Matrix (Fin n) ι ℤ) (hWX : W * X = 1)
    (D : Fin n → ℤ) (V : Matrix (Fin n) (Fin n) ℤ) (hV : IsUnit V.det)
    (α : Matrix (Fin n) ι ℤ) (hα : Function.Surjective α.mulVec)
    (hA : A = E * X * Matrix.diagonal D * V * α) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis (Fin n ⊕ κ) ℤ (ι → ℤ)),
      LinearMap.range A.mulVecLin =
        Submodule.span ℤ (Set.range fun r : Fin n => D r • b (Sum.inl r)) := by
  classical
  set B := E * X with hB
  have hLB : (W * E) * B = 1 := by
    rw [hB, Matrix.mul_assoc, ← Matrix.mul_assoc E E X, hE, Matrix.one_mul, hWX]
  have hgf : ∀ x, (W * E).mulVecLin (B.mulVecLin x) = x := by
    intro x
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hLB, Matrix.one_mulVec]
  obtain ⟨m, bK⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) (LinearMap.ker (W * E).mulVecLin)
  let b := ((Pi.basisFun ℤ (Fin n)).prod bK).map (As.sumEquiv _ _ hgf)
  refine ⟨Fin m, inferInstance, b, ?_⟩
  have hb : ∀ r, b (Sum.inl r) = B.col r := by
    intro r
    simp only [b, Module.Basis.map_apply, As.sumEquiv_apply, Module.Basis.prod_apply_inl_fst,
      Module.Basis.prod_apply_inl_snd, Pi.basisFun_apply, ZeroMemClass.coe_zero, add_zero,
      Matrix.mulVecLin_apply]
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.col]
  have hVα : Function.Surjective (V * α).mulVec := by
    intro y
    obtain ⟨z, hz⟩ := As.mulVec_surjective_of_isUnit V hV y
    obtain ⟨x, hx⟩ := hα z
    exact ⟨x, by rw [← Matrix.mulVec_mulVec, hx, hz]⟩
  rw [hA, Matrix.mul_assoc _ V α, As.range_mul_of_surjective _ _ hVα, Matrix.range_mulVecLin]
  congr 1
  ext v
  simp only [Set.mem_range]
  refine exists_congr fun r => ?_
  rw [hb]
  have hcol : (B * Matrix.diagonal D).col r = D r • B.col r := by
    ext i
    simp only [Matrix.col_apply, Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hcol, eq_comm]
