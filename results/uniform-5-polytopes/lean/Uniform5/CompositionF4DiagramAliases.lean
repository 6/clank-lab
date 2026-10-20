import Uniform5.CompositionWythoffConjugacy

/-! Three F4 aliases from the explicit orthogonal reversal of its diagram. -/
noncomputable section
namespace Uniform5.Composition
open scoped RealInnerProductSpace

/-- Two independent 45-degree reflected coordinate pairs. -/
noncomputable def f4ReversalLinear : ModelSpace 4 →ₗ[ℝ] ModelSpace 4 where
  toFun x := fun i => (![x 0 + x 1, x 0 - x 1, x 2 + x (⟨3, by decide⟩ : Fin 4), x 2 - x (⟨3, by decide⟩ : Fin 4)] i) / Real.sqrt 2
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem f4ReversalLinear_involutive : Function.Involutive f4ReversalLinear := by
  intro x
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext i
  fin_cases i <;> simp [f4ReversalLinear] <;> field_simp

theorem f4ReversalLinear_norm (x : ModelSpace 4) : ‖f4ReversalLinear x‖ = ‖x‖ := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp [f4ReversalLinear, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ]
  field_simp
  nlinarith

noncomputable def f4Reversal : ModelSpace 4 ≃ₗᵢ[ℝ] ModelSpace 4 :=
  { toLinearEquiv :=
      { toLinearMap := f4ReversalLinear
        invFun := f4ReversalLinear
        left_inv := f4ReversalLinear_involutive
        right_inv := f4ReversalLinear_involutive }
    norm_map' := f4ReversalLinear_norm }

noncomputable def f4ReversalScale (i : Fin 4) : ℝ :=
  if i.val < 2 then Real.sqrt 2 else 1 / Real.sqrt 2

theorem f4ReversalScale_pos (i : Fin 4) : 0 < f4ReversalScale i := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold f4ReversalScale
  split_ifs <;> positivity

theorem f4Reversal_roots (i : Fin 4) :
    f4Reversal (rootsF4 i) = f4ReversalScale i • rootsF4 i.rev := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [f4Reversal, f4ReversalLinear, f4ReversalScale, rootsF4,
      coordinateVector, EuclideanSpace.single_apply, Fin.rev, Fin.isValue, Fin.mk.injEq, Fin.succ] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat'] <;>
    (try field_simp)

variable {E : Type*} [PseudoMetricSpace E]

theorem f4_named_reversal {m n : Fin 15}
    (hmn : (libraryRingSet m).image (Fin.revPerm : Equiv.Perm (Fin 4)) = libraryRingSet n)
    {P : Set E} (hP : NamedWythoff4Model 3 m P) : NamedWythoff4Model 3 n P := by
  obtain ⟨x, hseed, hcongr⟩ := hP
  have hs := wythoffSeed_conjugacy rootsF4 rootsF4 f4Reversal Fin.revPerm
    f4ReversalScale f4ReversalScale_pos f4Reversal_roots hseed
  rw [hmn] at hs
  refine ⟨f4Reversal x, hs, ?_⟩
  apply congruent_trans hcongr
  have he := wythoffHull_conjugacy rootsF4 rootsF4 f4Reversal Fin.revPerm
    f4ReversalScale (fun i => ne_of_gt (f4ReversalScale_pos i)) f4Reversal_roots x
  rw [← he]
  exact congruent_affineIsometry_image f4Reversal.toAffineIsometryEquiv.toAffineIsometry _

noncomputable def f4AliasPairs : List (Fin 15 × Fin 15) := [(9, 4), (13, 6), (12, 10)]

theorem f4AliasPairs_table :
    f4AliasPairs.map (fun p => (FacetLibraryName.wythoff 3 p.1,
      FacetLibraryName.wythoff 3 p.2)) = (facetAliasTable.drop 29).take 3 := by decide

theorem f4_aliases_geometric {m n : Fin 15} (hmn : (m, n) ∈ f4AliasPairs)
    (P : Set E) : FacetLibraryModel (.wythoff 3 m) P ↔ FacetLibraryModel (.wythoff 3 n) P := by
  have hfor : (libraryRingSet m).image (Fin.revPerm : Equiv.Perm (Fin 4)) = libraryRingSet n := by
    revert m n
    decide
  have hback : (libraryRingSet n).image (Fin.revPerm : Equiv.Perm (Fin 4)) = libraryRingSet m := by
    revert m n
    decide
  exact ⟨f4_named_reversal hfor, f4_named_reversal hback⟩

end Uniform5.Composition
