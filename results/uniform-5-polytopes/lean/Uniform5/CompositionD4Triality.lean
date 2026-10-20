import Uniform5.CompositionD4B4Orbit

/-! The two explicit orthogonal symmetries generating D4 triality, acting
on actual signed seeds and reflection hulls. -/
noncomputable section
namespace Uniform5.Composition
open scoped RealInnerProductSpace

/-- The rational Hadamard involution exchanges outer nodes zero and three. -/
noncomputable def d4TrialityLinear : ModelSpace 4 →ₗ[ℝ] ModelSpace 4 where
  toFun x := fun i => (![x 0 + x 1 + x 2 + x (⟨3, by decide⟩ : Fin 4),
    x 0 + x 1 - x 2 - x (⟨3, by decide⟩ : Fin 4),
    x 0 - x 1 + x 2 - x (⟨3, by decide⟩ : Fin 4),
    x 0 - x 1 - x 2 + x (⟨3, by decide⟩ : Fin 4)] i) / 2
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem d4TrialityLinear_involutive : Function.Involutive d4TrialityLinear := by
  intro x
  ext i
  fin_cases i <;> simp [d4TrialityLinear] <;> ring

theorem d4TrialityLinear_norm (x : ModelSpace 4) : ‖d4TrialityLinear x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp [d4TrialityLinear, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_succ]
  ring

noncomputable def d4Triality : ModelSpace 4 ≃ₗᵢ[ℝ] ModelSpace 4 :=
  { toLinearEquiv :=
      { toLinearMap := d4TrialityLinear
        invFun := d4TrialityLinear
        left_inv := d4TrialityLinear_involutive
        right_inv := d4TrialityLinear_involutive }
    norm_map' := d4TrialityLinear_norm }

theorem d4Triality_roots (i : Fin 4) :
    d4Triality (rootsD4 i) = rootsD4 (Equiv.swap (⟨0, by decide⟩ : Fin 4) ⟨3, by decide⟩ i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [d4Triality, d4TrialityLinear, rootsD4,
      coordinateVector, EuclideanSpace.single_apply, Equiv.swap_apply_def,
      Fin.isValue, Fin.mk.injEq, Fin.succ] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat']

/-- Changing the last coordinate's sign exchanges the two fork nodes. -/
noncomputable def d4ForkSwap : ModelSpace 4 ≃ₗᵢ[ℝ] ModelSpace 4 :=
  mirrorReflection (rootsB4 (⟨3, by decide⟩ : Fin 4))

theorem d4ForkSwap_roots (i : Fin 4) :
    d4ForkSwap (rootsD4 i) = rootsD4 (Equiv.swap (⟨2, by decide⟩ : Fin 4) ⟨3, by decide⟩ i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [d4ForkSwap, b4_reflection_coordinates, rootsD4,
      coordinateVector, EuclideanSpace.single_apply, Equiv.swap_apply_def,
      Fin.isValue, Fin.mk.injEq, Fin.succ] <;>
    simp only [Fin.ext_iff] <;> norm_num [Fin.instOfNat, Fin.ofNat']

variable {E : Type*} [PseudoMetricSpace E]

theorem d4_named_symmetry (e : ModelSpace 4 ≃ₗᵢ[ℝ] ModelSpace 4)
    (π : Equiv.Perm (Fin 4)) (hr : ∀ i, e (rootsD4 i) = rootsD4 (π i))
    {m n : Fin 15} (hmn : (libraryRingSet m).image π = libraryRingSet n)
    {P : Set E} (hP : NamedWythoff4Model 2 m P) : NamedWythoff4Model 2 n P := by
  obtain ⟨x, hseed, hcongr⟩ := hP
  have hroot (i : Fin 4) : e (rootsD4 i) = (1 : ℝ) • rootsD4 (π i) := by simpa using hr i
  have hs := wythoffSeed_conjugacy rootsD4 rootsD4 e π
    (fun _ => 1) (fun _ => zero_lt_one) hroot hseed
  rw [hmn] at hs
  refine ⟨e x, hs, ?_⟩
  apply congruent_trans hcongr
  have he := wythoffHull_conjugacy rootsD4 rootsD4 e π
    (fun _ => 1) (fun _ => one_ne_zero) hroot x
  rw [← he]
  exact congruent_affineIsometry_image e.toAffineIsometryEquiv.toAffineIsometry _

theorem d4_named_symmetry_iff (e : ModelSpace 4 ≃ₗᵢ[ℝ] ModelSpace 4)
    (π : Equiv.Perm (Fin 4)) (hr : ∀ i, e (rootsD4 i) = rootsD4 (π i))
    {m n : Fin 15} (hmn : (libraryRingSet m).image π = libraryRingSet n)
    (P : Set E) : NamedWythoff4Model 2 m P ↔ NamedWythoff4Model 2 n P := by
  refine ⟨d4_named_symmetry e π hr hmn, ?_⟩
  apply d4_named_symmetry e.symm π.symm
  · intro i
    apply e.injective
    simp only [e.apply_symm_apply, hr, π.apply_symm_apply]
  · rw [← hmn, Finset.image_image]
    simp

theorem d4ForkTriality_roots (i : Fin 4) :
    (d4ForkSwap.trans d4Triality) (rootsD4 i) =
      rootsD4 ((Equiv.swap (2 : Fin 4) 3).trans (Equiv.swap 0 3) i) := by
  change d4Triality (d4ForkSwap (rootsD4 i)) = _
  rw [d4ForkSwap_roots, d4Triality_roots]
  rfl

end Uniform5.Composition
