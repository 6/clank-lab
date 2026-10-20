import Uniform5.CompositionLibraryNames

/-! Reflection words, hulls and signed mirror seeds under actual Euclidean
isometries. The A4 diagram reversal is implemented by negated coordinate
reversal, giving the six A4 aliases without a congruence premise. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Nonzero rescaling does not change a reflecting hyperplane. -/
theorem mirrorReflection_smul {c : ℝ} (hc : c ≠ 0) (a : E) :
    mirrorReflection (c • a) = mirrorReflection a := by
  unfold mirrorReflection
  simp only [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

theorem mirrorReflection_isometry (e : E ≃ₗᵢ[ℝ] F) (a x : E) :
    e (mirrorReflection a x) = mirrorReflection (e a) (e x) := by
  simp only [mirrorReflection_formula, map_sub, map_smul,
    e.inner_map_map, e.norm_map]

theorem reflectionWord_conjugacy {k : ℕ} (r : Fin k → E) (s : Fin k → F)
    (e : E ≃ₗᵢ[ℝ] F) (π : Equiv.Perm (Fin k)) (c : Fin k → ℝ)
    (hc : ∀ i, c i ≠ 0) (hroot : ∀ i, e (r i) = c i • s (π i))
    (w : List (Fin k)) (x : E) :
    e (reflectionWord r w x) = reflectionWord s (w.map π) (e x) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [reflectionWord, List.map_cons]
    rw [mirrorReflection_isometry, hroot, mirrorReflection_smul (hc i), ih]

theorem reflectionOrbit_conjugacy {k : ℕ} (r : Fin k → E) (s : Fin k → F)
    (e : E ≃ₗᵢ[ℝ] F) (π : Equiv.Perm (Fin k)) (c : Fin k → ℝ)
    (hc : ∀ i, c i ≠ 0) (hroot : ∀ i, e (r i) = c i • s (π i)) (x : E) :
    e '' reflectionOrbit r x = reflectionOrbit s (e x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    exact ⟨w.map π, (reflectionWord_conjugacy r s e π c hc hroot w x).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨reflectionWord r (w.map π.symm) x, ⟨_, rfl⟩, ?_⟩
    rw [reflectionWord_conjugacy r s e π c hc hroot]
    simp only [List.map_map, Function.comp_def, π.apply_symm_apply, List.map_id']

theorem wythoffHull_conjugacy {k : ℕ} (r : Fin k → E) (s : Fin k → F)
    (e : E ≃ₗᵢ[ℝ] F) (π : Equiv.Perm (Fin k)) (c : Fin k → ℝ)
    (hc : ∀ i, c i ≠ 0) (hroot : ∀ i, e (r i) = c i • s (π i)) (x : E) :
    e '' WythoffHull r x = WythoffHull s (e x) := by
  change e.toAffineIsometryEquiv.toAffineMap '' convexHull ℝ (reflectionOrbit r x) = _
  rw [e.toAffineIsometryEquiv.toAffineMap.image_convexHull]
  change convexHull ℝ (e '' reflectionOrbit r x) = _
  rw [reflectionOrbit_conjugacy r s e π c hc hroot]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Positive root scaling preserves the paper's signed distance equations. -/
theorem wythoffSeed_conjugacy {k : ℕ} (r : Fin k → E) (s : Fin k → F)
    (e : E ≃ₗᵢ[ℝ] F) (π : Equiv.Perm (Fin k)) (c : Fin k → ℝ)
    (hc : ∀ i, 0 < c i) (hroot : ∀ i, e (r i) = c i • s (π i))
    {J : Finset (Fin k)} {x : E} (hx : WythoffSeed r J x) :
    WythoffSeed s (J.image π) (e x) := by
  classical
  intro j
  obtain ⟨i, rfl⟩ := π.surjective j
  have hi := hx i
  have hn := e.norm_map (r i)
  rw [hroot, norm_smul, Real.norm_eq_abs, abs_of_pos (hc i)] at hn
  rw [← e.inner_map_map (r i) x, hroot, real_inner_smul_left] at hi
  have hmem : π i ∈ J.image π ↔ i ∈ J := by simp
  by_cases hJ : i ∈ J
  · simp only [if_pos hJ] at hi
    rw [if_pos (hmem.mpr hJ)]
    apply mul_left_cancel₀ (ne_of_gt (hc i))
    nlinarith
  · simp only [if_neg hJ] at hi
    rw [if_neg (fun h => hJ (hmem.mp h))]
    exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hc i))

/-- Negated reversal of the five coordinates preserves the A4 chamber
while reversing its four nodes. -/
noncomputable def a4Reversal : ModelSpace 5 ≃ₗᵢ[ℝ] ModelSpace 5 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fin.revPerm : Equiv.Perm (Fin 5))).trans
    (LinearIsometryEquiv.neg ℝ)

theorem a4Reversal_apply (x : ModelSpace 5) (i : Fin 5) :
    a4Reversal x i = -x i.rev := rfl

theorem a4Reversal_roots (i : Fin 4) : a4Reversal (rootsA4 i) = rootsA4 i.rev := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [a4Reversal_apply, rootsA4, coordinateVector,
      EuclideanSpace.single_apply, Fin.rev, Fin.succ]

theorem a4Reversal_sum_zero {x : ModelSpace 5} (hx : (∑ i, x i) = 0) :
    (∑ i, a4Reversal x i) = 0 := by
  simp only [a4Reversal_apply, Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin 5)) (fun i => x i)] at hx
  simpa only [Fin.revPerm_apply, neg_zero] using congrArg Neg.neg hx

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- All ring masks are reversed by an actual congruence of the orbit hull. -/
theorem a4_named_reversal {m n : Fin 15}
    (hmn : (libraryRingSet m).image (Fin.revPerm : Equiv.Perm (Fin 4)) = libraryRingSet n)
    {P : Set E} (hP : NamedWythoff4Model 0 m P) : NamedWythoff4Model 0 n P := by
  obtain ⟨x, hx, hseed, hcongr⟩ := hP
  have hr (i : Fin 4) : a4Reversal (rootsA4 i) = (1 : ℝ) • rootsA4 (Fin.revPerm i) := by
    simpa using a4Reversal_roots i
  have hs := wythoffSeed_conjugacy rootsA4 rootsA4 a4Reversal Fin.revPerm
    (fun _ => 1) (fun _ => zero_lt_one) hr hseed
  rw [hmn] at hs
  refine ⟨a4Reversal x, a4Reversal_sum_zero hx, hs, ?_⟩
  apply congruent_trans hcongr
  have he := wythoffHull_conjugacy rootsA4 rootsA4 a4Reversal Fin.revPerm
    (fun _ => 1) (fun _ => one_ne_zero) hr x
  rw [← he]
  exact congruent_affineIsometry_image a4Reversal.toAffineIsometryEquiv.toAffineIsometry _

/-- Precisely the six A4 pairs printed in the alias table. -/
noncomputable def a4AliasPairs : List (Fin 15 × Fin 15) :=
  [(7, 0), (3, 1), (11, 2), (9, 4), (13, 6), (12, 10)]

theorem a4AliasPairs_table :
    a4AliasPairs.map (fun p => (FacetLibraryName.wythoff 0 p.1,
      FacetLibraryName.wythoff 0 p.2)) = facetAliasTable.take 6 := by decide

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem a4_aliases_geometric {m n : Fin 15} (hmn : (m, n) ∈ a4AliasPairs)
    (P : Set E) : FacetLibraryModel (.wythoff 0 m) P ↔ FacetLibraryModel (.wythoff 0 n) P := by
  have hfor : (libraryRingSet m).image (Fin.revPerm : Equiv.Perm (Fin 4)) = libraryRingSet n := by
    revert m n
    decide
  have hback : (libraryRingSet n).image (Fin.revPerm : Equiv.Perm (Fin 4)) = libraryRingSet m := by
    revert m n
    decide
  exact ⟨a4_named_reversal hfor, a4_named_reversal hback⟩

end Uniform5.Composition
