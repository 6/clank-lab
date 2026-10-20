import Uniform5.CompositionCubeOrbits

/-! The three-antiprism is the unit B3 octahedron as a concrete convex hull. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped RealInnerProductSpace

noncomputable def octahedronAxis (i : Fin 3) : Space 3 :=
  (Real.sqrt 2 / 2) • coordinateVector i

noncomputable def octahedronPoint (p : Bool × Fin 3) : Space 3 :=
  if p.1 then -octahedronAxis p.2 else octahedronAxis p.2

noncomputable def octahedronSeed : Space 3 := octahedronAxis ⟨0, by decide⟩

theorem octahedronSeed_seed : WythoffSeed rootsB3 {0} octahedronSeed := by
  intro i
  rw [rootsB3_norm]
  fin_cases i <;> norm_num [octahedronSeed, octahedronAxis, rootsB3, coordinateVector,
    inner_sub_left, inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two]

noncomputable def b3AxisPerm (i : Fin 3) : Equiv.Perm (Fin 3) :=
  ![Equiv.swap (⟨0, by decide⟩ : Fin 3) ⟨1, by decide⟩,
    Equiv.swap (⟨1, by decide⟩ : Fin 3) ⟨2, by decide⟩, Equiv.refl _] i

theorem b3_reflection_octahedronPoint (i : Fin 3) (p : Bool × Fin 3) :
    mirrorReflection (rootsB3 i) (octahedronPoint p) =
      octahedronPoint (Bool.xor p.1 (decide (i = (⟨2, by decide⟩ : Fin 3) ∧ p.2 = (⟨2, by decide⟩ : Fin 3))), b3AxisPerm i p.2) := by
  rcases p with ⟨b, j⟩
  cases b <;> fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    norm_num [b3_reflection_coordinates, octahedronPoint, octahedronAxis, coordinateVector,
      b3AxisPerm, Equiv.swap_apply_def, EuclideanSpace.single_apply,
      Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two]

noncomputable def b3AxisWord : Fin 3 → List (Fin 3) :=
  ![[], [⟨0, by decide⟩], [⟨1, by decide⟩, ⟨0, by decide⟩]]

theorem b3AxisWord_apply (i : Fin 3) :
    reflectionWord rootsB3 (b3AxisWord i) octahedronSeed = octahedronAxis i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [b3AxisWord, reflectionWord, b3_reflection_coordinates, octahedronSeed,
      octahedronAxis, coordinateVector, EuclideanSpace.single_apply,
      Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two]

theorem octahedronAxis_neg_mem_orbit (i : Fin 3) :
    -octahedronAxis i ∈ reflectionOrbit rootsB3 octahedronSeed := by
  have hp : octahedronAxis i ∈ reflectionOrbit rootsB3 octahedronSeed := ⟨_, b3AxisWord_apply i⟩
  have hh := reflectionOrbit_word_closed rootsB3 hp (b3SignFlipWord i)
  have he : reflectionWord rootsB3 (b3SignFlipWord i) (octahedronAxis i) = -octahedronAxis i := by
    ext j
    rw [b3SignFlipWord_coordinates]
    by_cases h : j = i
    · simp [h]
    · simp [h, octahedronAxis, coordinateVector, EuclideanSpace.single_apply, Ne.symm h]
  rwa [he] at hh

theorem octahedronSeed_orbit :
    reflectionOrbit rootsB3 octahedronSeed = Set.range octahedronPoint := by
  apply Subset.antisymm
  · apply reflectionOrbit_subset_of_invariant rootsB3 (show octahedronSeed ∈ Set.range octahedronPoint from
      ⟨(false, ⟨0, by decide⟩), rfl⟩)
    rintro i x ⟨p, rfl⟩
    rw [b3_reflection_octahedronPoint]
    exact Set.mem_range_self _
  · rintro x ⟨⟨b, i⟩, rfl⟩
    cases b
    · exact ⟨_, b3AxisWord_apply i⟩
    · exact octahedronAxis_neg_mem_orbit i

theorem unitPolygonRadius_three : unitPolygonRadius 3 = 1 / Real.sqrt 3 := by
  unfold unitPolygonRadius
  norm_num only [Nat.cast_ofNat]
  rw [Real.sin_pi_div_three]
  ring

theorem antiprismHeight_three_sq : antiprismHeight 3 ^ 2 = 2 / 3 := by
  have hr : (unitPolygonRadius 3) ^ 2 = 1 / 3 := by
    rw [unitPolygonRadius_three, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  unfold antiprismHeight
  simp only [Nat.cast_ofNat, show (2 : ℝ) * 3 = 6 by norm_num, Real.sin_pi_div_six]
  have he : 1 - (2 * unitPolygonRadius 3 * (1 / 2)) ^ 2 = 2 / 3 := by nlinarith
  rw [he, Real.sq_sqrt (by norm_num)]

theorem antiprism_three_top_coordinates (i : Fin 3) :
    antiprismPoint 3 false i =
      ![!₂[1 / Real.sqrt 3, 0, antiprismHeight 3 / 2],
        !₂[-(1 / Real.sqrt 3) / 2, 1 / 2, antiprismHeight 3 / 2],
        !₂[-(1 / Real.sqrt 3) / 2, -(1 / 2), antiprismHeight 3 / 2]] i := by
  have h1 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  have h2 : 2 * Real.pi * (2 : ℝ) / 3 = Real.pi + Real.pi / 3 := by ring
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [antiprismPoint, unitPolygonRadius_three, h1, h2, Real.cos_pi_sub,
      Real.sin_pi_sub, Real.cos_add, Real.sin_add, Real.sin_pi_div_three,
      Real.cos_pi_div_three, Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] <;> field_simp

noncomputable def triangularBottomMatch : Equiv.Perm (Fin 3) :=
  (Equiv.swap (⟨0, by decide⟩ : Fin 3) ⟨1, by decide⟩).trans
    (Equiv.swap (⟨1, by decide⟩ : Fin 3) ⟨2, by decide⟩)

theorem antiprism_three_bottom_coordinates (i : Fin 3) :
    antiprismPoint 3 true i = -antiprismPoint 3 false (triangularBottomMatch i) := by
  rw [antiprism_three_top_coordinates]
  have h1 : 2 * Real.pi / 3 + Real.pi / 3 = Real.pi := by ring
  have h2 : 2 * Real.pi * (2 : ℝ) / 3 + Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [antiprismPoint, unitPolygonRadius_three, triangularBottomMatch,
      Equiv.swap_apply_def, h1, h2, Real.cos_sub, Real.sin_sub, Real.sin_pi_div_three,
      Real.cos_pi_div_three, Real.cos_two_pi, Real.sin_two_pi,
      Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] <;> field_simp

theorem antiprism_three_top_gram (i j : Fin 3) :
    ⟪antiprismPoint 3 false i, antiprismPoint 3 false j⟫ = if i = j then (1 / 2 : ℝ) else 0 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hh := antiprismHeight_three_sq
  rw [antiprism_three_top_coordinates, antiprism_three_top_coordinates]
  fin_cases i <;> fin_cases j <;>
    norm_num [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_succ, Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] <;>
    field_simp <;> nlinarith

theorem octahedronAxis_gram (i j : Fin 3) :
    ⟪octahedronAxis i, octahedronAxis j⟫ = if i = j then (1 / 2 : ℝ) else 0 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;>
    norm_num [octahedronAxis, coordinateVector, real_inner_smul_left, inner_smul_right,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
      Fin.isValue, Fin.mk.injEq] <;> nlinarith

/-- Equal finite Gram matrices give an ambient isometric linear map. -/
theorem exists_space3_isometry_of_gram (v w : Fin 3 → Space 3)
    (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) :
    ∃ M : Space 3 →ₗᵢ[ℝ] Space 3, ∀ i, M (v i) = w i := by
  let L := gramRangeIsometry v w h
  let M : Space 3 →ₗᵢ[ℝ] Space 3 := L.extend
  refine ⟨M, fun i => ?_⟩
  have hv : Finsupp.linearCombination ℝ v (Finsupp.single i 1) = v i := by simp
  have hw : Finsupp.linearCombination ℝ w (Finsupp.single i 1) = w i := by simp
  have hmem : v i ∈ LinearMap.range (Finsupp.linearCombination ℝ v) := ⟨_, hv⟩
  calc
    M (v i) = L ⟨v i, hmem⟩ := L.extend_apply ⟨v i, hmem⟩
    _ = w i := by simpa only [hv, hw] using gramRangeIsometry_apply v w h (Finsupp.single i 1)

/-- The three-antiprism's six vertices are the three orthogonal top rays
and their opposites, hence its complete hull is the unit octahedron. -/
theorem congruent_antiprism_three_octahedron :
    Congruent (antiprismModel 3) (WythoffHull rootsB3 octahedronSeed) := by
  obtain ⟨M, hM⟩ := exists_space3_isometry_of_gram octahedronAxis (antiprismPoint 3 false)
    (fun i j => (octahedronAxis_gram i j).trans (antiprism_three_top_gram i j).symm)
  have he : M '' Set.range octahedronPoint =
      Set.range (fun p : Bool × Fin 3 => antiprismPoint 3 p.1 p.2) := by
    ext y
    constructor
    · rintro ⟨x, ⟨⟨b, i⟩, rfl⟩, rfl⟩
      cases b
      · exact ⟨(false, i), (hM i).symm⟩
      · refine ⟨(true, triangularBottomMatch.symm i), ?_⟩
        change antiprismPoint 3 true (triangularBottomMatch.symm i) =
          M (octahedronPoint (true, i))
        rw [antiprism_three_bottom_coordinates, Equiv.apply_symm_apply]
        simp [octahedronPoint, hM]
    · rintro ⟨⟨b, i⟩, rfl⟩
      cases b
      · exact ⟨octahedronPoint (false, i), Set.mem_range_self _, hM i⟩
      · refine ⟨octahedronPoint (true, triangularBottomMatch i), Set.mem_range_self _, ?_⟩
        change M (octahedronPoint (true, triangularBottomMatch i)) = antiprismPoint 3 true i
        rw [antiprism_three_bottom_coordinates]
        simp [octahedronPoint, hM]
  have hh : M.toAffineIsometry '' WythoffHull rootsB3 octahedronSeed = antiprismModel 3 := by
    rw [WythoffHull, octahedronSeed_orbit]
    change M.toLinearMap.toAffineMap '' convexHull ℝ _ = _
    rw [M.toLinearMap.toAffineMap.image_convexHull]
    change convexHull ℝ (M '' Set.range octahedronPoint) = _
    rw [he]
    rfl
  rw [← hh]
  exact congruent_symm (congruent_affineIsometry_image M.toAffineIsometry _)

theorem b3_octahedron_named : NamedPolyhedronModel 1 (WythoffHull rootsB3 octahedronSeed) := by
  change B3RingModel {0} (WythoffHull rootsB3 octahedronSeed)
  exact ⟨octahedronSeed, octahedronSeed_seed, congruent_refl _⟩

theorem facet_octahedronPrism_iff {E : Type*} [PseudoMetricSpace E] {P : Set E} :
    FacetLibraryModel (.polyhedronPrism 1) P ↔
      Congruent P (polyhedralPrismModel (WythoffHull rootsB3 octahedronSeed)) := by
  constructor
  · rintro ⟨Q, hQ, hPQ⟩
    exact congruent_trans hPQ (congruent_product
      (namedPolyhedronModel_unique hQ b3_octahedron_named) (congruent_refl unitInterval))
  · intro h
    exact ⟨_, b3_octahedron_named, h⟩

/-- Literal alias-table entry antiprism-prism(3) → pr-octahedron. -/
theorem triangularAntiprismPrism_octahedron_alias
    {E : Type*} [PseudoMetricSpace E] {P : Set E} :
    FacetLibraryModel (.antiprismPrism 0) P ↔ FacetLibraryModel (.polyhedronPrism 1) P := by
  rw [facet_octahedronPrism_iff]
  change Congruent P (antiprismPrismModel 3) ↔
    Congruent P (polyhedralPrismModel (WythoffHull rootsB3 octahedronSeed))
  have h := congruent_product congruent_antiprism_three_octahedron (congruent_refl unitInterval)
  exact ⟨fun hP => congruent_trans hP h, fun hP => congruent_trans hP (congruent_symm h)⟩

end Uniform5.Composition
