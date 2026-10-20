import Uniform5.CompositionWythoffSeedUnique

/-! Uniqueness of the concrete eighteen named polyhedron models. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

theorem rootsB3_annihilator {x : ModelSpace 3} (hx : ∀ i, ⟪rootsB3 i, x⟫ = 0) : x = 0 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  norm_num [rootsB3, coordinateVector, inner_sub_left, EuclideanSpace.inner_single_left,
    Fin.isValue, Fin.mk.injEq, Fin.succ] at h0 h1 h2
  have hx2 : x 2 = 0 := h2
  have hx1 : x 1 = 0 := by
    have hh : x 1 - x 2 = 0 := h1
    linarith
  have hx0 : x 0 = 0 := by
    have hh : x 0 - x 1 = 0 := h0
    linarith
  ext i
  fin_cases i <;> first | exact hx0 | exact hx1 | exact hx2

theorem rootsH3_annihilator {x : ModelSpace 3} (hx : ∀ i, ⟪rootsH3 i, x⟫ = 0) : x = 0 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  norm_num [rootsH3, coordinateVector, inner_add_left, inner_neg_left,
    real_inner_smul_left, EuclideanSpace.inner_single_left, Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two]
    at h0 h1 h2
  have hg : goldenRatio - 1 ≠ 0 := by
    intro he
    have hh := goldenRatio_sq
    have : goldenRatio = 1 := by linarith
    rw [this] at hh
    norm_num at hh
  have hx2 : x (⟨2, by decide⟩ : Fin 3) = 0 := by
    apply (mul_eq_zero.mp (show (goldenRatio - 1) * x (⟨2, by decide⟩ : Fin 3) = 0 by
      rw [h0] at h1
      nlinarith)).resolve_left hg
  have hx0 : x 0 = 0 := h0
  have hx1 : x 1 = 0 := h2
  ext i
  fin_cases i <;> first | exact hx0 | exact hx1 | exact hx2

theorem rootsB3_span : Submodule.span ℝ (Set.range rootsB3) = ⊤ :=
  root_span_top_of_annihilator rootsB3 (fun _ => rootsB3_annihilator)

theorem rootsH3_span : Submodule.span ℝ (Set.range rootsH3) = ⊤ :=
  root_span_top_of_annihilator rootsH3 (fun _ => rootsH3_annihilator)

theorem a3_seed_unique {J : Finset (Fin 3)} {x y : ModelSpace 4}
    (hx0 : (∑ i, x i) = 0) (hy0 : (∑ i, y i) = 0)
    (hx : WythoffSeed rootsA3 J x) (hy : WythoffSeed rootsA3 J y) : x = y := by
  have h (i : Fin 3) : x i.castSucc - x i.succ = y i.castSucc - y i.succ := by
    have hh := (hx i).trans (hy i).symm
    simpa [rootsA3, coordinateVector, inner_sub_left, EuclideanSpace.inner_single_left] using hh
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [Fin.sum_univ_succ, Fin.succ] at hx0 hy0 h0 h1 h2
  change x 0 - x 1 = y 0 - y 1 at h0
  change x 1 - x 2 = y 1 - y 2 at h1
  change x 2 - x 3 = y 2 - y 3 at h2
  change x 0 + (x 1 + (x 2 + x 3)) = 0 at hx0
  change y 0 + (y 1 + (y 2 + y 3)) = 0 at hy0
  have he0 : x 0 = y 0 := by linarith
  have he1 : x 1 = y 1 := by linarith
  have he2 : x 2 = y 2 := by linarith
  have he3 : x 3 = y 3 := by linarith
  ext i
  fin_cases i <;> first | exact he0 | exact he1 | exact he2 | exact he3

/-- Two successive unit-root reflections have this exact chord square. -/
theorem two_reflections_chord_sq {a b x : Space 3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    dist x (mirrorReflection a (mirrorReflection b x)) ^ 2 =
      4 * (⟪a, x⟫ ^ 2 + ⟪b, x⟫ ^ 2 - 2 * ⟪a, b⟫ * ⟪a, x⟫ * ⟪b, x⟫) := by
  rw [dist_eq_norm, norm_sub_sq_real]
  simp only [mirrorReflection_norm]
  simp only [mirrorReflection_formula, ha, hb, one_pow, div_one, inner_sub_right,
    inner_smul_right, inner_sub_left, real_inner_smul_left]
  rw [real_inner_comm x a, real_inner_comm x b, real_inner_self_eq_norm_sq]
  ring

/-- Positivity makes the snub ratio equations injective throughout the
positive chamber, independently of the width of the certificate box. -/
theorem positive_snub_ratios_unique {a b t s t' s' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a * b < 1)
    (ht : 0 < t) (hs : 0 < s) (ht' : 0 < t') (hs' : 0 < s')
    (het : t ^ 2 = 1 + 2 * b * s) (hes : s ^ 2 = 1 + 2 * a * t)
    (het' : t' ^ 2 = 1 + 2 * b * s') (hes' : s' ^ 2 = 1 + 2 * a * t') :
    t = t' ∧ s = s' := by
  have ht1 : 1 < t := by nlinarith [mul_pos hb hs]
  have hs1 : 1 < s := by nlinarith [mul_pos ha ht]
  have ht1' : 1 < t' := by nlinarith [mul_pos hb hs']
  have hs1' : 1 < s' := by nlinarith [mul_pos ha ht']
  have hpos : 0 < (t + t') * (s + s') - 4 * a * b := by
    have hmul := mul_lt_mul_of_pos_right (show (2 : ℝ) < t + t' by linarith)
      (show 0 < s + s' by linarith)
    nlinarith
  have he : (t - t') * ((t + t') * (s + s') - 4 * a * b) = 0 := by
    linear_combination (s + s') * (het - het') + 2 * b * (hes - hes')
  have htt : t = t' := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hpos.ne')
  refine ⟨htt, ?_⟩
  rw [htt] at het
  nlinarith

/-- Equal selected rotation chords become two ratio equations in the
three signed simple-root coordinates. -/
theorem snubSeed_inner_equations {r : Fin 3 → Space 3} {lo hi : Fin 3 → ℚ}
    {c : Space 3} (hc : SnubSeed r lo hi c)
    (hn : ∀ i, ‖r i‖ = 1) {a b : ℝ}
    (h01 : ⟪r 0, r 1⟫ = -a) (h12 : ⟪r 1, r 2⟫ = -b)
    (h02 : ⟪r 0, r 2⟫ = 0) :
    let x := snubPhysicalSeed r c
    ⟪r 0, x⟫ ^ 2 = ⟪r 1, x⟫ ^ 2 + 2 * b * ⟪r 1, x⟫ * ⟪r 2, x⟫ ∧
    ⟪r 2, x⟫ ^ 2 = ⟪r 1, x⟫ ^ 2 + 2 * a * ⟪r 0, x⟫ * ⟪r 1, x⟫ := by
  let x := snubPhysicalSeed r c
  have hA := two_reflections_chord_sq (x := x) (hn 0) (hn 1)
  have hB := two_reflections_chord_sq (x := x) (hn 1) (hn 2)
  have hC := two_reflections_chord_sq (x := x) (hn 0) (hn 2)
  rw [h01] at hA
  rw [h12] at hB
  rw [h02] at hC
  have heA : snubRotationWord r [0] x = mirrorReflection (r 0) (mirrorReflection (r 1) x) := rfl
  have heB : snubRotationWord r [1] x = mirrorReflection (r 1) (mirrorReflection (r 2) x) := rfl
  have heC : snubRotationWord r [0, 1] x = mirrorReflection (r 0) (mirrorReflection (r 2) x) := by
    change mirrorReflection (r 0) (mirrorReflection (r 1) (mirrorReflection (r 1)
      (mirrorReflection (r 2) x))) = _
    rw [mirrorReflection_involutive]
  have he1 := hc.2.2.1
  have he2 := hc.2.2.2.1
  change dist x (snubRotationWord r [0] x) ^ 2 = dist x (snubRotationWord r [1] x) ^ 2 at he1
  change dist x (snubRotationWord r [0] x) ^ 2 = dist x (snubRotationWord r [0, 1] x) ^ 2 at he2
  rw [heA, heB, hA, hB] at he1
  rw [heA, heC, hA, hC] at he2
  dsimp only
  change ⟪r 0, x⟫ ^ 2 = _ ∧ ⟪r 2, x⟫ ^ 2 = _
  constructor <;> nlinarith

/-- A positive-chamber snub seed is unique as an actual physical point.
The norm equation fixes the positive scale left by the chord ratios. -/
theorem positive_snubPhysicalSeed_unique {r : Fin 3 → Space 3} {lo hi : Fin 3 → ℚ}
    {c d : Space 3} (hc : SnubSeed r lo hi c) (hd : SnubSeed r lo hi d)
    (hn : ∀ i, ‖r i‖ = 1)
    (hspan : ∀ x : Space 3, (∀ i, ⟪r i, x⟫ = 0) → x = 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a * b < 1)
    (h01 : ⟪r 0, r 1⟫ = -a) (h12 : ⟪r 1, r 2⟫ = -b)
    (h02 : ⟪r 0, r 2⟫ = 0)
    (hpc : ∀ i, 0 < ⟪r i, snubPhysicalSeed r c⟫)
    (hpd : ∀ i, 0 < ⟪r i, snubPhysicalSeed r d⟫) :
    snubPhysicalSeed r c = snubPhysicalSeed r d := by
  let x := snubPhysicalSeed r c
  let y := snubPhysicalSeed r d
  let u : Fin 3 → ℝ := fun i => ⟪r i, x⟫
  let v : Fin 3 → ℝ := fun i => ⟪r i, y⟫
  have hu : ∀ i, 0 < u i := hpc
  have hv : ∀ i, 0 < v i := hpd
  obtain ⟨hc0, hc2⟩ := snubSeed_inner_equations hc hn h01 h12 h02
  obtain ⟨hd0, hd2⟩ := snubSeed_inner_equations hd hn h01 h12 h02
  change u 0 ^ 2 = u 1 ^ 2 + 2 * b * u 1 * u 2 at hc0
  change u 2 ^ 2 = u 1 ^ 2 + 2 * a * u 0 * u 1 at hc2
  change v 0 ^ 2 = v 1 ^ 2 + 2 * b * v 1 * v 2 at hd0
  change v 2 ^ 2 = v 1 ^ 2 + 2 * a * v 0 * v 1 at hd2
  have huc0 : (u 0 / u 1) ^ 2 = 1 + 2 * b * (u 2 / u 1) := by
    field_simp [(hu 1).ne']
    linear_combination u 1 * hc0
  have huc2 : (u 2 / u 1) ^ 2 = 1 + 2 * a * (u 0 / u 1) := by
    field_simp [(hu 1).ne']
    linear_combination u 1 * hc2
  have hvc0 : (v 0 / v 1) ^ 2 = 1 + 2 * b * (v 2 / v 1) := by
    field_simp [(hv 1).ne']
    linear_combination v 1 * hd0
  have hvc2 : (v 2 / v 1) ^ 2 = 1 + 2 * a * (v 0 / v 1) := by
    field_simp [(hv 1).ne']
    linear_combination v 1 * hd2
  obtain ⟨h0, h2⟩ := positive_snub_ratios_unique ha hb hab
    (div_pos (hu 0) (hu 1)) (div_pos (hu 2) (hu 1))
    (div_pos (hv 0) (hv 1)) (div_pos (hv 2) (hv 1)) huc0 huc2 hvc0 hvc2
  have hscale0 : u 0 = (u 1 / v 1) * v 0 := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hv 1).ne').mpr
    have hh := (div_eq_div_iff (hu 1).ne' (hv 1).ne').mp h0
    nlinarith only [hh]
  have hscale2 : u 2 = (u 1 / v 1) * v 2 := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hv 1).ne').mpr
    have hh := (div_eq_div_iff (hu 1).ne' (hv 1).ne').mp h2
    nlinarith only [hh]
  have hscale (i : Fin 3) : u i = (u 1 / v 1) * v i := by
    fin_cases i
    · exact hscale0
    · exact (div_mul_cancel₀ (u 1) (hv 1).ne').symm
    · exact hscale2
  have hxy : x = (u 1 / v 1) • y := by
    apply sub_eq_zero.mp
    apply hspan
    intro i
    simpa only [inner_sub_right, inner_smul_right, sub_eq_zero] using hscale i
  have hnX : ‖x‖ = 1 := (sq_eq_sq₀ (norm_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [one_pow] using hc.2.1)
  have hnY : ‖y‖ = 1 := (sq_eq_sq₀ (norm_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [one_pow] using hd.2.1)
  have hscaleone : u 1 / v 1 = 1 := by
    have hh := congrArg norm hxy
    rw [norm_smul, hnX, hnY, mul_one, Real.norm_eq_abs, abs_of_pos (div_pos (hu 1) (hv 1))] at hh
    exact hh.symm
  rw [hscaleone, one_smul] at hxy
  exact hxy

theorem snubCube_seed_coarse_bounds {c : Space 3}
    (hc : SnubSeed snubCubeRoots snubCubeLower snubCubeUpper c) :
    (120 / 100 : ℝ) ≤ c 0 ∧ c 0 ≤ 121 / 100 ∧
    (185 / 100 : ℝ) ≤ c 1 ∧ c 1 ≤ 186 / 100 ∧
    (156 / 100 : ℝ) ≤ c 2 ∧ c 2 ≤ 157 / 100 := by
  have h0 := hc.1 0
  have h1 := hc.1 1
  have h2 := hc.1 2
  norm_num [snubCubeLower, snubCubeUpper, Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] at h0 h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem snubDodeca_seed_coarse_bounds {c : Space 3}
    (hc : SnubSeed snubDodecaRoots snubDodecaLower snubDodecaUpper c) :
    (270 / 100 : ℝ) ≤ c 0 ∧ c 0 ≤ 271 / 100 ∧
    (314 / 100 : ℝ) ≤ c 1 ∧ c 1 ≤ 315 / 100 ∧
    (174 / 100 : ℝ) ≤ c 2 ∧ c 2 ≤ 175 / 100 := by
  have h0 := hc.1 0
  have h1 := hc.1 1
  have h2 := hc.1 2
  norm_num [snubDodecaLower, snubDodecaUpper, Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] at h0 h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem snubPhysicalSeed_inner (r : Fin 3 → Space 3) (c : Space 3) (i : Fin 3) :
    ⟪r i, snubPhysicalSeed r c⟫ = ∑ j, c j * ⟪r i, r j⟫ := by
  simp only [snubPhysicalSeed, inner_sum, inner_smul_right]

theorem sum_fin_three_real (f : Fin 3 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + f 2) = _
  ring

theorem snubCube_seed_positive {c : Space 3}
    (hc : SnubSeed snubCubeRoots snubCubeLower snubCubeUpper c) :
    ∀ i, 0 < ⟪snubCubeRoots i, snubPhysicalSeed snubCubeRoots c⟫ := by
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u⟩ := snubCube_seed_coarse_bounds hc
  have hs : Real.sqrt 2 ≤ 142 / 100 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hprod1 := mul_le_mul hs h1u (by linarith : 0 ≤ c 1) (by norm_num : (0 : ℝ) ≤ 142 / 100)
  have hprod2 := mul_le_mul hs h2u (by linarith : 0 ≤ c 2) (by norm_num : (0 : ℝ) ≤ 142 / 100)
  intro i
  rw [snubPhysicalSeed_inner]
  rw [sum_fin_three_real]
  simp only [snubCubeRoots_gram]
  fin_cases i <;> norm_num [Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] <;> nlinarith

theorem snubDodeca_seed_positive {c : Space 3}
    (hc : SnubSeed snubDodecaRoots snubDodecaLower snubDodecaUpper c) :
    ∀ i, 0 < ⟪snubDodecaRoots i, snubPhysicalSeed snubDodecaRoots c⟫ := by
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u⟩ := snubDodeca_seed_coarse_bounds hc
  have hg : 0 < goldenRatio := by unfold goldenRatio; positivity
  have hg' : goldenRatio ≤ 162 / 100 := by nlinarith [goldenRatio_sq]
  have hprod0 := mul_le_mul hg' h0u (by linarith : 0 ≤ c 0) (by norm_num : (0 : ℝ) ≤ 162 / 100)
  have hprod1 := mul_le_mul hg' h1u (by linarith : 0 ≤ c 1) (by norm_num : (0 : ℝ) ≤ 162 / 100)
  intro i
  rw [snubPhysicalSeed_inner]
  rw [sum_fin_three_real]
  simp only [snubDodecaRoots, rootsH3_gram]
  fin_cases i <;> norm_num [Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] <;> nlinarith

theorem snubCube_physicalSeed_unique {c d : Space 3}
    (hc : SnubSeed snubCubeRoots snubCubeLower snubCubeUpper c)
    (hd : SnubSeed snubCubeRoots snubCubeLower snubCubeUpper d) :
    snubPhysicalSeed snubCubeRoots c = snubPhysicalSeed snubCubeRoots d := by
  apply positive_snubPhysicalSeed_unique hc hd snubCubeRoots_norm
    (a := 1 / 2) (b := Real.sqrt 2 / 2)
  · intro x hx
    apply rootsB3_annihilator
    intro i
    have hh := hx i
    rw [snubCubeRoots, real_inner_smul_left] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr (rootsB3_ne_zero i)))
  · norm_num
  · positivity
  · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  · simpa [neg_div] using snubCubeRoots_gram 0 1
  · simpa [neg_div] using snubCubeRoots_gram 1 2
  · simpa [neg_div] using snubCubeRoots_gram 0 2
  · exact snubCube_seed_positive hc
  · exact snubCube_seed_positive hd

theorem snubDodeca_physicalSeed_unique {c d : Space 3}
    (hc : SnubSeed snubDodecaRoots snubDodecaLower snubDodecaUpper c)
    (hd : SnubSeed snubDodecaRoots snubDodecaLower snubDodecaUpper d) :
    snubPhysicalSeed snubDodecaRoots c = snubPhysicalSeed snubDodecaRoots d := by
  have hg : 0 < goldenRatio := by unfold goldenRatio; positivity
  apply positive_snubPhysicalSeed_unique hc hd rootsH3_norm
    (a := goldenRatio / 2) (b := 1 / 2)
  · exact fun _ => rootsH3_annihilator
  · positivity
  · norm_num
  · nlinarith [goldenRatio_sq]
  · simpa [snubDodecaRoots, neg_div] using rootsH3_gram 0 1
  · simpa [snubDodecaRoots, neg_div] using rootsH3_gram 1 2
  · simpa [snubDodecaRoots, neg_div] using rootsH3_gram 0 2
  · exact snubDodeca_seed_positive hc
  · exact snubDodeca_seed_positive hd

theorem snubFiniteHull_eq_of_physicalSeed_eq {r : Fin 3 → Space 3} {c d : Space 3}
    (h : snubPhysicalSeed r c = snubPhysicalSeed r d) {n : ℕ}
    (words : Fin n → List (Fin 2)) : snubFiniteHull r c words = snubFiniteHull r d words := by
  simp only [snubFiniteHull, snubFinitePoints, snubIndexedPoint, snubEdgeScale, h]

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

theorem isSnubCube_unique {P : Set E} {Q : Set F} (hP : IsSnubCube P) (hQ : IsSnubCube Q) :
    Congruent P Q := by
  obtain ⟨c, hc, hPc⟩ := hP
  obtain ⟨d, hd, hQd⟩ := hQ
  have he := snubFiniteHull_eq_of_physicalSeed_eq (snubCube_physicalSeed_unique hc hd) snubCubeWords
  change snubCubeModel c = snubCubeModel d at he
  rw [he] at hPc
  exact congruent_trans hPc (congruent_symm hQd)

theorem isSnubDodeca_unique {P : Set E} {Q : Set F} (hP : IsSnubDodeca P) (hQ : IsSnubDodeca Q) :
    Congruent P Q := by
  obtain ⟨c, hc, hPc⟩ := hP
  obtain ⟨d, hd, hQd⟩ := hQ
  have he := snubFiniteHull_eq_of_physicalSeed_eq (snubDodeca_physicalSeed_unique hc hd) snubDodecaWords
  change snubDodecaModel c = snubDodecaModel d at he
  rw [he] at hPc
  exact congruent_trans hPc (congruent_symm hQd)

theorem a3RingModel_unique {J : Finset (Fin 3)} {P Q : Set (Space 3)}
    (hP : A3RingModel J P) (hQ : A3RingModel J Q) : Congruent P Q := by
  obtain ⟨x, hx0, hx, hPx⟩ := hP
  obtain ⟨y, hy0, hy, hQy⟩ := hQ
  have he := a3_seed_unique hx0 hy0 hx hy
  subst y
  exact congruent_trans hPx (congruent_symm hQy)

theorem b3RingModel_unique {J : Finset (Fin 3)} {P Q : Set (Space 3)}
    (hP : B3RingModel J P) (hQ : B3RingModel J Q) : Congruent P Q := by
  obtain ⟨x, hx, hPx⟩ := hP
  obtain ⟨y, hy, hQy⟩ := hQ
  have he := wythoffSeed_unique_of_span_top rootsB3_span hx hy
  subst y
  exact congruent_trans hPx (congruent_symm hQy)

theorem h3RingModel_unique {J : Finset (Fin 3)} {P Q : Set (Space 3)}
    (hP : H3RingModel J P) (hQ : H3RingModel J Q) : Congruent P Q := by
  obtain ⟨x, hx, hPx⟩ := hP
  obtain ⟨y, hy, hQy⟩ := hQ
  have he := wythoffSeed_unique_of_span_top rootsH3_span hx hy
  subst y
  exact congruent_trans hPx (congruent_symm hQy)

theorem platonicModel_unique {i : Fin 5} {P Q : Set (Space 3)}
    (hP : PlatonicModel i P) (hQ : PlatonicModel i Q) : Congruent P Q := by
  fin_cases i
  · exact a3RingModel_unique hP hQ
  · exact b3RingModel_unique hP hQ
  · exact b3RingModel_unique hP hQ
  · exact h3RingModel_unique hP hQ
  · exact h3RingModel_unique hP hQ

theorem archimedeanModel_unique {i : Fin 13} {P Q : Set (Space 3)}
    (hP : ArchimedeanModel i P) (hQ : ArchimedeanModel i Q) : Congruent P Q := by
  fin_cases i
  · exact a3RingModel_unique hP hQ
  · exact b3RingModel_unique hP hQ
  · exact b3RingModel_unique hP hQ
  · exact b3RingModel_unique hP hQ
  · exact b3RingModel_unique hP hQ
  · exact b3RingModel_unique hP hQ
  · exact h3RingModel_unique hP hQ
  · exact h3RingModel_unique hP hQ
  · exact h3RingModel_unique hP hQ
  · exact h3RingModel_unique hP hQ
  · exact h3RingModel_unique hP hQ
  · exact isSnubCube_unique hP hQ
  · exact isSnubDodeca_unique hP hQ

/-- Every one of the eighteen named polyhedron entries has a unique
whole-body congruence type, without a model-uniformity premise. -/
theorem namedPolyhedronModel_unique {i : Fin 18} {P Q : Set (Space 3)}
    (hP : NamedPolyhedronModel i P) (hQ : NamedPolyhedronModel i Q) : Congruent P Q := by
  unfold NamedPolyhedronModel at hP hQ
  split_ifs at hP hQ
  · exact platonicModel_unique hP hQ
  · exact archimedeanModel_unique hP hQ

end Uniform5.Composition
