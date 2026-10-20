import Uniform5.CompositionFigureFaces

/-!
# Lifting actual faces from a geometric vertex section
-/

noncomputable section

namespace Uniform5.Composition

open Set Classical
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive generator heights make the origin the unique zero-height
point in the entire finite hull. -/
theorem finiteHull_height_nonnegative_zero (V : Finset E) (L : E →L[ℝ] ℝ)
    (hheight : ∀ x ∈ V.erase 0, 0 < L x) :
    ∀ x ∈ convexHull ℝ (V : Set E), 0 ≤ L x ∧ (L x = 0 → x = 0) := by
  apply convexHull_min
  · intro x hx
    change 0 ≤ L x ∧ (L x = 0 → x = 0)
    by_cases hx0 : x = 0
    · simp [hx0]
    have hpos := hheight x (Finset.mem_erase.mpr ⟨hx0, hx⟩)
    exact ⟨hpos.le, fun heq => False.elim (hpos.ne' heq)⟩
  · intro x hx y hy a b ha hb hab
    change 0 ≤ L x ∧ (L x = 0 → x = 0) at hx
    change 0 ≤ L y ∧ (L y = 0 → y = 0) at hy
    change 0 ≤ L (a • x + b • y) ∧ (L (a • x + b • y) = 0 → a • x + b • y = 0)
    simp only [map_add, map_smul, smul_eq_mul]
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_⟩
    intro hz
    have hax : a • x = 0 := by
      by_cases ha0 : a = 0
      · simp [ha0]
      have hamul : a * L x = 0 := by nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
      have : L x = 0 := (mul_eq_zero.mp hamul).resolve_left ha0
      simp [hx.2 this]
    have hby : b • y = 0 := by
      by_cases hb0 : b = 0
      · simp [hb0]
      have hbmul : b * L y = 0 := by nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
      have : L y = 0 := (mul_eq_zero.mp hbmul).resolve_left hb0
      simp [hy.2 this]
    simp [hax, hby]

/-- Every positive-height hull point normalizes into the geometric section. -/
theorem finiteHull_radialPoint_mem_section (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {x : E} (hx : x ∈ convexHull ℝ (V : Set E)) (hxpos : 0 < L x) :
    radialPoint L x ∈ heightSection (convexHull ℝ (V : Set E)) L := by
  classical
  let T := V.erase 0
  have hpos (z : E) (hz : z ∈ T) : 0 < L z := lt_of_lt_of_le zero_lt_one (hheight z hz)
  have hsection : heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ ((radialPoint L) '' (T : Set E)) :=
    finiteHull_radial_section V hzero L hheight
  rw [hsection]
  obtain ⟨w, hw, _, hxw⟩ := Finset.mem_convexHull'.mp hx
  let a : E → ℝ := fun z => w z * L z
  have hsuma : ∑ z ∈ T, a z = L x := by
    have hsumV : ∑ z ∈ V, a z = L x := by
      calc
        ∑ z ∈ V, a z = L (∑ z ∈ V, w z • z) := by simp [a, map_sum, mul_comm]
        _ = L x := by rw [hxw]
    simpa [T, a] using (Finset.sum_erase_add V (fun z => a z) hzero).trans hsumV
  have hsumr : ∑ z ∈ T, a z • radialPoint L z = x := by
    calc
      ∑ z ∈ T, a z • radialPoint L z = ∑ z ∈ T, w z • z := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [a, radialPoint, smul_smul, (hpos z hz).ne']
      _ = ∑ z ∈ V, w z • z := by
        simpa [T] using Finset.sum_erase_add V (fun z => w z • z) hzero
      _ = x := hxw
  have hcm := Finset.centerMass_mem_convexHull
    (s := (radialPoint L) '' (T : Set E)) T (w := a) (z := radialPoint L)
    (fun z hz => mul_nonneg (hw z (Finset.mem_erase.mp hz).2) (hpos z hz).le)
    (by rw [hsuma]; exact hxpos) (fun z hz => ⟨z, hz, rfl⟩)
  rw [Finset.centerMass, hsuma, hsumr] at hcm
  exact hcm

theorem radialPoint_smul (L : E →L[ℝ] ℝ) (x : E) {a : ℝ} (ha : a ≠ 0) :
    radialPoint L (a • x) = radialPoint L x := by
  simp [radialPoint, smul_smul, mul_inv_rev, ha]

/-- Radial normalization reweights a positive-height combination. -/
theorem radialPoint_combination (L : E →L[ℝ] ℝ) {x y : E}
    (hx : L x ≠ 0) (hy : L y ≠ 0) (a b : ℝ) :
    radialPoint L (a • x + b • y) =
      (a * L x / L (a • x + b • y)) • radialPoint L x +
      (b * L y / L (a • x + b • y)) • radialPoint L y := by
  simp only [radialPoint, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hx, hy]

/-- Lift a section face along its rays, retaining the apex. -/
noncomputable def sectionFaceLift (P : Set E) (L : E →L[ℝ] ℝ) (G : Set E) : Set E :=
  {x ∈ P | x = 0 ∨ radialPoint L x ∈ G}

/-- The section face condition on an interior segment is equivalent to the
condition at both endpoints. This proves both convexity and extremality of
the lifted geometric face. -/
theorem sectionFaceLift_combo_iff (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {G : Set E} (hG : IsConvexFace (heightSection (convexHull ℝ (V : Set E)) L) G)
    {x y : E} (hx : x ∈ convexHull ℝ (V : Set E))
    (hy : y ∈ convexHull ℝ (V : Set E))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a • x + b • y = 0 ∨ radialPoint L (a • x + b • y) ∈ G) ↔
      (x = 0 ∨ radialPoint L x ∈ G) ∧ (y = 0 ∨ radialPoint L y ∈ G) := by
  by_cases hx0 : x = 0
  · simp [hx0, smul_eq_zero, hb.ne', radialPoint_smul L y hb.ne']
  by_cases hy0 : y = 0
  · simp [hy0, smul_eq_zero, ha.ne', radialPoint_smul L x ha.ne']
  have hpositive (z : E) (hz : z ∈ convexHull ℝ (V : Set E)) (hz0 : z ≠ 0) :
      0 < L z := by
    have hh := finiteHull_height_nonnegative_zero V L
      (fun z hz => lt_of_lt_of_le zero_lt_one (hheight z hz)) z hz
    exact lt_of_le_of_ne hh.1 (fun heq => hz0 (hh.2 heq.symm))
  have hxpos := hpositive x hx hx0
  have hypos := hpositive y hy hy0
  have hzpos : 0 < L (a • x + b • y) := by
    simp only [map_add, map_smul, smul_eq_mul]
    exact add_pos (mul_pos ha hxpos) (mul_pos hb hypos)
  have hz0 : a • x + b • y ≠ 0 := by
    intro h
    simp [h] at hzpos
  have hseg : radialPoint L (a • x + b • y) ∈
      openSegment ℝ (radialPoint L x) (radialPoint L y) := by
    refine ⟨a * L x / L (a • x + b • y), b * L y / L (a • x + b • y),
      div_pos (mul_pos ha hxpos) hzpos, div_pos (mul_pos hb hypos) hzpos, ?_, ?_⟩
    · rw [← add_div]
      have hL : a * L x + b * L y = L (a • x + b • y) := by
        simp [map_add, map_smul]
      rw [hL, div_self hzpos.ne']
    · exact (radialPoint_combination L hxpos.ne' hypos.ne' a b).symm
  simp only [hx0, hy0, hz0, false_or]
  constructor
  · intro hzG
    exact hG.2.2 (finiteHull_radialPoint_mem_section V hzero L hheight hx hxpos)
      (finiteHull_radialPoint_mem_section V hzero L hheight hy hypos) hzG hseg
  · rintro ⟨hxG, hyG⟩
    exact hG.1.openSegment_subset hxG hyG hseg

/-- Every actual face of the vertex section lifts to an actual face of the
original finite polytope containing the apex. -/
theorem sectionFaceLift_isFace (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    {G : Set E} (hG : IsConvexFace (heightSection (convexHull ℝ (V : Set E)) L) G) :
    IsConvexFace (convexHull ℝ (V : Set E))
      (sectionFaceLift (convexHull ℝ (V : Set E)) L G) := by
  constructor
  · apply convex_iff_openSegment_subset.mpr
    intro x hx y hy z hz
    refine ⟨(convex_convexHull ℝ (V : Set E)).openSegment_subset hx.1 hy.1 hz, ?_⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    exact (sectionFaceLift_combo_iff V hzero L hheight hG hx.1 hy.1 ha hb).mpr
      ⟨hx.2, hy.2⟩
  · refine ⟨fun _ hx => hx.1, ?_⟩
    intro x hx y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    have hxy := (sectionFaceLift_combo_iff V hzero L hheight hG hx hy ha hb).mp hz.2
    exact ⟨⟨hx, hxy.1⟩, ⟨hy, hxy.2⟩⟩

/-- Cutting the lifted face returns the original geometric section face. -/
theorem sectionFaceLift_section {P G : Set E} (L : E →L[ℝ] ℝ)
    (hG : G ⊆ heightSection P L) :
    sectionFaceLift P L G ∩ heightSection P L = G := by
  ext x
  constructor
  · rintro ⟨hx, hxC⟩
    rcases hx.2 with hx0 | hxG
    · have : L x = 1 := hxC.2
      simp [hx0] at this
    · simpa [radialPoint, hxC.2] using hxG
  · intro hxG
    have hxC := hG hxG
    refine ⟨⟨hxC.1, Or.inr ?_⟩, hxC⟩
    simpa [radialPoint, hxC.2] using hxG

/-- The actual apex-face order embedding is surjective onto every actual
geometric face of the height-one section, including the empty face. -/
theorem apexFaceSectionEmbedding_surjective (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x) :
    Function.Surjective (apexFaceSectionEmbedding V L hheight) := by
  intro G
  let F : GeometricFace (convexHull ℝ (V : Set E)) :=
    ⟨sectionFaceLift (convexHull ℝ (V : Set E)) L G.val,
      sectionFaceLift_isFace V hzero L hheight G.property⟩
  have hFzero : (0 : E) ∈ F.val := ⟨subset_convexHull ℝ (V : Set E) hzero, Or.inl rfl⟩
  refine ⟨⟨F, hFzero⟩, ?_⟩
  apply Subtype.ext
  exact sectionFaceLift_section L G.property.2.1

/-- The actual face-poset correspondence between faces through the apex
and faces of the geometric vertex section, derived from finite convexity. -/
noncomputable def apexFaceSectionEquiv (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x) :
    {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val} ≃o
      GeometricFace (heightSection (convexHull ℝ (V : Set E)) L) where
  toEquiv := Equiv.ofBijective (apexFaceSectionEmbedding V L hheight)
    ⟨(apexFaceSectionEmbedding V L hheight).injective,
      apexFaceSectionEmbedding_surjective V hzero L hheight⟩
  map_rel_iff' := (apexFaceSectionEmbedding V L hheight).map_rel_iff

/-- The correspondence sends each actual face to its literal section. -/
@[simp] theorem apexFaceSectionEquiv_apply (V : Finset E) (hzero : 0 ∈ V)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (F : {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val}) :
    (apexFaceSectionEquiv V hzero L hheight F).val =
      F.val.val ∩ heightSection (convexHull ℝ (V : Set E)) L := rfl

end Uniform5.Composition
