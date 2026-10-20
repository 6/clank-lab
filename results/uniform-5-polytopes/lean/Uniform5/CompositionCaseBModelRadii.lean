import Uniform5.CompositionCaseBFamilyFaces
import Uniform5.CompositionProductAssociativity

/-! Exact Case B radii of concrete family models occurring as actual uniform
faces. Uniformity is transported from the actual face, never presumed of
an unverified coordinate model. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A full-dimensional uniform hull has the radius of any sphere through
its specified generators. The centre need not be computed as a centroid. -/
theorem uniform_radius_sq_of_generator_sphere {d : ℕ} {P S : Set E}
    (hP : Uniform (d + 3) P) (hd : Module.finrank ℝ E = d + 3)
    (hull : P = convexHull ℝ S) (c : E) (s : ℝ)
    (hs : ∀ x ∈ S, dist x c ^ 2 = s) : intrinsicRadius P ^ 2 = s := by
  have hfull : affineSpan ℝ P = ⊤ := by
    have hh : (affineSpan ℝ P).direction = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hd]
      exact uniform_dimension hP
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty ?_).mp hh
    obtain ⟨x, hx⟩ := finitePolytope_nonempty (uniform_finitePolytope hP)
    exact ⟨x, subset_affineSpan ℝ P hx⟩
  let hPP := uniform_finitePolytope hP
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty hPP
  have hsx (y : E) (hy : y ∈ P.extremePoints ℝ) : dist y c ^ 2 = s := by
    apply hs
    rw [hull] at hy
    exact extremePoints_convexHull_subset hy
  have hs0 : 0 ≤ s := (hsx x hx) ▸ sq_nonneg (dist x c)
  obtain ⟨_, hr, hrad⟩ := uniform_hasIntrinsicRadius hP
  have he := finitePolytope_intrinsic_sphere_unique hPP
    (c := c) (a := vertexCentroid (vertices P hPP))
    (R := Real.sqrt s) (r := intrinsicRadius P)
    (by rw [hfull]; trivial)
    (subset_affineSpan ℝ P (intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior hPP)))
    (fun y hy => (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg s)).mp
      ((hsx y hy).trans (Real.sq_sqrt hs0).symm))
    (fun y hy => by rw [dist_eq_norm]; exact (sq_eq_sq₀ (norm_nonneg _) hr).mp (hrad y hy))
  rw [← he.2, Real.sq_sqrt hs0]

theorem unitPolygonRadius_caseB (n : ℕ) : unitPolygonRadius n = CaseB.polygonRadius n := rfl

theorem antiprismHeight_sq_caseB {n : ℕ} (hn : 3 ≤ n) :
    antiprismHeight n ^ 2 = CaseB.antiprismHeightSq n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let t : ℝ := Real.pi / (2 * n)
  have ht : 0 < t := div_pos Real.pi_pos (by positivity)
  have htpi : t < Real.pi / 2 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    nlinarith [Real.pi_pos]
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htpi⟩).ne'
  have he : Real.pi / n = 2 * t := by dsimp [t]; ring
  have hprod : 2 * unitPolygonRadius n * Real.sin t = 1 / (2 * Real.cos t) := by
    unfold unitPolygonRadius
    rw [he, Real.sin_two_mul]
    field_simp
    ring
  have hpos := antiprismHeight_pos hn
  have hrad : 0 ≤ 1 - (2 * unitPolygonRadius n * Real.sin t) ^ 2 := by
    exact (Real.sqrt_pos.mp hpos).le
  unfold antiprismHeight
  change Real.sqrt (1 - (2 * unitPolygonRadius n * Real.sin t) ^ 2) ^ 2 = _
  rw [Real.sq_sqrt hrad, hprod]
  unfold CaseB.antiprismHeightSq
  change 1 - (1 / (2 * Real.cos t)) ^ 2 = 1 - 1 / (4 * Real.cos t ^ 2)
  field_simp
  ring

theorem antiprismPoint_norm_sq (n : ℕ) (b : Bool) (i : Fin n) :
    ‖antiprismPoint n b i‖ ^ 2 = unitPolygonRadius n ^ 2 + antiprismHeight n ^ 2 / 4 := by
  rw [← real_inner_self_eq_norm_sq]
  let t := 2 * Real.pi * (i : ℕ) / n + if b then Real.pi / n else 0
  have ht := Real.sin_sq_add_cos_sq t
  cases b <;>
    simp [antiprismPoint, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_succ, Fin.isValue, Fin.mk.injEq, Matrix.cons_val_two] <;>
    dsimp [t] at ht <;> simp only [add_zero] at ht <;> linear_combination (unitPolygonRadius n) ^ 2 * ht

theorem congruent_antiprism_intrinsicRadius_sq {P : Set E} {n : ℕ}
    (hP : UnitUniform 3 P) (hn : 3 ≤ n) (h : Congruent P (antiprismModel n)) :
    intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq n := by
  have hM := (unitUniform_cross_congruent_iff h 3).mp hP
  rw [intrinsicRadius_cross_congruent h]
  apply (uniform_radius_sq_of_generator_sphere hM.1 (by simp [Space]) rfl 0 _ ?_)
  rintro x ⟨⟨b, i⟩, rfl⟩
  rw [dist_zero_right, antiprismPoint_norm_sq, antiprismHeight_sq_caseB hn]
  rfl

/-- Generator radii add in the actual Euclidean product. -/
theorem uniform_product_radius_sq {a b d : ℕ}
    {P S : Set (Space a)} {Q T : Set (Space b)}
    (hU : Uniform (d + 3) (product P Q)) (hd : a + b = d + 3)
    (hP : P = convexHull ℝ S) (hQ : Q = convexHull ℝ T)
    (c : Space a) (e : Space b) (s t : ℝ)
    (hs : ∀ x ∈ S, dist x c ^ 2 = s) (ht : ∀ y ∈ T, dist y e ^ 2 = t) :
    intrinsicRadius (product P Q) ^ 2 = s + t := by
  apply uniform_radius_sq_of_generator_sphere hU
    (by simpa using hd) (by rw [hP, hQ, product_convexHull]) (productPoint c e) (s + t)
  rintro z ⟨x, hx, y, hy, rfl⟩
  rw [productPoint_dist_sq, hs x hx, ht y hy]

theorem unitInterval_generator_sphere :
    ∀ x ∈ ({0, !₂[1]} : Set (Space 1)), dist x (!₂[1 / 2] : Space 1) ^ 2 = 1 / 4 := by
  intro x hx
  rcases hx with rfl | rfl <;>
    norm_num [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

theorem congruent_polygonPrism_intrinsicRadius_sq {P : Set E} {n : ℕ}
    (hP : UnitUniform 3 P) (h : Congruent P (polygonPrismModel n)) :
    intrinsicRadius P ^ 2 = CaseB.polygonRadius n ^ 2 + 1 / 4 := by
  have hM := (unitUniform_cross_congruent_iff h 3).mp hP
  rw [intrinsicRadius_cross_congruent h]
  apply uniform_product_radius_sq hM.1 (by decide) rfl
    (by exact (convexHull_pair (0 : Space 1) !₂[1]).symm) 0 (!₂[1 / 2] : Space 1)
    (CaseB.polygonRadius n ^ 2) (1 / 4) ?_ unitInterval_generator_sphere
  rintro x ⟨i, rfl⟩
  rw [dist_zero_right, polygonPoint_norm_sq]
  rfl

theorem congruent_duoprism_intrinsicRadius_sq {P : Set E} {n q : ℕ}
    (hP : UnitUniform 4 P) (h : Congruent P (duoprismModel n q)) :
    intrinsicRadius P ^ 2 = CaseB.polygonRadius n ^ 2 + CaseB.polygonRadius q ^ 2 := by
  have hM := (unitUniform_cross_congruent_iff h 4).mp hP
  rw [intrinsicRadius_cross_congruent h]
  apply uniform_product_radius_sq hM.1 (by decide) rfl rfl 0 0
    (CaseB.polygonRadius n ^ 2) (CaseB.polygonRadius q ^ 2)
  · rintro x ⟨i, rfl⟩
    rw [dist_zero_right, polygonPoint_norm_sq]
    rfl
  · rintro x ⟨i, rfl⟩
    rw [dist_zero_right, polygonPoint_norm_sq]
    rfl

theorem congruent_antiprismPrism_intrinsicRadius_sq {P : Set E} {n : ℕ}
    (hP : UnitUniform 4 P) (hn : 3 ≤ n) (h : Congruent P (antiprismPrismModel n)) :
    intrinsicRadius P ^ 2 = CaseB.antiprismRadiusSq n + 1 / 4 := by
  have hM := (unitUniform_cross_congruent_iff h 4).mp hP
  rw [intrinsicRadius_cross_congruent h]
  apply uniform_product_radius_sq hM.1 (by decide) rfl
    (by exact (convexHull_pair (0 : Space 1) !₂[1]).symm) 0 (!₂[1 / 2] : Space 1)
    (CaseB.antiprismRadiusSq n) (1 / 4) ?_ unitInterval_generator_sphere
  rintro x ⟨⟨b, i⟩, rfl⟩
  rw [dist_zero_right, antiprismPoint_norm_sq, antiprismHeight_sq_caseB hn]
  rfl

/-- A prism cell has exactly half a unit of transverse centroid height. -/
theorem ActualPolygonCycle.prism_height {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (i : ℕ)
    (h : Congruent (D.cell i) (polygonPrismModel n)) : D.height n i = 1 / 2 := by
  have hr := congruent_polygonPrism_intrinsicRadius_sq (D.cell_unitUniform hP hG i) h
  unfold ActualPolygonCycle.height
  rw [hr, unitPolygonRadius_caseB]
  have he : CaseB.polygonRadius n ^ 2 + 1 / 4 - CaseB.polygonRadius n ^ 2 = (1 / 2 : ℝ) ^ 2 := by ring
  rw [he, Real.sqrt_sq (by norm_num)]

/-- An antiprism cell's transverse centroid height is half its layer separation. -/
theorem ActualPolygonCycle.antiprism_height {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn : 3 ≤ n) (i : ℕ)
    (h : Congruent (D.cell i) (antiprismModel n)) : D.height n i = antiprismHeight n / 2 := by
  have hr := congruent_antiprism_intrinsicRadius_sq (D.cell_unitUniform hP hG i) hn h
  unfold ActualPolygonCycle.height
  rw [hr, CaseB.antiprismRadiusSq, unitPolygonRadius_caseB,
    ← antiprismHeight_sq_caseB hn]
  have he : CaseB.polygonRadius n ^ 2 + antiprismHeight n ^ 2 / 4 -
      CaseB.polygonRadius n ^ 2 = (antiprismHeight n / 2) ^ 2 := by ring
  rw [he, Real.sqrt_sq (by exact div_nonneg (antiprismHeight_pos hn).le (by norm_num))]

end Uniform5.Composition
