import Uniform5.CompositionPlanarFan
import Uniform5.CompositionEdgeFaces

/-! Consecutive angular vertices are actual exposed polygon edges. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two nonnegative coefficients with total at most one give a convex
combination after filling the remaining weight with the origin. -/
theorem convex_two_smul_mem_of_sum_le_one {C : Set E} (hC : Convex ℝ C)
    (h0 : (0 : E) ∈ C) {x z : E} (hx : x ∈ C) (hz : z ∈ C)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    a • x + b • z ∈ C := by
  have hh := hC.sum_mem (t := Finset.univ) (w := ![1-a-b, a, b])
    (z := ![(0 : E), x, z])
    (by intro i hi; fin_cases i <;> dsimp <;> linarith)
    (by simp [Fin.sum_univ_succ])
    (by intro i hi; fin_cases i <;> assumption)
  simpa [Fin.sum_univ_succ] using hh

/-- A nonpositive coordinate outside two extreme rays forces the chord
functional strictly below its value at those two endpoints. -/
theorem extreme_two_ray_coordinate_sum_lt_one {P : Set E} (hP : Convex ℝ P)
    (h0 : (0 : E) ∈ P) {x y z : E}
    (hx : x ∈ P.extremePoints ℝ) (hy : y ∈ P.extremePoints ℝ) (hz : z ∈ P)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    {a b : ℝ} (hzab : z = a • x + b • y) (hout : a ≤ 0 ∨ b ≤ 0) : a + b < 1 := by
  have step {x y z : E} (hy : y ∈ P.extremePoints ℝ) (hx : x ∈ P) (hz : z ∈ P)
      (hy0 : y ≠ 0) (hxy : x ≠ y) (hzy : z ≠ y)
      {a b : ℝ} (hzab : z = a • x + b • y) (ha : a ≤ 0) : a + b < 1 := by
    by_contra hn
    have hab : 1 ≤ a + b := le_of_not_gt hn
    have hb : 0 < b := by linarith
    have hC := (hP.mem_extremePoints_iff_convex_diff.mp hy).2
    have hh := convex_two_smul_mem_of_sum_le_one hC
      ⟨h0, hy0.symm⟩ ⟨hx, hxy⟩ ⟨hz, hzy⟩
      (div_nonneg (neg_nonneg.mpr ha) hb.le) (div_nonneg zero_le_one hb.le)
      (show -a / b + 1 / b ≤ 1 by rw [← add_div, div_le_one hb]; linarith)
    have heq : (-a / b) • x + (1 / b) • z = y := by
      rw [hzab, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
      have he1 : -a / b + 1 / b * a = 0 := by field_simp
      have he2 : 1 / b * b = 1 := by field_simp
      rw [he1, he2, zero_smul, one_smul, zero_add]
    rw [heq] at hh
    exact hh.2 rfl
  rcases hout with ha | hb
  · exact step hy hx.1 hz hy0 hxy hzy hzab ha
  · have hh := step hx hy.1 hz hx0 hxy.symm hzx (a := b) (b := a)
      (by rw [hzab, add_comm]) hb
    linarith

/-- Oriented determinant in the real complex plane. -/
noncomputable def planarDet (x y : ℂ) : ℝ := x.re * y.im - x.im * y.re

/-- First coordinate in the basis of two noncollinear rays. -/
noncomputable def planarFirstCoordinate (x y : ℂ) : ℂ →ₗ[ℝ] ℝ :=
  (planarDet x y)⁻¹ • (y.im • Complex.reLm - y.re • Complex.imLm)

/-- Second coordinate in the basis of two noncollinear rays. -/
noncomputable def planarSecondCoordinate (x y : ℂ) : ℂ →ₗ[ℝ] ℝ :=
  (planarDet x y)⁻¹ • (x.re • Complex.imLm - x.im • Complex.reLm)

@[simp] theorem planarFirstCoordinate_apply (x y z : ℂ) :
    planarFirstCoordinate x y z = planarDet z y / planarDet x y := by
  simp [planarFirstCoordinate, planarDet, div_eq_mul_inv]; ring

@[simp] theorem planarSecondCoordinate_apply (x y z : ℂ) :
    planarSecondCoordinate x y z = planarDet x z / planarDet x y := by
  simp [planarSecondCoordinate, planarDet, div_eq_mul_inv]; ring

theorem planar_coordinates_reconstruct {x y : ℂ} (hd : planarDet x y ≠ 0) (z : ℂ) :
    z = planarFirstCoordinate x y z • x + planarSecondCoordinate x y z • y := by
  apply Complex.ext <;>
    simp only [planarFirstCoordinate_apply, planarSecondCoordinate_apply, Complex.add_re,
      Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  · field_simp
    simp only [planarDet]
    ring
  · field_simp
    simp only [planarDet]
    ring

theorem planarDet_eq_norm_sin (x y : ℂ) :
    planarDet x y = ‖x‖ * ‖y‖ * Real.sin (y.arg - x.arg) := by
  rw [Real.sin_sub, planarDet, ← Complex.norm_mul_cos_arg x, ← Complex.norm_mul_sin_arg x,
    ← Complex.norm_mul_cos_arg y, ← Complex.norm_mul_sin_arg y]
  ring

/-- The chord is an actual exposed edge if every other actual vertex lies
outside its positive ray sector. This is derived from endpoint extremity. -/
theorem planar_edge_of_ray_coordinates {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ P) {x y : ℂ}
    (hx : x ∈ P.extremePoints ℝ) (hy : y ∈ P.extremePoints ℝ)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hd : planarDet x y ≠ 0)
    (hout : ∀ z ∈ P.extremePoints ℝ, z ≠ x → z ≠ y →
      planarFirstCoordinate x y z ≤ 0 ∨ planarSecondCoordinate x y z ≤ 0) : Edge P x y := by
  have hxy : x ≠ y := by intro h; apply hd; simp [h, planarDet, mul_comm]
  let L : ℂ →L[ℝ] ℝ := (planarFirstCoordinate x y + planarSecondCoordinate x y).toContinuousLinearMap
  have hself (z : ℂ) : planarDet z z = 0 := by simp [planarDet, mul_comm]
  have hLx : L x = 1 := by
    change planarFirstCoordinate x y x + planarSecondCoordinate x y x = 1
    rw [planarFirstCoordinate_apply, planarSecondCoordinate_apply, hself, zero_div, add_zero, div_self hd]
  have hLy : L y = 1 := by
    change planarFirstCoordinate x y y + planarSecondCoordinate x y y = 1
    rw [planarFirstCoordinate_apply, planarSecondCoordinate_apply, hself, zero_div, zero_add, div_self hd]
  have hstrict (z : ℂ) (hz : z ∈ P.extremePoints ℝ) (hzx : z ≠ x) (hzy : z ≠ y) : L z < 1 := by
    exact extreme_two_ray_coordinate_sum_lt_one (finitePolytope_convex hP) h0 hx hy hz.1
      hx0 hy0 hxy hzx hzy (planar_coordinates_reconstruct hd z) (hout z hz hzx hzy)
  refine ⟨hx, hy, hxy, ?_⟩
  rw [finitePolytope_eq_convexHull_extremePoints hP]
  apply exposes_segment hx hy L 1 hLx hLy
  · intro z hz
    by_cases hzx : z = x
    · simpa [hzx] using hLx.le
    by_cases hzy : z = y
    · simpa [hzy] using hLy.le
    exact (hstrict z hz hzx hzy).le
  · intro z hz heq
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr hzy
    exact False.elim ((ne_of_lt (hstrict z hz hzx hzy)) heq)

theorem sin_nonpos_of_pi_le_of_le_two_pi {t : ℝ}
    (hlo : Real.pi ≤ t) (hhi : t ≤ 2 * Real.pi) : Real.sin t ≤ 0 := by
  have hh := Real.sin_nonneg_of_mem_Icc (x := t - Real.pi)
    (show t - Real.pi ∈ Set.Icc 0 Real.pi by constructor <;> linarith)
  rw [Real.sin_sub_pi] at hh
  linarith

/-- A ray outside an unwrapped angular sector has a nonpositive oriented
area against at least one bounding ray. -/
theorem sine_outside_principal_interval {a b t : ℝ}
    (ha : -Real.pi < a) (hb : b ≤ Real.pi)
    (htlo : -Real.pi < t) (hthi : t ≤ Real.pi) (hab : a < b)
    (hout : t ≤ a ∨ b ≤ t) : Real.sin (b - t) ≤ 0 ∨ Real.sin (t - a) ≤ 0 := by
  rcases hout with hleft | hright
  · by_cases hlo : -Real.pi ≤ t - a
    · exact Or.inr (Real.sin_nonpos_of_nonnpos_of_neg_pi_le (by linarith) hlo)
    · exact Or.inl (sin_nonpos_of_pi_le_of_le_two_pi (by linarith) (by linarith))
  · by_cases hlo : -Real.pi ≤ b - t
    · exact Or.inl (Real.sin_nonpos_of_nonnpos_of_neg_pi_le (by linarith) hlo)
    · exact Or.inr (sin_nonpos_of_pi_le_of_le_two_pi (by linarith) (by linarith))

/-- Consecutive distinct arguments inside the principal range expose an
actual edge; the strict gap bound is proved from the interior origin. -/
theorem planar_edge_of_angular_successors {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) {x y : ℂ}
    (hx : x ∈ P.extremePoints ℝ) (hy : y ∈ P.extremePoints ℝ)
    (harg : x.arg < y.arg)
    (hgap : ∀ z ∈ P.extremePoints ℝ, z.arg ≤ x.arg ∨ y.arg ≤ z.arg) : Edge P x y := by
  have hx0 : x ≠ 0 := fun h => planar_origin_not_extreme h0 (h ▸ hx)
  have hy0 : y ≠ 0 := fun h => planar_origin_not_extreme h0 (h ▸ hy)
  have hpi := planar_empty_angular_interval_lt_pi hP h0 x.arg y.arg
    (Complex.neg_pi_lt_arg x) (Complex.arg_le_pi y) hgap
  have hd : 0 < planarDet x y := by
    rw [planarDet_eq_norm_sin]
    exact mul_pos (mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0))
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr harg) hpi)
  apply planar_edge_of_ray_coordinates hP (interior_subset h0) hx hy hx0 hy0 hd.ne'
  intro z hz _ _
  have hs := sine_outside_principal_interval (Complex.neg_pi_lt_arg x) (Complex.arg_le_pi y)
    (Complex.neg_pi_lt_arg z) (Complex.arg_le_pi z) harg (hgap z hz)
  rcases hs with hs | hs
  · left
    rw [planarFirstCoordinate_apply, planarDet_eq_norm_sin z y]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (norm_nonneg z) (norm_nonneg y)) hs) hd.le
  · right
    rw [planarSecondCoordinate_apply, planarDet_eq_norm_sin x z]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (norm_nonneg x) (norm_nonneg z)) hs) hd.le

/-- The last and first arguments also expose an actual edge. The gap
across the branch cut is derived from the polygon's angular spread. -/
theorem planar_edge_of_angular_extremes {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) {x y : ℂ}
    (hx : x ∈ P.extremePoints ℝ) (hy : y ∈ P.extremePoints ℝ)
    (hbounds : ∀ z ∈ P.extremePoints ℝ, y.arg ≤ z.arg ∧ z.arg ≤ x.arg) : Edge P x y := by
  have hx0 : x ≠ 0 := fun h => planar_origin_not_extreme h0 (h ▸ hx)
  have hy0 : y ≠ 0 := fun h => planar_origin_not_extreme h0 (h ▸ hy)
  have hspread := planar_angular_spread_gt_pi hP h0 y.arg x.arg hbounds
  have hfull : x.arg - y.arg < 2 * Real.pi := by
    linarith [Complex.arg_le_pi x, Complex.neg_pi_lt_arg y]
  have hd : 0 < planarDet x y := by
    rw [planarDet_eq_norm_sin]
    apply mul_pos (mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0))
    have hh := Real.sin_pos_of_pos_of_lt_pi (x := y.arg - x.arg + 2 * Real.pi)
      (by linarith) (by linarith)
    simpa only [Real.sin_add_two_pi] using hh
  apply planar_edge_of_ray_coordinates hP (interior_subset h0) hx hy hx0 hy0 hd.ne'
  intro z hz _ _
  obtain ⟨hzlo, hzhi⟩ := hbounds z hz
  by_cases hnear : z.arg - y.arg ≤ Real.pi
  · left
    rw [planarFirstCoordinate_apply, planarDet_eq_norm_sin z y]
    apply div_nonpos_of_nonpos_of_nonneg _ hd.le
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (norm_nonneg z) (norm_nonneg y))
      (Real.sin_nonpos_of_nonnpos_of_neg_pi_le (by linarith) (by linarith))
  · right
    rw [planarSecondCoordinate_apply, planarDet_eq_norm_sin x z]
    apply div_nonpos_of_nonpos_of_nonneg _ hd.le
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (norm_nonneg x) (norm_nonneg z))
      (Real.sin_nonpos_of_nonnpos_of_neg_pi_le (by linarith) (by linarith))

/-- The polygon itself supplies a cyclic enumeration of all actual
vertices whose consecutive segments are actual exposed edges and whose
actual Euclidean ray angles satisfy the full spherical-fan data. -/
theorem exists_planar_edge_ray_fan {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) :
    ∃ u : ℕ → ℂ,
      (u '' Set.Iio (vertices P hP).card = P.extremePoints ℝ) ∧
      (Set.InjOn u (Set.Iio (vertices P hP).card)) ∧
      u (vertices P hP).card = u 0 ∧
      (∀ i ≤ (vertices P hP).card, u i ≠ 0) ∧
      (∀ i < (vertices P hP).card, Edge P (u i) (u (i + 1))) ∧
      Nonempty (SphericalFanData (vertices P hP).card
        (fun i => InnerProductGeometry.angle (u i) (u (i + 1)))) := by
  let n := (vertices P hP).card
  have hn : 0 < n := Finset.card_pos.mpr (vertices_nonempty hP)
  obtain ⟨v, a, hrange, hinj, ha, hgap, hwind, _⟩ := exists_planar_angular_lift hP h0
  have hmonoA : StrictMono (fun i : Fin (n + 1) => a i) :=
    Fin.strictMono_iff_lt_succ.mpr (fun i => sub_pos.mp (hgap i i.2).1)
  have hvmono : StrictMono (fun i => (v i).arg) := by
    intro i j hij
    change (v i).arg < (v j).arg
    rw [← ha i, ← ha j]
    exact hmonoA (show i.castSucc < j.castSucc from hij)
  let u : ℕ → ℂ := fun i => if hi : i < n then v ⟨i, hi⟩ else v ⟨0, hn⟩
  have hu (i : Fin n) : u i = v i := dif_pos i.2
  have hucyclic : u n = u 0 := by simp only [u, dif_neg (lt_irrefl n), dif_pos hn]
  have hune (i : ℕ) (hi : i ≤ n) : u i ≠ 0 := by
    have hui : u i ∈ P.extremePoints ℝ := by
      rw [← hrange]
      by_cases hi' : i < n
      · exact ⟨⟨i, hi'⟩, (hu ⟨i, hi'⟩).symm⟩
      · have heq : i = n := by omega
        rw [heq, hucyclic, hu ⟨0, hn⟩]
        exact mem_range_self _
    exact fun heq => planar_origin_not_extreme h0 (heq ▸ hui)
  have harg (i : ℕ) (hi : i ≤ n) : ((u i).arg : Real.Angle) = (a i : Real.Angle) := by
    by_cases hi' : i < n
    · rw [hu ⟨i, hi'⟩, ha ⟨i, hi'⟩]
    · have heq : i = n := by omega
      rw [heq, hucyclic, hu ⟨0, hn⟩, hwind, ha ⟨0, hn⟩]
      simp
  have hv (i : Fin n) : v i ∈ P.extremePoints ℝ := by
    rw [← hrange]
    exact mem_range_self i
  have hedges (i : ℕ) (hi : i < n) : Edge P (u i) (u (i + 1)) := by
    by_cases hnext : i + 1 < n
    · rw [hu ⟨i, hi⟩, hu ⟨i+1, hnext⟩]
      apply planar_edge_of_angular_successors hP h0
        (hv ⟨i, hi⟩) (hv ⟨i+1, hnext⟩)
        (hvmono (show (⟨i, hi⟩ : Fin n) < ⟨i+1, hnext⟩ by simp))
      intro z hz
      obtain ⟨j, rfl⟩ := hrange.symm ▸ hz
      by_cases hj : j.val ≤ i
      · exact Or.inl (hvmono.monotone (show j ≤ ⟨i, hi⟩ from hj))
      · exact Or.inr (hvmono.monotone (show (⟨i+1, hnext⟩ : Fin n) ≤ j by
          change i + 1 ≤ j.val; omega))
    · have hlast : i + 1 = n := by omega
      rw [hlast, hucyclic, hu ⟨i, hi⟩, hu ⟨0, hn⟩]
      apply planar_edge_of_angular_extremes hP h0
        (hv ⟨i, hi⟩) (hv ⟨0, hn⟩)
      intro z hz
      obtain ⟨j, rfl⟩ := hrange.symm ▸ hz
      exact ⟨hvmono.monotone (show (⟨0, hn⟩ : Fin n) ≤ j from Nat.zero_le _),
        hvmono.monotone (show j ≤ ⟨i, hi⟩ by change j.val ≤ i; omega)⟩
  refine ⟨u, ?_, ?_, hucyclic, hune, hedges, ⟨{
    lift := a
    gap := ?_
    gap_pos := fun i hi => (hgap i hi).1
    gap_lt_pi := fun i hi => (hgap i hi).2
    winding := hwind }⟩⟩
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hu ⟨i, hi⟩, ← hrange]
      exact mem_range_self _
    · intro hx
      obtain ⟨i, rfl⟩ := hrange.symm ▸ hx
      exact ⟨i, i.2, hu i⟩
  · intro i hi j hj heq
    have hh : (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩ := hinj (by rwa [hu ⟨i, hi⟩, hu ⟨j, hj⟩] at heq)
    exact congrArg Fin.val hh
  · intro i hi
    exact planar_angle_eq_lift_gap (hune i (by omega)) (hune (i+1) (by omega))
      (harg i (by omega)) (harg (i+1) (by omega)) (hgap i hi).1.le (hgap i hi).2.le


/-- Full intrinsic planar dimension and an interior origin suffice for
the complete cyclic edge fan, including all actual incidence and angles. -/
theorem exists_planar_intrinsic_edge_ray_fan {P : Set ℂ} (hP : FinitePolytope P)
    (hd : affineDimension P = 2) (h0 : (0 : ℂ) ∈ intrinsicInterior ℝ P) :
    ∃ u : ℕ → ℂ,
      (u '' Set.Iio (vertices P hP).card = P.extremePoints ℝ) ∧
      (Set.InjOn u (Set.Iio (vertices P hP).card)) ∧
      u (vertices P hP).card = u 0 ∧
      (∀ i ≤ (vertices P hP).card, u i ≠ 0) ∧
      (∀ i < (vertices P hP).card, Edge P (u i) (u (i + 1))) ∧
      Nonempty (SphericalFanData (vertices P hP).card
        (fun i => InnerProductGeometry.angle (u i) (u (i + 1)))) := by
  have hdir : (affineSpan ℝ P).direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Complex.finrank_real_complex] using hd
  have hfull : affineSpan ℝ P = ⊤ := by
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty ?_).mp hdir
    obtain ⟨x, hx⟩ := finitePolytope_nonempty hP
    exact ⟨x, subset_affineSpan ℝ P hx⟩
  rw [intrinsicInterior_eq_interior_of_full_span hfull] at h0
  exact exists_planar_edge_ray_fan hP h0

end Uniform5.Composition
