import Uniform5.CompositionCenteredModel
import Uniform5.CompositionRelativeFaces
import Uniform5.Closure
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Angle
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Complex.FiniteDimensional

/-! Angular ordering of genuine vertices around an interior origin. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An interior origin allows a positive, sufficiently small multiple of
any prescribed direction. -/
theorem origin_interior_small_multiple {P : Set E} (h0 : (0 : E) ∈ interior P) (x : E) :
    ∃ t : ℝ, 0 < t ∧ t • x ∈ P := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  let t := ε / (2 * (‖x‖ + 1))
  have ht : 0 < t := div_pos hε (by positivity)
  refine ⟨t, ht, hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  change ε / (2 * (‖x‖ + 1)) * ‖x‖ < ε
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (show 0 < 2 * (‖x‖ + 1) by positivity)).mpr
  nlinarith [norm_nonneg x]

/-- No nonzero linear functional can be nonpositive on a set containing
an interior neighborhood of the origin. -/
theorem origin_interior_linear_nonpositive {P : Set E} (h0 : (0 : E) ∈ interior P)
    (L : E →ₗ[ℝ] ℝ) (hL : ∀ x ∈ P, L x ≤ 0) : L = 0 := by
  have hnonpos (x : E) : L x ≤ 0 := by
    obtain ⟨t, ht, hx⟩ := origin_interior_small_multiple h0 x
    have hh := hL _ hx
    rw [map_smul, smul_eq_mul] at hh
    nlinarith
  ext x
  have hp := hnonpos x
  have hn := hnonpos (-x)
  simp only [map_neg] at hn
  change L x = 0
  linarith

/-- Actual finite-polytope vertices meet the positive side of every
nonzero linear functional when the origin is interior. -/
theorem origin_interior_vertex_positive {P : Set E} (hP : FinitePolytope P)
    (h0 : (0 : E) ∈ interior P) (L : E →ₗ[ℝ] ℝ) (hne : L ≠ 0) :
    ∃ x ∈ P.extremePoints ℝ, 0 < L x := by
  by_contra hn
  push_neg at hn
  apply hne
  apply origin_interior_linear_nonpositive h0 L
  have hh : convexHull ℝ (P.extremePoints ℝ) ⊆ {x | L x ≤ 0} :=
    convexHull_min hn (convex_halfSpace_le L.isLinear 0)
  rwa [← finitePolytope_eq_convexHull_extremePoints hP] at hh

/-- The interior origin is not an actual polygon vertex. -/
theorem planar_origin_not_extreme {P : Set ℂ} (h0 : (0 : ℂ) ∈ interior P) :
    (0 : ℂ) ∉ P.extremePoints ℝ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  let z : ℂ := (ε / 2 : ℝ)
  have hz0 : z ≠ 0 := by
    change (↑(ε / 2) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (half_pos hε))
  have hz : z ∈ P := hball (by
    simp only [Metric.mem_ball, dist_zero_right, z, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith)
  have hnz : -z ∈ P := hball (by
    simp only [Metric.mem_ball, dist_zero_right, norm_neg, z, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith)
  intro he
  have hm : (0 : ℂ) ∈ segment ℝ z (-z) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp
  have hh := (mem_extremePoints_iff_forall_segment.mp he).2 z hz (-z) hnz hm
  rcases hh with hh | hh
  · exact hz0 hh
  · exact hz0 (neg_eq_zero.mp hh)

/-- Distinct nonzero actual vertices of a convex set containing the origin
cannot have the same complex argument. -/
theorem planar_arg_injective_extreme {P : Set ℂ} (h0 : (0 : ℂ) ∈ P)
    (hne : (0 : ℂ) ∉ P.extremePoints ℝ) : Set.InjOn Complex.arg (P.extremePoints ℝ) := by
  have step {x y : ℂ} (hx : x ∈ P.extremePoints ℝ) (hy : y ∈ P.extremePoints ℝ)
      (ha : x.arg = y.arg) (hle : ‖x‖ ≤ ‖y‖) : x = y := by
    have hx0 : x ≠ 0 := fun h => hne (h ▸ hx)
    have hy0 : y ≠ 0 := fun h => hne (h ▸ hy)
    have hypos := norm_pos_iff.mpr hy0
    have hratio : x = (‖x‖ / ‖y‖) • y := by
      have hh := (Complex.arg_eq_arg_iff hy0 hx0).mp ha.symm
      simpa only [Complex.real_smul, Complex.ofReal_div] using hh.symm
    have hseg : x ∈ segment ℝ (0 : ℂ) y := by
      refine ⟨1 - ‖x‖ / ‖y‖, ‖x‖ / ‖y‖,
        sub_nonneg.mpr ((div_le_one hypos).mpr hle), div_nonneg (norm_nonneg _) hypos.le,
        by ring, ?_⟩
      simpa only [smul_zero, zero_add] using hratio.symm
    have hh := (mem_extremePoints_iff_forall_segment.mp hx).2 0 h0 y hy.1 hseg
    exact (hh.resolve_left hx0.symm).symm
  intro x hx y hy ha
  rcases le_total ‖x‖ ‖y‖ with hle | hle
  · exact step hx hy ha hle
  · exact (step hy hx ha.symm hle).symm

/-- The actual vertices of an arbitrary finite polygon around an interior
origin have a strictly increasing angular enumeration. -/
theorem exists_planar_angular_enumeration {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) :
    ∃ v : Fin (vertices P hP).card → ℂ,
      Set.range v = P.extremePoints ℝ ∧ Function.Injective v ∧
      StrictMono (fun i => Complex.arg (v i)) := by
  let V := vertices P hP
  let A := V.image Complex.arg
  have hinj := planar_arg_injective_extreme (interior_subset h0) (planar_origin_not_extreme h0)
  have hcard : A.card = V.card := Finset.card_image_of_injOn (by
    intro x hx y hy ha
    exact hinj ((mem_vertices hP x).mp hx) ((mem_vertices hP y).mp hy) ha)
  have hex (i : Fin V.card) : ∃ x ∈ V, Complex.arg x = A.orderEmbOfFin hcard i :=
    Finset.mem_image.mp (A.orderEmbOfFin_mem hcard i)
  choose v hv ha using hex
  refine ⟨v, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (mem_vertices hP _).mp (hv i)
    · intro hx
      have hxA : Complex.arg x ∈ A := Finset.mem_image.mpr
        ⟨x, (mem_vertices hP x).mpr hx, rfl⟩
      let i := (A.orderIsoOfFin hcard).symm ⟨Complex.arg x, hxA⟩
      refine ⟨i, hinj ((mem_vertices hP _).mp (hv i)) hx ?_⟩
      rw [ha]
      exact congrArg Subtype.val ((A.orderIsoOfFin hcard).apply_symm_apply ⟨Complex.arg x, hxA⟩)
  · intro i j hij
    apply (A.orderEmbOfFin hcard).injective
    rw [← ha, ← ha, hij]
  · intro i j hij
    change Complex.arg (v i) < Complex.arg (v j)
    rw [ha, ha]
    exact (A.orderEmbOfFin hcard).strictMono hij

/-- Oriented area against the unit ray at angle `a`. -/
noncomputable def planarRayFunctional (a : ℝ) : ℂ →ₗ[ℝ] ℝ :=
  Real.cos a • Complex.imLm - Real.sin a • Complex.reLm

@[simp] theorem planarRayFunctional_apply (a : ℝ) (z : ℂ) :
    planarRayFunctional a z = Real.cos a * z.im - Real.sin a * z.re := rfl

theorem planarRayFunctional_eq_norm_sin (a : ℝ) (z : ℂ) :
    planarRayFunctional a z = ‖z‖ * Real.sin (z.arg - a) := by
  rw [Real.sin_sub]
  rw [planarRayFunctional_apply, ← Complex.norm_mul_sin_arg z, ← Complex.norm_mul_cos_arg z]
  ring

theorem planarRayFunctional_ne_zero (a : ℝ) : planarRayFunctional a ≠ 0 := by
  intro h
  have hh := LinearMap.congr_fun h ((-Real.sin a : ℝ) + (Real.cos a : ℝ) * Complex.I)
  simp only [planarRayFunctional_apply, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
    Complex.add_re, Complex.mul_re, sub_zero, LinearMap.zero_apply] at hh
  nlinarith [Real.sin_sq_add_cos_sq a]

/-- A polygon surrounding zero cannot leave an empty angular interval
of width at least pi between two rays in the principal argument range. -/
theorem planar_empty_angular_interval_lt_pi {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) (a b : ℝ) (ha : -Real.pi < a) (hb : b ≤ Real.pi)
    (hgap : ∀ x ∈ P.extremePoints ℝ, x.arg ≤ a ∨ b ≤ x.arg) : b - a < Real.pi := by
  by_contra hn
  have hwide : Real.pi ≤ b - a := le_of_not_gt hn
  obtain ⟨x, hx, hpos⟩ := origin_interior_vertex_positive hP h0
    (planarRayFunctional a) (planarRayFunctional_ne_zero a)
  have hs : Real.sin (x.arg - a) ≤ 0 := by
    rcases hgap x hx with hleft | hright
    · apply Real.sin_nonpos_of_nonnpos_of_neg_pi_le
      · linarith
      · have hh := Complex.neg_pi_lt_arg x; linarith
    · have hh := Real.sin_nonneg_of_mem_Icc (x := x.arg - a - Real.pi)
        (show x.arg - a - Real.pi ∈ Set.Icc 0 Real.pi by
          constructor <;> linarith [Complex.arg_le_pi x])
      rw [Real.sin_sub_pi] at hh
      linarith
  rw [planarRayFunctional_eq_norm_sin] at hpos
  have hh := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg x) hs
  linarith

/-- The angular spread of all actual vertices exceeds pi; otherwise a
closed halfplane through the interior origin would contain the polygon. -/
theorem planar_angular_spread_gt_pi {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) (a b : ℝ)
    (hbounds : ∀ x ∈ P.extremePoints ℝ, a ≤ x.arg ∧ x.arg ≤ b) : Real.pi < b - a := by
  by_contra hn
  have hwide : b - a ≤ Real.pi := le_of_not_gt hn
  obtain ⟨x, hx, hpos⟩ := origin_interior_vertex_positive hP h0
    (-(planarRayFunctional a)) (neg_ne_zero.mpr (planarRayFunctional_ne_zero a))
  have hs : 0 ≤ Real.sin (x.arg - a) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [(hbounds x hx).1], by linarith [(hbounds x hx).2]⟩
  change -(planarRayFunctional a x) > 0 at hpos
  rw [planarRayFunctional_eq_norm_sin] at hpos
  have hh := mul_nonneg (norm_nonneg x) hs
  linarith

/-- A once-around angular lift is constructed from the polygon itself.
Every gap, including the closing gap, lies strictly between zero and pi,
and their total is exactly one full turn. -/
theorem exists_planar_angular_lift {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) :
    ∃ (v : Fin (vertices P hP).card → ℂ) (a : ℕ → ℝ),
      Set.range v = P.extremePoints ℝ ∧ Function.Injective v ∧
      (∀ i : Fin (vertices P hP).card, a i = Complex.arg (v i)) ∧
      (∀ i < (vertices P hP).card, 0 < a (i + 1) - a i ∧ a (i + 1) - a i < Real.pi) ∧
      a (vertices P hP).card = a 0 + 2 * Real.pi ∧
      ∑ i ∈ Finset.range (vertices P hP).card, (a (i + 1) - a i) = 2 * Real.pi := by
  let n := (vertices P hP).card
  have hn : 0 < n := Finset.card_pos.mpr (vertices_nonempty hP)
  obtain ⟨v, hvrange, hvinj, hvmono⟩ := exists_planar_angular_enumeration hP h0
  let a : ℕ → ℝ := fun i => if hi : i < n then (v ⟨i, hi⟩).arg
    else (v ⟨0, hn⟩).arg + 2 * Real.pi
  have ha (i : Fin n) : a i = (v i).arg := dif_pos i.2
  have hwind : a n = a 0 + 2 * Real.pi := by
    simp only [a, dif_neg (lt_irrefl n), dif_pos hn]
  refine ⟨v, a, hvrange, hvinj, ha, ?_, hwind, ?_⟩
  · intro i hi
    by_cases hnext : i + 1 < n
    · have hai : a i = (v ⟨i, hi⟩).arg := ha ⟨i, hi⟩
      have haj : a (i + 1) = (v ⟨i + 1, hnext⟩).arg := ha ⟨i + 1, hnext⟩
      rw [hai, haj]
      refine ⟨sub_pos.mpr (hvmono (show (⟨i, hi⟩ : Fin n) < ⟨i+1, hnext⟩ by simp)), ?_⟩
      apply planar_empty_angular_interval_lt_pi hP h0 _ _
        (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)
      intro x hx
      obtain ⟨j, rfl⟩ := hvrange.symm ▸ hx
      by_cases hj : j.val ≤ i
      · exact Or.inl (hvmono.monotone (show j ≤ ⟨i, hi⟩ from hj))
      · exact Or.inr (hvmono.monotone (show (⟨i+1, hnext⟩ : Fin n) ≤ j by
          change i + 1 ≤ j.val; omega))
    · have hlast : i + 1 = n := by omega
      have hai : a i = (v ⟨i, hi⟩).arg := ha ⟨i, hi⟩
      have ha0 : a 0 = (v ⟨0, hn⟩).arg := ha ⟨0, hn⟩
      rw [hlast, hwind, hai, ha0]
      refine ⟨by linarith [Complex.neg_pi_lt_arg (v ⟨0, hn⟩), Complex.arg_le_pi (v ⟨i, hi⟩)], ?_⟩
      have hspread := planar_angular_spread_gt_pi hP h0 (v ⟨0, hn⟩).arg (v ⟨i, hi⟩).arg (by
        intro x hx
        obtain ⟨j, rfl⟩ := hvrange.symm ▸ hx
        exact ⟨hvmono.monotone (show (⟨0, hn⟩ : Fin n) ≤ j from Nat.zero_le _),
          hvmono.monotone (show j ≤ ⟨i, hi⟩ by change j.val ≤ i; omega)⟩)
      linarith
  · rw [Finset.sum_range_sub, hwind]
    ring

/-- An angular lift with a gap in `[0,pi]` measures the actual Euclidean
angle between the two nonzero rays. -/
theorem planar_angle_eq_lift_gap {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    {a b : ℝ} (hxa : (x.arg : Real.Angle) = (a : Real.Angle))
    (hyb : (y.arg : Real.Angle) = (b : Real.Angle))
    (hgap0 : 0 ≤ b - a) (hgappi : b - a ≤ Real.pi) :
    InnerProductGeometry.angle x y = b - a := by
  rw [InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg hy hx]
  have he : ((y / x).arg : Real.Angle) = ((b - a : ℝ) : Real.Angle) := by
    rw [Complex.arg_div_coe_angle hy hx, hxa, hyb, Real.Angle.coe_sub]
  have hr := Complex.arg_coe_angle_eq_iff_eq_toReal.mp he
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨by linarith [Real.pi_pos], hgappi⟩] at hr
  rw [hr, abs_of_nonneg hgap0]

/-- A genuine planar polygon containing the origin in its interior supplies
a once-around spherical fan of its actual vertex rays, with its actual
Euclidean consecutive angles. This constructs all angular hypotheses. -/
theorem exists_planar_vertex_ray_fan {P : Set ℂ} (hP : FinitePolytope P)
    (h0 : (0 : ℂ) ∈ interior P) :
    ∃ u : ℕ → ℂ,
      (u '' Set.Iio (vertices P hP).card = P.extremePoints ℝ) ∧
      (Set.InjOn u (Set.Iio (vertices P hP).card)) ∧
      u (vertices P hP).card = u 0 ∧
      (∀ i ≤ (vertices P hP).card, u i ≠ 0) ∧
      Nonempty (SphericalFanData (vertices P hP).card
        (fun i => InnerProductGeometry.angle (u i) (u (i + 1)))) := by
  let n := (vertices P hP).card
  have hn : 0 < n := Finset.card_pos.mpr (vertices_nonempty hP)
  obtain ⟨v, a, hrange, hinj, ha, hgap, hwind, _⟩ := exists_planar_angular_lift hP h0
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
  refine ⟨u, ?_, ?_, hucyclic, hune, ⟨{
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

/-- Full planar dimension turns the relative-interior premise into the
interior premise used by the angular fan construction. -/
theorem exists_planar_intrinsic_vertex_ray_fan {P : Set ℂ} (hP : FinitePolytope P)
    (hd : affineDimension P = 2) (h0 : (0 : ℂ) ∈ intrinsicInterior ℝ P) :
    ∃ u : ℕ → ℂ,
      (u '' Set.Iio (vertices P hP).card = P.extremePoints ℝ) ∧
      (Set.InjOn u (Set.Iio (vertices P hP).card)) ∧
      u (vertices P hP).card = u 0 ∧
      (∀ i ≤ (vertices P hP).card, u i ≠ 0) ∧
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
  exact exists_planar_vertex_ray_fan hP h0

end Uniform5.Composition
