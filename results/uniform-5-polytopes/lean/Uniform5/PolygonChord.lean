import Uniform5.SphereSection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

open scoped RealInnerProductSpace

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The metric part of the regular-polygon chord assertion. The input is the
usual interior angle of a regular `p`-gon at `v`, rather than the desired
chord length. Identifying a polygonal face with this angle data is separate. -/
theorem polygon_neighbor_chord_of_angle {p : ℕ} (hp : 3 ≤ p) {v x y : E}
    (hx : dist x v = 1) (hy : dist y v = 1)
    (hangle : InnerProductGeometry.angle (x - v) (y - v) =
      Real.pi - 2 * (Real.pi / (p : ℝ))) :
    dist x y = 2 * Real.cos (Real.pi / (p : ℝ)) := by
  have hxnorm : ‖x - v‖ = 1 := by simpa only [dist_eq_norm] using hx
  have hynorm : ‖y - v‖ = 1 := by simpa only [dist_eq_norm] using hy
  have hinner := InnerProductGeometry.cos_angle_mul_norm_mul_norm (x - v) (y - v)
  rw [hangle, Real.cos_pi_sub, hxnorm, hynorm, mul_one, mul_one, Real.cos_two_mul] at hinner
  have hsq := norm_sub_sq_real (x - v) (y - v)
  rw [hxnorm, hynorm, sub_sub_sub_cancel_right] at hsq
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hppos : (0 : ℝ) < p := by linarith
  have hlow : -(Real.pi / 2) ≤ Real.pi / (p : ℝ) := by
    have hh := div_nonneg Real.pi_pos.le hppos.le
    linarith [Real.pi_pos]
  have hupp : Real.pi / (p : ℝ) ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  have hcos : 0 ≤ Real.cos (Real.pi / (p : ℝ)) :=
    Real.cos_nonneg_of_mem_Icc ⟨hlow, hupp⟩
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - y)]

/-- The standard equal-spaced circle model of a regular polygon, in the plane
with orthonormal axes `e,f`. Integer indices allow the neighbours of vertex
zero to be written as `1` and `-1`. -/
noncomputable def regularPolygonPoint (c e f : E) (ρ : ℝ) (p : ℕ) (k : ℤ) : E :=
  c + (ρ * Real.cos ((k : ℝ) * (2 * (Real.pi / (p : ℝ))))) • e +
    (ρ * Real.sin ((k : ℝ) * (2 * (Real.pi / (p : ℝ))))) • f

lemma orthonormal_pair_norm_sq {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (horth : ⟪e, f⟫ = 0) (a b : ℝ) :
    ‖a • e + b • f‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right, horth, he, hf]
  ring

/-- The chord between the neighbours in an actual equal-spaced circle model
of a regular `p`-gon, normalized by its side length. No interior-angle
hypothesis is supplied; the chord is computed directly from the coordinates. -/
theorem regularPolygon_neighbor_chord {p : ℕ} (hp : 3 ≤ p) (c e f : E) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0)
    (hunit : dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p 0) = 1) :
    dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p (-1)) =
      2 * Real.cos (Real.pi / (p : ℝ)) := by
  let α := Real.pi / (p : ℝ)
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hppos : (0 : ℝ) < p := by linarith
  have hα0 : 0 ≤ α := div_nonneg Real.pi_pos.le hppos.le
  have hαhalf : α ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  have hsin : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [Real.pi_pos])
  have hcos : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hαhalf⟩
  have hside : regularPolygonPoint c e f ρ p 1 - regularPolygonPoint c e f ρ p 0 =
      (ρ * (Real.cos (2 * α) - 1)) • e + (ρ * Real.sin (2 * α)) • f := by
    simp only [regularPolygonPoint, Int.cast_one, Int.cast_zero, one_mul, zero_mul,
      Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_smul, add_zero]
    dsimp [α]
    module
  have hsidesq : dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p 0) ^ 2 =
      4 * ρ ^ 2 * Real.sin α ^ 2 := by
    rw [dist_eq_norm, hside, orthonormal_pair_norm_sq he hf horth]
    calc
      (ρ * (Real.cos (2 * α) - 1)) ^ 2 + (ρ * Real.sin (2 * α)) ^ 2 =
          2 * ρ ^ 2 * (1 - Real.cos (2 * α)) := by
        linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq (2 * α)
      _ = 4 * ρ ^ 2 * Real.sin α ^ 2 := by
        rw [Real.cos_two_mul]
        linear_combination -4 * ρ ^ 2 * Real.sin_sq_add_cos_sq α
  have hscale : 2 * ρ * Real.sin α = 1 := by
    rw [hunit] at hsidesq
    have hh : 0 ≤ 2 * ρ * Real.sin α := by positivity
    nlinarith
  have hchord : regularPolygonPoint c e f ρ p 1 - regularPolygonPoint c e f ρ p (-1) =
      (2 * ρ * Real.sin (2 * α)) • f := by
    simp only [regularPolygonPoint, Int.cast_one, Int.cast_neg, neg_mul, one_mul,
      Real.cos_neg, Real.sin_neg]
    dsimp [α]
    module
  rw [dist_eq_norm, hchord, norm_smul, hf, mul_one, Real.norm_eq_abs, Real.sin_two_mul]
  rw [abs_of_nonneg (by positivity)]
  change 2 * ρ * (2 * Real.sin α * Real.cos α) = 2 * Real.cos α
  nlinarith [congrArg (fun t : ℝ => t * (2 * Real.cos α)) hscale]

/-- Squared distances in the circle model are computed from the difference
of the indices; in particular all consecutive side lengths are equal. -/
theorem regularPolygonPoint_dist_sq (c e f : E) (ρ : ℝ) (p : ℕ)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0) (k l : ℤ) :
    dist (regularPolygonPoint c e f ρ p k) (regularPolygonPoint c e f ρ p l) ^ 2 =
      2 * ρ ^ 2 * (1 - Real.cos (((k : ℝ) - (l : ℝ)) * (2 * (Real.pi / (p : ℝ))))) := by
  let t := 2 * (Real.pi / (p : ℝ))
  have hdiff : regularPolygonPoint c e f ρ p k - regularPolygonPoint c e f ρ p l =
      (ρ * (Real.cos ((k : ℝ) * t) - Real.cos ((l : ℝ) * t))) • e +
      (ρ * (Real.sin ((k : ℝ) * t) - Real.sin ((l : ℝ) * t))) • f := by
    dsimp [regularPolygonPoint, t]
    module
  rw [dist_eq_norm, hdiff, orthonormal_pair_norm_sq he hf horth]
  change _ = 2 * ρ ^ 2 * (1 - Real.cos (((k : ℝ) - (l : ℝ)) * t))
  rw [sub_mul, Real.cos_sub]
  linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq ((k : ℝ) * t) +
    ρ ^ 2 * Real.sin_sq_add_cos_sq ((l : ℝ) * t)

/-- Unit length at one side normalizes every side of the explicit polygon. -/
theorem regularPolygonPoint_unit_sides (c e f : E) (ρ : ℝ) (p : ℕ)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0)
    (hunit : dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p 0) = 1)
    (k : ℤ) :
    dist (regularPolygonPoint c e f ρ p (k + 1)) (regularPolygonPoint c e f ρ p k) = 1 := by
  have hside := regularPolygonPoint_dist_sq c e f ρ p he hf horth 1 0
  have hnext := regularPolygonPoint_dist_sq c e f ρ p he hf horth (k + 1) k
  rw [hunit] at hside
  simp only [Int.cast_one, Int.cast_zero, Int.cast_add, add_sub_cancel_left, add_sub_cancel_right, sub_zero, one_mul] at hside hnext
  nlinarith [dist_nonneg (x := regularPolygonPoint c e f ρ p (k + 1))
    (y := regularPolygonPoint c e f ρ p k)]

/-- One complete turn gives period `p` in the equal-spaced circle model. -/
theorem regularPolygonPoint_periodic (c e f : E) (ρ : ℝ) {p : ℕ} (hp : 0 < p) (k : ℤ) :
    regularPolygonPoint c e f ρ p (k + (p : ℤ)) = regularPolygonPoint c e f ρ p k := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hangle : ((k + (p : ℤ) : ℤ) : ℝ) * (2 * (Real.pi / (p : ℝ))) =
      (k : ℝ) * (2 * (Real.pi / (p : ℝ))) + 2 * Real.pi := by
    push_cast
    field_simp [hpR]
    ring
  simp only [regularPolygonPoint, hangle, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Distinct indices in one turn give distinct vertices when the radius is
positive. Thus this is an actual `p`-vertex model, not a possibly collapsed cycle. -/
theorem regularPolygonPoint_injective_fin (c e f : E) {ρ : ℝ} (hρ : 0 < ρ)
    {p : ℕ} (hp : 0 < p) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0) :
    Function.Injective (fun k : Fin p => regularPolygonPoint c e f ρ p (k.val : ℤ)) := by
  intro k l heq
  have hsq := regularPolygonPoint_dist_sq c e f ρ p he hf horth (k.val : ℤ) (l.val : ℤ)
  change regularPolygonPoint c e f ρ p (k.val : ℤ) = regularPolygonPoint c e f ρ p (l.val : ℤ) at heq
  rw [heq, dist_self] at hsq
  have hcos : Real.cos (((k.val : ℝ) - (l.val : ℝ)) * (2 * (Real.pi / (p : ℝ)))) = 1 := by
    push_cast at hsq
    nlinarith [sq_pos_of_pos hρ]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hk0 : (0 : ℝ) ≤ k.val := by positivity
  have hl0 : (0 : ℝ) ≤ l.val := by positivity
  have hkp : (k.val : ℝ) < p := by exact_mod_cast k.isLt
  have hlp : (l.val : ℝ) < p := by exact_mod_cast l.isLt
  have hratioL : (-1 : ℝ) < ((k.val : ℝ) - (l.val : ℝ)) / (p : ℝ) := by
    rw [lt_div_iff₀ hpR]
    linarith
  have hratioU : ((k.val : ℝ) - (l.val : ℝ)) / (p : ℝ) < 1 := by
    rw [div_lt_iff₀ hpR]
    linarith
  have hprod : ((k.val : ℝ) - (l.val : ℝ)) * (2 * (Real.pi / (p : ℝ))) =
      (2 * Real.pi) * (((k.val : ℝ) - (l.val : ℝ)) / (p : ℝ)) := by ring
  have htL : -(2 * Real.pi) <
      ((k.val : ℝ) - (l.val : ℝ)) * (2 * (Real.pi / (p : ℝ))) := by
    rw [hprod]
    have hh := mul_lt_mul_of_pos_left hratioL (show 0 < 2 * Real.pi by positivity)
    nlinarith
  have htU : ((k.val : ℝ) - (l.val : ℝ)) * (2 * (Real.pi / (p : ℝ))) < 2 * Real.pi := by
    rw [hprod]
    have hh := mul_lt_mul_of_pos_left hratioU (show 0 < 2 * Real.pi by positivity)
    nlinarith
  have hθ := (Real.cos_eq_one_iff_of_lt_of_lt htL htU).mp hcos
  have hdiff : (k.val : ℝ) = (l.val : ℝ) := by
    have hα : 0 < 2 * (Real.pi / (p : ℝ)) := by positivity
    nlinarith
  apply Fin.ext
  exact_mod_cast hdiff

/-- The finite vertex set of the concrete equal-spaced circle polygon. -/
noncomputable def regularPolygonVertices (c e f : E) (ρ : ℝ) (p : ℕ) : Finset E :=
  by
    classical
    exact (Finset.univ : Finset (Fin p)).image (fun k => regularPolygonPoint c e f ρ p (k.val : ℤ))

/-- The concrete polygon has exactly the specified number of vertices. -/
theorem regularPolygonVertices_card (c e f : E) {ρ : ℝ} (hρ : 0 < ρ)
    {p : ℕ} (hp : 0 < p) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0) :
    (regularPolygonVertices c e f ρ p).card = p := by
  classical
  rw [regularPolygonVertices, Finset.card_image_of_injective _
    (regularPolygonPoint_injective_fin c e f hρ hp he hf horth)]
  simp

/-- The model is inscribed in its specified circle. -/
theorem regularPolygonPoint_on_sphere (c e f : E) {ρ : ℝ} (hρ : 0 ≤ ρ) (p : ℕ)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0) (k : ℤ) :
    dist (regularPolygonPoint c e f ρ p k) c = ρ := by
  let θ := (k : ℝ) * (2 * (Real.pi / (p : ℝ)))
  have hdiff : regularPolygonPoint c e f ρ p k - c =
      (ρ * Real.cos θ) • e + (ρ * Real.sin θ) • f := by
    dsimp [regularPolygonPoint, θ]
    module
  rw [dist_eq_norm, hdiff]
  have hh := orthonormal_pair_norm_sq he hf horth (ρ * Real.cos θ) (ρ * Real.sin θ)
  have hsq : ‖(ρ * Real.cos θ) • e + (ρ * Real.sin θ) • f‖ ^ 2 = ρ ^ 2 := by
    rw [hh]
    linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq θ
  nlinarith [norm_nonneg ((ρ * Real.cos θ) • e + (ρ * Real.sin θ) • f)]

/-- The chosen vertex and its two cyclic neighbours belong to the finite
polygon model, including the neighbour with integer index `-1`. -/
theorem regularPolygon_neighbor_mem (c e f : E) (ρ : ℝ) {p : ℕ} (hp : 3 ≤ p) :
    regularPolygonPoint c e f ρ p 0 ∈ regularPolygonVertices c e f ρ p ∧
    regularPolygonPoint c e f ρ p 1 ∈ regularPolygonVertices c e f ρ p ∧
    regularPolygonPoint c e f ρ p (-1) ∈ regularPolygonVertices c e f ρ p := by
  classical
  have hp0 : 0 < p := by omega
  have hmem (k : Fin p) : regularPolygonPoint c e f ρ p (k.val : ℤ) ∈
      regularPolygonVertices c e f ρ p := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  refine ⟨hmem ⟨0, hp0⟩, hmem ⟨1, by omega⟩, ?_⟩
  have hlast := hmem ⟨p - 1, by omega⟩
  have hcast : ((p - 1 : ℕ) : ℤ) = -1 + (p : ℤ) := by omega
  change regularPolygonPoint c e f ρ p ((p - 1 : ℕ) : ℤ) ∈ _ at hlast
  rw [hcast, regularPolygonPoint_periodic c e f ρ hp0 (-1)] at hlast
  exact hlast

/-- An explicit unit regular `p`-gon model, with exactly `p` vertices on its
circle, all cyclic sides unit, and the vertex-figure chord formula. -/
theorem regularPolygon_unit_model {p : ℕ} (hp : 3 ≤ p) (c e f : E) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0)
    (hunit : dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p 0) = 1) :
    (regularPolygonVertices c e f ρ p).card = p ∧
    (∀ k : ℤ, dist (regularPolygonPoint c e f ρ p k) c = ρ) ∧
    (∀ k : ℤ, dist (regularPolygonPoint c e f ρ p (k + 1)) (regularPolygonPoint c e f ρ p k) = 1) ∧
    (regularPolygonPoint c e f ρ p 0 ∈ regularPolygonVertices c e f ρ p ∧
      regularPolygonPoint c e f ρ p 1 ∈ regularPolygonVertices c e f ρ p ∧
      regularPolygonPoint c e f ρ p (-1) ∈ regularPolygonVertices c e f ρ p) ∧
    dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p (-1)) =
      2 * Real.cos (Real.pi / (p : ℝ)) := by
  have hρne : ρ ≠ 0 := by
    intro hh
    simp [hh, regularPolygonPoint] at hunit
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ hρne.symm
  exact ⟨regularPolygonVertices_card c e f hρpos (by omega) he hf horth,
    regularPolygonPoint_on_sphere c e f hρ p he hf horth,
    regularPolygonPoint_unit_sides c e f ρ p he hf horth hunit,
    regularPolygon_neighbor_mem c e f ρ hp,
    regularPolygon_neighbor_chord hp c e f hρ he hf horth hunit⟩

/-- The two supporting-ray inequalities for the cyclic angles between the
first and last nonzero samples. They follow from nonnegative half-angle sines. -/
lemma polygon_halfangle_cone {α β : ℝ} (hα : 0 ≤ α) (hβL : α ≤ β)
    (hβU : β ≤ Real.pi - α) :
    0 ≤ Real.sin (2 * α) * (1 - Real.cos (2 * β)) +
      Real.sin (2 * β) * (1 - Real.cos (2 * α)) ∧
    0 ≤ Real.sin (2 * α) * (1 - Real.cos (2 * β)) -
      Real.sin (2 * β) * (1 - Real.cos (2 * α)) := by
  have hsα : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα (by linarith)
  have hsβ : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsadd : 0 ≤ Real.sin (β + α) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hssub : 0 ≤ Real.sin (β - α) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hdouble (t : ℝ) : 1 - Real.cos (2 * t) = 2 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
  constructor
  · have heq : Real.sin (2 * α) * (1 - Real.cos (2 * β)) +
        Real.sin (2 * β) * (1 - Real.cos (2 * α)) =
        4 * Real.sin α * Real.sin β * Real.sin (β + α) := by
      rw [hdouble β, hdouble α, Real.sin_two_mul, Real.sin_two_mul, Real.sin_add]
      ring
    rw [heq]
    positivity
  · have heq : Real.sin (2 * α) * (1 - Real.cos (2 * β)) -
        Real.sin (2 * β) * (1 - Real.cos (2 * α)) =
        4 * Real.sin α * Real.sin β * Real.sin (β - α) := by
      rw [hdouble β, hdouble α, Real.sin_two_mul, Real.sin_two_mul, Real.sin_sub]
      ring
    rw [heq]
    positivity

/-- Level and positive-ray identities need only distinct points on the common
sphere; membership in the section's hull is supplied separately below. -/
lemma sphericalRayPoint_level_rep {v x : E} {ρ : ℝ} (hv : ‖v‖ = ρ) (hx : ‖x‖ = ρ)
    (hxv : x ≠ v) :
    sphericalRayPoint v x ρ ∈ figureHyperplane v ρ ∧
      ∃ a : ℝ, 0 < a ∧ x = v + a • (sphericalRayPoint v x ρ - v) := by
  let a := 2 * (ρ ^ 2 - ⟪x, v⟫)
  have hch := sphere_chord_sq hx hv
  have hn : 0 < ‖x - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxv)
  have ha : 0 < a := by dsimp [a]; nlinarith
  refine ⟨?_, a, ha, ?_⟩
  · change ⟪v + a⁻¹ • (x - v), v⟫ = ρ ^ 2 - 1 / 2
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq, hv]
    have haeq : a = 2 * (ρ ^ 2 - ⟪x, v⟫) := rfl
    field_simp
    nlinarith
  · change x = v + a • (v + a⁻¹ • (x - v) - v)
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    abel

/-- A unit chord endpoint is fixed by the normalized-ray map. -/
lemma sphericalRayPoint_eq_of_unit {v x : E} {ρ : ℝ} (hv : ‖v‖ = ρ) (hx : ‖x‖ = ρ)
    (hunit : dist x v = 1) : sphericalRayPoint v x ρ = x := by
  have hch := sphere_chord_sq hx hv
  rw [dist_eq_norm] at hunit
  have ha : 2 * (ρ ^ 2 - ⟪x, v⟫) = 1 := by nlinarith
  unfold sphericalRayPoint
  rw [ha]
  simp

/-- Every non-apex normalized ray of the concrete polygon meets the segment
between its two cyclic neighbours. This is the geometric section step, rather
than an assumed identification of the chord with a vertex-figure edge. -/
theorem regularPolygon_ray_mem_segment {p : ℕ} (hp : 3 ≤ p) (e f : E) {ρ : ℝ}
    (hρ : 0 < ρ) (he : ‖e‖ = 1) (horth : ⟪e, f⟫ = 0)
    (hcal : 2 * ρ ^ 2 * (1 - Real.cos (2 * (Real.pi / (p : ℝ)))) = 1)
    {k : ℕ} (hk : 0 < k) (hkp : k < p) :
    sphericalRayPoint (regularPolygonPoint 0 e f ρ p 0) (regularPolygonPoint 0 e f ρ p (k : ℤ)) ρ ∈
      segment ℝ (regularPolygonPoint 0 e f ρ p 1) (regularPolygonPoint 0 e f ρ p (-1)) := by
  let α := Real.pi / (p : ℝ)
  let β := (k : ℝ) * α
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hppos : (0 : ℝ) < p := by linarith
  have hα : 0 < α := div_pos Real.pi_pos hppos
  have hαp : α * (p : ℝ) = Real.pi := by dsimp [α]; field_simp
  have hβL : α ≤ β := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [β]
    nlinarith
  have hβU : β ≤ Real.pi - α := by
    have hkR : (k : ℝ) + 1 ≤ p := by exact_mod_cast hkp
    have hh := mul_le_mul_of_nonneg_right hkR hα.le
    dsimp [β]
    nlinarith
  have hsinβ : 0 < Real.sin β :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hδpos : 0 < Real.sin (2 * α) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by linarith)
    have hh : α < Real.pi / 2 := by
      apply (div_lt_iff₀ hppos).mpr
      nlinarith [Real.pi_pos]
    linarith
  have hdouble : 1 - Real.cos (2 * β) = 2 * Real.sin β ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq β]
  let A := 2 * ρ ^ 2 * (1 - Real.cos (2 * β))
  let d := ρ * Real.sin (2 * α)
  let s := ρ * Real.sin (2 * β) / A
  have hA : 0 < A := by dsimp [A]; rw [hdouble]; positivity
  have hd : 0 < d := mul_pos hρ hδpos
  have hcone := polygon_halfangle_cone hα.le hβL hβU
  have hcal' : 2 * ρ ^ 2 * (1 - Real.cos (2 * α)) = 1 := hcal
  have hupEq : A * d - ρ * Real.sin (2 * β) = 2 * ρ ^ 3 *
      (Real.sin (2 * α) * (1 - Real.cos (2 * β)) -
        Real.sin (2 * β) * (1 - Real.cos (2 * α))) := by
    dsimp [A, d]
    linear_combination (ρ * Real.sin (2 * β)) * hcal'
  have hloEq : A * d + ρ * Real.sin (2 * β) = 2 * ρ ^ 3 *
      (Real.sin (2 * α) * (1 - Real.cos (2 * β)) +
        Real.sin (2 * β) * (1 - Real.cos (2 * α))) := by
    dsimp [A, d]
    linear_combination -(ρ * Real.sin (2 * β)) * hcal'
  have hsu : s ≤ d := by
    apply (div_le_iff₀ hA).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2 * ρ ^ 3 by positivity) hcone.2]
  have hsl : -d ≤ s := by
    apply (le_div_iff₀ hA).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2 * ρ ^ 3 by positivity) hcone.1]
  have hvcoord : regularPolygonPoint (0 : E) e f ρ p 0 = ρ • e := by
    simp [regularPolygonPoint]
  have hxcoord : regularPolygonPoint (0 : E) e f ρ p (k : ℤ) =
      (ρ * Real.cos (2 * β)) • e + (ρ * Real.sin (2 * β)) • f := by
    have ht : ((k : ℤ) : ℝ) * (2 * (Real.pi / (p : ℝ))) = 2 * β := by
      push_cast
      dsimp [β, α]
      ring
    simp only [regularPolygonPoint, ht, zero_add]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm e f, horth]
  have hden : 2 * (ρ ^ 2 - ⟪regularPolygonPoint (0 : E) e f ρ p (k : ℤ),
      regularPolygonPoint (0 : E) e f ρ p 0⟫) = A := by
    rw [hxcoord, hvcoord]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, hee, hfe,
      mul_zero, mul_one, add_zero]
    dsimp [A]
    ring
  have hcoeff : ρ + A⁻¹ * (ρ * Real.cos (2 * β) - ρ) = ρ * Real.cos (2 * α) := by
    field_simp
    dsimp [A]
    linear_combination (ρ * (1 - Real.cos (2 * β))) * hcal'
  have hqcoord : sphericalRayPoint (regularPolygonPoint (0 : E) e f ρ p 0)
      (regularPolygonPoint 0 e f ρ p (k : ℤ)) ρ = (ρ * Real.cos (2 * α)) • e + s • f := by
    rw [sphericalRayPoint, hden, hvcoord, hxcoord]
    calc
      _ = (ρ + A⁻¹ * (ρ * Real.cos (2 * β) - ρ)) • e +
          (A⁻¹ * (ρ * Real.sin (2 * β))) • f := by module
      _ = _ := by rw [hcoeff]; simp only [s, div_eq_inv_mul]
  have hpcoord : regularPolygonPoint (0 : E) e f ρ p 1 =
      (ρ * Real.cos (2 * α)) • e + d • f := by simp [regularPolygonPoint, α, d]
  have hmcoord : regularPolygonPoint (0 : E) e f ρ p (-1) =
      (ρ * Real.cos (2 * α)) • e + (-d) • f := by simp [regularPolygonPoint, α, d]
  let u := (s + d) / (2 * d)
  let w := (d - s) / (2 * d)
  have hu : 0 ≤ u := div_nonneg (by linarith) (by positivity)
  have hw : 0 ≤ w := div_nonneg (by linarith) (by positivity)
  have husum : u + w = 1 := by dsimp [u, w]; field_simp; ring
  have hudiff : (u - w) * d = s := by dsimp [u, w]; field_simp; ring
  refine ⟨u, w, hu, hw, husum, ?_⟩
  rw [hpcoord, hmcoord, hqcoord]
  calc
    _ = ((u + w) * (ρ * Real.cos (2 * α))) • e + ((u - w) * d) • f := by module
    _ = _ := by rw [husum, hudiff, one_mul]

/-- The actual vertex-figure section of the centred equal-spaced circle
polygon is the segment joining the two cyclic neighbours. No section identity,
edge property, or interior-angle datum is assumed. -/
theorem regularPolygon_section_eq_segment {p : ℕ} (hp : 3 ≤ p) (e f : E) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0)
    (hunit : dist (regularPolygonPoint 0 e f ρ p 1) (regularPolygonPoint 0 e f ρ p 0) = 1) :
    convexHull ℝ (regularPolygonVertices (0 : E) e f ρ p : Set E) ∩
        figureHyperplane (regularPolygonPoint 0 e f ρ p 0) ρ =
      segment ℝ (regularPolygonPoint 0 e f ρ p 1) (regularPolygonPoint 0 e f ρ p (-1)) := by
  classical
  let V := regularPolygonVertices (0 : E) e f ρ p
  let v := regularPolygonPoint (0 : E) e f ρ p 0
  let xp := regularPolygonPoint (0 : E) e f ρ p 1
  let xm := regularPolygonPoint (0 : E) e f ρ p (-1)
  let q := fun x => sphericalRayPoint v x ρ
  let L := innerSL ℝ v
  let b := ρ ^ 2 - 1 / 2
  have hρne : ρ ≠ 0 := by intro hh; simp [hh, regularPolygonPoint] at hunit
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ hρne.symm
  have hnorm (k : ℤ) : ‖regularPolygonPoint (0 : E) e f ρ p k‖ = ρ := by
    simpa only [dist_zero_right] using regularPolygonPoint_on_sphere 0 e f hρ p he hf horth k
  have hcal : 2 * ρ ^ 2 * (1 - Real.cos (2 * (Real.pi / (p : ℝ)))) = 1 := by
    have hh := regularPolygonPoint_dist_sq (0 : E) e f ρ p he hf horth 1 0
    rw [hunit] at hh
    simpa only [Int.cast_one, Int.cast_zero, sub_zero, one_mul, one_pow] using hh.symm
  obtain ⟨hv, hxp, hxm⟩ := regularPolygon_neighbor_mem (0 : E) e f ρ hp
  have hnormV : ∀ x ∈ V, ‖x‖ = ρ := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact hnorm k.val
  have hqseg : ∀ x ∈ V.erase v, q x ∈ segment ℝ xp xm := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hx).2
    have hkne : k.val ≠ 0 := by
      intro hk0
      apply (Finset.mem_erase.mp hx).1
      change regularPolygonPoint 0 e f ρ p (k.val : ℤ) = regularPolygonPoint 0 e f ρ p 0
      simp only [hk0, Nat.cast_zero]
    exact regularPolygon_ray_mem_segment hp e f hρpos he horth hcal (Nat.pos_of_ne_zero hkne) k.isLt
  have hLv : L v = ρ ^ 2 := by
    simp only [L, innerSL_apply, real_inner_self_eq_norm_sq, v, hnorm 0]
  have hb : b < L v := by rw [hLv]; dsimp [b]; linarith
  have hqlevel : ∀ x ∈ V.erase v, L (q x) = b := by
    intro x hx
    have hh := (sphericalRayPoint_level_rep (hnorm 0)
      (hnormV x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1).1
    change ⟪q x, v⟫ = b at hh
    change ⟪v, q x⟫ = b
    rw [real_inner_comm (q x) v]
    exact hh
  have hqmem : ∀ x ∈ V.erase v, q x ∈ convexHull ℝ (V : Set E) := by
    intro x hx
    exact segment_subset_convexHull hxp hxm (hqseg x hx)
  have hrep : ∀ x ∈ V.erase v, ∃ a : ℝ, 0 < a ∧ x = v + a • (q x - v) := by
    intro x hx
    exact (sphericalRayPoint_level_rep (hnorm 0)
      (hnormV x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1).2
  have hslic := finite_section_eq_rayHull V L hb q hqlevel hqmem hrep
  have hsets : convexHull ℝ (V : Set E) ∩ figureHyperplane v ρ =
      convexHull ℝ (q '' (↑(V.erase v) : Set E)) := by
    convert hslic using 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, figureHyperplane, L, b, innerSL_apply]
    rw [real_inner_comm v x]
  change convexHull ℝ (V : Set E) ∩ figureHyperplane v ρ = segment ℝ xp xm
  rw [hsets]
  apply le_antisymm
  · apply convexHull_min _ (convex_segment xp xm)
    rintro x ⟨y, hy, rfl⟩
    exact hqseg y hy
  · have hxpUnit : dist xp v = 1 := hunit
    have hxmUnit : dist xm v = 1 := by
      have hh := regularPolygonPoint_unit_sides (0 : E) e f ρ p he hf horth hunit (-1)
      simpa [xm, v, dist_comm] using hh
    have hxpne : xp ≠ v := by intro hh; rw [hh, dist_self] at hxpUnit; norm_num at hxpUnit
    have hxmne : xm ≠ v := by intro hh; rw [hh, dist_self] at hxmUnit; norm_num at hxmUnit
    have hqp : q xp = xp := sphericalRayPoint_eq_of_unit (hnorm 0) (hnorm 1) hxpUnit
    have hqm : q xm = xm := sphericalRayPoint_eq_of_unit (hnorm 0) (hnorm (-1)) hxmUnit
    exact segment_subset_convexHull
      ⟨xp, Finset.mem_erase.mpr ⟨hxpne, hxp⟩, hqp⟩
      ⟨xm, Finset.mem_erase.mpr ⟨hxmne, hxm⟩, hqm⟩

/-- The actual regular-polygon vertex figure is a nondegenerate segment of
the paper's chord length, derived from the circle model and unit sides. -/
theorem regularPolygon_vertexFigure {p : ℕ} (hp : 3 ≤ p) (e f : E) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0)
    (hunit : dist (regularPolygonPoint 0 e f ρ p 1) (regularPolygonPoint 0 e f ρ p 0) = 1) :
    (convexHull ℝ (regularPolygonVertices (0 : E) e f ρ p : Set E) ∩
        figureHyperplane (regularPolygonPoint 0 e f ρ p 0) ρ =
      segment ℝ (regularPolygonPoint 0 e f ρ p 1) (regularPolygonPoint 0 e f ρ p (-1))) ∧
    (regularPolygonPoint (0 : E) e f ρ p 1 ≠ regularPolygonPoint 0 e f ρ p (-1)) ∧
    dist (regularPolygonPoint 0 e f ρ p 1) (regularPolygonPoint 0 e f ρ p (-1)) =
      2 * Real.cos (Real.pi / (p : ℝ)) := by
  have hc := regularPolygon_neighbor_chord hp (0 : E) e f hρ he hf horth hunit
  refine ⟨regularPolygon_section_eq_segment hp e f hρ he hf horth hunit, ?_, hc⟩
  apply dist_pos.mp
  rw [hc]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hppos : (0 : ℝ) < p := by linarith
  have hα0 : 0 < Real.pi / (p : ℝ) := div_pos Real.pi_pos hppos
  have hαhalf : Real.pi / (p : ℝ) < Real.pi / 2 := by
    apply (div_lt_iff₀ hppos).mpr
    nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos (Real.pi / (p : ℝ)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαhalf⟩
  positivity

end Uniform5
