import Uniform5.FiniteExposure

open Set
open scoped RealInnerProductSpace

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [DecidableEq E]

/-- Tilting a functional so that its value at the apex agrees with the
specified value on a transverse level hyperplane. -/
noncomputable def tiltFunctional (M L : E →L[ℝ] ℝ) (v : E) (b m : ℝ) : E →L[ℝ] ℝ :=
  M - ((m - M v) / (b - L v)) • L

omit [DecidableEq E] in
lemma tiltFunctional_level (M L : E →L[ℝ] ℝ) (v : E) {b m : ℝ}
    (hb : b ≠ L v) {q : E} (hq : L q = b) :
    tiltFunctional M L v b m q - tiltFunctional M L v b m v = M q - m := by
  simp only [tiltFunctional, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hq]
  field_simp [sub_ne_zero.mpr hb]
  ring

/-- A finite slice is the hull of the intersections of its generating rays.
The hypotheses only specify ray intersections and positive radial parameters. -/
theorem finite_section_eq_rayHull (V : Finset E) {v : E}
    (L : E →L[ℝ] ℝ) {b : ℝ} (hb : b < L v) (q : E → E)
    (hqlevel : ∀ x ∈ V.erase v, L (q x) = b)
    (hqmem : ∀ x ∈ V.erase v, q x ∈ convexHull ℝ (V : Set E))
    (hrep : ∀ x ∈ V.erase v, ∃ a : ℝ, 0 < a ∧ x = v + a • (q x - v)) :
    {y ∈ convexHull ℝ (V : Set E) | L y = b} =
      convexHull ℝ (q '' (↑(V.erase v) : Set E)) := by
  classical
  let Q := (V.erase v).image q
  have hQ : (Q : Set E) = q '' (↑(V.erase v) : Set E) := Finset.coe_image
  have hlevel : ∀ y ∈ convexHull ℝ (Q : Set E), L y = b := by
    apply convexHull_min _ (convex_hyperplane (.mk L.map_add L.map_smul) b)
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hqlevel x hx
  ext y
  constructor
  · rintro ⟨hy, hyL⟩
    rw [← hQ]
    by_contra hn
    obtain ⟨M, m, hM, hm⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) Q.finite_toSet.isCompact_convexHull.isClosed hn
    let F := tiltFunctional M L v b m
    have hf : ∀ x ∈ V, F x ≤ F v := by
      intro x hx
      by_cases hxv : x = v
      · simp [hxv]
      have hxe : x ∈ V.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
      obtain ⟨a, ha, heq⟩ := hrep x hxe
      have hMq := hM (q x) (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨x, hxe, rfl⟩))
      have he := tiltFunctional_level M L v (ne_of_lt hb) (hqlevel x hxe) (m := m)
      change F (q x) - F v = M (q x) - m at he
      have hex : F x - F v = a * (F (q x) - F v) := by
        conv_lhs => rw [heq]
        simp only [map_add, map_smul, map_sub, smul_eq_mul]
        ring
      nlinarith
    have hHull : ∀ x ∈ convexHull ℝ (V : Set E), F x ≤ F v :=
      convexHull_min hf (convex_halfSpace_le (.mk F.map_add F.map_smul) (F v))
    have he := tiltFunctional_level M L v (ne_of_lt hb) hyL (m := m)
    change F y - F v = M y - m at he
    have := hHull y hy
    linarith
  · intro hy
    rw [← hQ] at hy
    refine ⟨?_, hlevel y hy⟩
    apply convexHull_min _ (convex_convexHull ℝ _) hy
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hqmem x hx

/-- An exposed point of the transverse ray hull gives an exposed edge at the
apex, provided distinct generators have distinct ray intersections. -/
theorem ray_exposedPoint_isEdge (V : Finset E) {v : E} (hv : v ∈ V)
    (L : E →L[ℝ] ℝ) {b : ℝ} (hb : b < L v) (q : E → E)
    (hqlevel : ∀ x ∈ V.erase v, L (q x) = b)
    (hrep : ∀ x ∈ V.erase v, ∃ a : ℝ, 0 < a ∧ x = v + a • (q x - v))
    (hinj : Set.InjOn q (↑(V.erase v) : Set E))
    {x : E} (hx : x ∈ V.erase v)
    (hex : q x ∈ (convexHull ℝ (q '' (↑(V.erase v) : Set E))).exposedPoints ℝ) :
    IsEdge V v x := by
  obtain ⟨_, M, hM⟩ := exposed_point_def.mp hex
  let F := tiltFunctional M L v b (M (q x))
  have hqx : F (q x) = F v := by
    have := tiltFunctional_level M L v (ne_of_lt hb) (hqlevel x hx) (m := M (q x))
    change F (q x) - F v = M (q x) - M (q x) at this
    linarith
  have hf (z : E) (hz : z ∈ V.erase v) :
      F z ≤ F v ∧ (F z = F v → z = x) := by
    obtain ⟨a, ha, heq⟩ := hrep z hz
    have hMq := hM (q z) (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)
    have he := tiltFunctional_level M L v (ne_of_lt hb) (hqlevel z hz) (m := M (q x))
    change F (q z) - F v = M (q z) - M (q x) at he
    have hexz : F z - F v = a * (F (q z) - F v) := by
      conv_lhs => rw [heq]
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
      ring
    refine ⟨by nlinarith [hMq.1], ?_⟩
    intro hez
    have hMeq : M (q x) ≤ M (q z) := by nlinarith
    exact hinj hz hx (hMq.2 hMeq)
  have hxF : F x = F v := by
    obtain ⟨a, ha, heq⟩ := hrep x hx
    conv_lhs => rw [heq]
    simp [map_add, map_smul, map_sub, hqx]
  refine ⟨hv, (Finset.mem_erase.mp hx).2, (Finset.mem_erase.mp hx).1.symm,
    exposes_segment hv (Finset.mem_erase.mp hx).2 F (F v) rfl hxF ?_ ?_⟩
  · intro z hz
    by_cases hzv : z = v
    · simp [hzv]
    · exact (hf z (Finset.mem_erase.mpr ⟨hzv, hz⟩)).1
  · intro z hz hez
    by_cases hzv : z = v
    · exact Or.inl hzv
    · exact Or.inr ((hf z (Finset.mem_erase.mpr ⟨hzv, hz⟩)).2 hez)

end Uniform5
