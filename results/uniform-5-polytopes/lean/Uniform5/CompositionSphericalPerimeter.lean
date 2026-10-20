import Uniform5.CompositionTransverseFacets
import Uniform5.CompositionAngleSplit
import Uniform5.CompositionFacetCentroidCone

/-!
# Strict spherical perimeter of actual polygon links

Strict angular triangle inequality and Euclidean triangle sums bound the
perimeter of every exhaustive edge cycle in an apex-separating planar
section. Actual transverse-link incidence and positive centroid-ray scales
then give strict perimeter for the same cell cycle used by closure.
-/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem independent_three_coefficients {x y z : E}
    (h : LinearIndependent ℝ ![x, y, z]) {a b c : ℝ}
    (heq : a • x + b • y + c • z = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hh := Fintype.linearIndependent_iff.mp h ![a, b, c]
    (by simpa [Fin.sum_univ_succ, add_assoc] using heq)
  exact ⟨hh 0, hh 1, hh 2⟩

/-- The angle triangle inequality is strict for three independent unit vectors. -/
theorem angle_triangle_strict_unit {x y z : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hli : LinearIndependent ℝ ![x, y, z]) :
    angle x z < angle x y + angle y z := by
  let a := angle x y
  let b := angle y z
  let X := x - Real.cos a • y
  let Z := z - Real.cos b • y
  have hxy : ⟪x, y⟫ = Real.cos a := by simp [a, cos_angle, hx, hy]
  have hyz : ⟪y, z⟫ = Real.cos b := by simp [b, cos_angle, hy, hz]
  have hzy : ⟪z, y⟫ = Real.cos b := (real_inner_comm z y).symm.trans hyz
  have hyy : ⟪y, y⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hX : ‖X‖ = Real.sin a := by
    have hsq : ‖X‖ ^ 2 = 1 - Real.cos a ^ 2 := by
      dsimp [X]
      rw [norm_sub_sq_real, hx, norm_smul, hy, real_inner_smul_right, hxy]
      simp only [Real.norm_eq_abs, mul_one, sq_abs]
      ring
    nlinarith [Real.sin_sq_add_cos_sq a, norm_nonneg X, sin_angle_nonneg x y]
  have hZ : ‖Z‖ = Real.sin b := by
    have hsq : ‖Z‖ ^ 2 = 1 - Real.cos b ^ 2 := by
      dsimp [Z]
      rw [norm_sub_sq_real, hz, norm_smul, hy, real_inner_smul_right, hzy]
      simp only [Real.norm_eq_abs, mul_one, sq_abs]
      ring
    nlinarith [Real.sin_sq_add_cos_sq b, norm_nonneg Z, sin_angle_nonneg y z]
  have hZne : Z ≠ 0 := by
    intro heq
    have hcoeff := independent_three_coefficients hli
      (a := 0) (b := -Real.cos b) (c := 1)
      (by simpa [X, Z, sub_eq_add_neg, add_comm] using heq)
    norm_num at hcoeff
  have hstrict : -‖X‖ * ‖Z‖ < ⟪X, Z⟫ := by
    have hh : ⟪X, -Z⟫ < ‖X‖ * ‖-Z‖ := by
      apply inner_lt_norm_mul_iff_real.mpr
      intro heq
      have hrel : ‖Z‖ • x +
          (-(‖Z‖ * Real.cos a) - ‖X‖ * Real.cos b) • y + ‖X‖ • z = 0 := by
        have hh := sub_eq_zero.mpr heq
        simp only [norm_neg, X, Z, smul_sub, smul_neg, smul_smul] at hh
        simp only [sub_smul, neg_smul, mul_smul]
        convert hh using 1
        module
      have hc := (independent_three_coefficients hli hrel).1
      exact (norm_ne_zero_iff.mpr hZne) hc
    simpa only [inner_neg_right, norm_neg, neg_neg, neg_mul] using (neg_lt_neg hh)
  have hinner : ⟪X, Z⟫ = ⟪x, z⟫ - Real.cos a * Real.cos b := by
    simp only [X, Z, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hxy, hyz, hyy]
    ring
  have hcos : Real.cos (a + b) < Real.cos (angle x z) := by
    have hxz : Real.cos (angle x z) = ⟪x, z⟫ := by simp [cos_angle, hx, hz]
    rw [Real.cos_add, hxz]
    rw [hinner, hX, hZ] at hstrict
    linarith
  by_cases hab : a + b ≤ Real.pi
  · apply lt_of_not_ge
    intro hle
    have := Real.cos_le_cos_of_nonneg_of_le_pi
      (add_nonneg (angle_nonneg x y) (angle_nonneg y z)) (angle_le_pi x z) hle
    linarith
  · exact lt_of_le_of_lt (angle_le_pi x z) (lt_of_not_ge hab)

/-- Strict angular triangle inequality, with independence as the exact
nondegeneracy condition needed at a planar link vertex and its cone apex. -/
theorem angle_triangle_strict_of_independent {x y z : E}
    (hli : LinearIndependent ℝ ![x, y, z]) :
    angle x z < angle x y + angle y z := by
  let v : Fin 3 → E := ![x, y, z]
  have hv : ∀ i, v i ≠ 0 := fun i => hli.ne_zero i
  let w (i : Fin 3) : ℝˣ := Units.mk0 (‖v i‖⁻¹) (inv_ne_zero (norm_ne_zero_iff.mpr (hv i)))
  have hi := hli.units_smul w
  have hi' : LinearIndependent ℝ
      ![‖x‖⁻¹ • x, ‖y‖⁻¹ • y, ‖z‖⁻¹ • z] := by
    convert hi using 1
    ext i
    fin_cases i <;> rfl
  have hx := hv 0
  have hy := hv 1
  have hz := hv 2
  change x ≠ 0 at hx
  change y ≠ 0 at hy
  change z ≠ 0 at hz
  have hh := angle_triangle_strict_unit (norm_smul_inv_norm hx)
    (norm_smul_inv_norm hy) (norm_smul_inv_norm hz) hi'
  change angle (‖x‖⁻¹ • x) (‖z‖⁻¹ • z) <
    angle (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) + angle (‖y‖⁻¹ • y) (‖z‖⁻¹ • z) at hh
  simpa only [angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hx)),
    angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hy)),
    angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hy)),
    angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hz))] using hh

/-- Three distinct actual vertices of a two-dimensional polytope span
its direction space. -/
theorem planar_three_vertices_span [FiniteDimensional ℝ E] {P : Set E}
    (hd : affineDimension P = 2) {a b c : E}
    (ha : a ∈ P.extremePoints ℝ) (hb : b ∈ P.extremePoints ℝ)
    (hc : c ∈ P.extremePoints ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Submodule.span ℝ ({b - a, c - a} : Set E) = (affineSpan ℝ P).direction := by
  have hai : AffineIndependent ℝ ![a, b, c] :=
    affineIndependent_iff_not_collinear_set.mpr (fun h => by
      rcases collinear_extreme_triple ha hb hc h with h | h | h
      · exact hab h
      · exact hac h
      · exact hbc h)
  have hsub : Set.range ![a, b, c] ⊆ P := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact ha.1
    · exact hb.1
    · exact hc.1
  have hs := hai.vectorSpan_eq_of_le_of_card_eq_finrank_add_one
    (sm := (affineSpan ℝ P).direction)
    (by rw [direction_affineSpan]; exact vectorSpan_mono ℝ hsub)
    (by change 3 = affineDimension P + 1; omega)
  have hrange : Set.range ![a, b, c] = {a, b, c} := by
    ext x
    simp [Set.mem_range, Fin.exists_fin_succ, or_comm, or_left_comm, or_assoc]
  rw [hrange, vectorSpan_eq_span_vsub_set_right ℝ (show a ∈ ({a, b, c} : Set E) by simp)] at hs
  simpa [Set.image_insert_eq, Set.image_singleton, vsub_eq_sub] using hs

/-- An exposing edge functional is strict at every point of the polytope
outside that edge. -/
theorem edge_support_strict {P : Set E} {a b : E} (he : Edge P a b) :
    ∃ L : E →L[ℝ] ℝ, L b = L a ∧
      ∀ p ∈ P, p ∉ segment ℝ a b → L p < L a := by
  obtain ⟨L, hL⟩ := he.2.2.2 ⟨a, left_mem_segment ℝ a b⟩
  have ha := left_mem_segment ℝ a b
  have hb := right_mem_segment ℝ a b
  rw [hL] at ha hb
  refine ⟨L, le_antisymm (ha.2 b he.2.1.1) (hb.2 a he.1.1), ?_⟩
  intro p hp hnot
  refine lt_of_le_of_ne (ha.2 p hp) ?_
  intro heq
  apply hnot
  rw [hL]
  exact ⟨hp, fun z hz => by rw [heq]; exact ha.2 z hz⟩

/-- Every relative interior point lies strictly inside the corner formed
by the two actual edges at a planar polygon vertex. -/
theorem planar_interior_corner_positive_combination [FiniteDimensional ℝ E]
    {P : Set E} (hd : affineDimension P = 2) {a b c p : E}
    (hab : Edge P a b) (hac : Edge P a c) (hbc : b ≠ c)
    (hp : p ∈ intrinsicInterior ℝ P) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ p - a = s • (b - a) + t • (c - a) := by
  have hspan := planar_three_vertices_span hd hab.1 hab.2.1 hac.2.1
    hab.2.2.1 hac.2.2.1 hbc
  have hpa : p - a ∈ Submodule.span ℝ ({b - a, c - a} : Set E) := by
    rw [hspan]
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ P (intrinsicInterior_subset hp))
      (subset_affineSpan ℝ P hab.1.1)
  obtain ⟨s, t, heq⟩ := Submodule.mem_span_pair.mp hpa
  have hnot (b c : E) (hb : b ∈ P.extremePoints ℝ) (hc : c ∈ P.extremePoints ℝ)
      (hba : b ≠ a) (hbc : b ≠ c) : b ∉ segment ℝ a c := by
    intro hh
    rcases (mem_extremePoints_iff_forall_segment.mp hb).2 a hab.1.1 c hc.1 hh with h | h
    · exact hba h.symm
    · exact hbc h.symm
  obtain ⟨L, hLc, hL⟩ := edge_support_strict hac
  obtain ⟨M, hMb, hM⟩ := edge_support_strict hab
  have hLb := hL b hab.2.1.1 (hnot b c hab.2.1 hac.2.1 hab.2.2.1.symm hbc)
  have hMc := hM c hac.2.1.1 (hnot c b hac.2.1 hab.2.1 hac.2.2.1.symm hbc.symm)
  have hpac := intrinsicInterior_not_mem_proper_face (edge_isConvexFace hac)
    (edge_proper hac (by omega)) hp
  have hpab := intrinsicInterior_not_mem_proper_face (edge_isConvexFace hab)
    (edge_proper hab (by omega)) hp
  have hLp := hL p (intrinsicInterior_subset hp) hpac
  have hMp := hM p (intrinsicInterior_subset hp) hpab
  have hLs := congrArg L heq
  have hMt := congrArg M heq
  simp only [map_add, map_smul, map_sub, hLc, sub_self, smul_eq_mul, mul_zero,
    add_zero] at hLs
  simp only [map_add, map_smul, map_sub, hMb, sub_self, smul_eq_mul, mul_zero,
    zero_add] at hMt
  refine ⟨s, t, ?_, ?_, heq.symm⟩
  · nlinarith
  · nlinarith

/-- An apex outside a polygon's plane makes the angle comparison at
each actual polygon corner strict. -/
theorem planar_corner_angle_lt_apex [FiniteDimensional ℝ E]
    {P : Set E} (hd : affineDimension P = 2) (L : E →L[ℝ] ℝ)
    (hL : ∀ x ∈ P, L x = 1) {a b c : E}
    (hab : Edge P a b) (hac : Edge P a c) (hbc : b ≠ c) :
    angle (b - a) (c - a) < angle (b - a) (-a) + angle (-a) (c - a) := by
  have hspan := planar_three_vertices_span hd hab.1 hab.2.1 hac.2.1
    hab.2.2.1 hac.2.2.1 hbc
  have hpair : LinearIndependent ℝ ![b - a, c - a] := by
    apply (linearIndependent_iff_card_eq_finrank_span).mpr
    have hrange : Set.range ![b - a, c - a] = {b - a, c - a} := by
      ext x
      simp [Set.mem_range, Fin.exists_fin_succ, or_comm, or_left_comm, or_assoc]
    change Fintype.card (Fin 2) = Module.finrank ℝ (Submodule.span ℝ (Set.range ![b - a, c - a]))
    rw [hrange, hspan]
    exact hd.symm
  apply angle_triangle_strict_of_independent
  rw [Fintype.linearIndependent_iff]
  intro f hf
  have hsum : f 0 • (b - a) + f 1 • (-a) + f 2 • (c - a) = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hf
  have hLsum := congrArg L hsum
  simp only [map_add, map_smul, map_sub, map_neg, map_zero, hL a hab.1.1,
    hL b hab.2.1.1, hL c hac.2.1.1, sub_self, smul_eq_mul, mul_zero,
    zero_add, add_zero, mul_neg, mul_one] at hLsum
  have hf1 : f 1 = 0 := neg_eq_zero.mp hLsum
  have hcoeff := Fintype.linearIndependent_iff.mp hpair ![f 0, f 2]
    (by simpa [Fin.sum_univ_succ, hf1] using hsum)
  intro i
  fin_cases i
  · exact hcoeff 0
  · exact hf1
  · exact hcoeff 1

open scoped BigOperators

/-- Strict cone-perimeter comparison for an actual cyclic polygon in an
apex-separating plane. The center-angle sum is the ordinary planar fan. -/
theorem cyclic_polygon_cone_perimeter_lt [FiniteDimensional ℝ E]
    {P : Set E} (hd : affineDimension P = 2) (L : E →L[ℝ] ℝ)
    (hL : ∀ x ∈ P, L x = 1) {p : E} (hp : p ∈ intrinsicInterior ℝ P)
    {n : ℕ} (hn : 3 ≤ n) (u : Fin n → E) (hinj : Function.Injective u)
    (hedge : ∀ i, Edge P (u i) (u (finRotate n i)))
    (hfan : ∑ i, angle (u i - p) (u (finRotate n i) - p) = 2 * Real.pi) :
    ∑ i, angle (u i) (u (finRotate n i)) < 2 * Real.pi := by
  let R := finRotate n
  have hprev (i : Fin n) : Edge P (u i) (u (R.symm i)) := by
    have hh := hedge (R.symm i)
    rw [R.apply_symm_apply] at hh
    exact ⟨hh.2.1, hh.1, hh.2.2.1.symm, by simpa only [segment_symm] using hh.2.2.2⟩
  have hne0 (i : Fin n) : u i ≠ 0 := by
    intro hz
    have hh := hL (u i) (hedge i).1.1
    rw [hz, map_zero] at hh
    norm_num at hh
  have hnep (i : Fin n) : u i ≠ p := by
    intro heq
    have hh := intrinsicInterior_not_mem_proper_face
      (edge_isConvexFace (hedge i)) (edge_proper (hedge i) (by omega)) hp
    exact hh (heq ▸ left_mem_segment ℝ (u i) (u (R i)))
  let A (i : Fin n) := angle (u i) (u (R i))
  let B (i : Fin n) := angle (-u i) (u (R i) - u i)
  let C (i : Fin n) := angle (-u (R i)) (u i - u (R i))
  let D (i : Fin n) := angle (u i - p) (u (R i) - p)
  let H (i : Fin n) := angle (p - u i) (u (R i) - u i)
  let J (i : Fin n) := angle (p - u (R i)) (u i - u (R i))
  have htri (i : Fin n) : A i + B i + C i = Real.pi := by
    have hh := angle_add_angle_sub_add_angle_sub_eq_pi (hne0 i) (hne0 (R i))
    have hB : B i = angle (u i) (u i - u (R i)) := by
      dsimp [B]
      rw [← angle_neg_neg, neg_neg, neg_sub]
    have hC : C i = angle (u (R i)) (u (R i) - u i) := by
      dsimp [C]
      rw [← angle_neg_neg, neg_neg, neg_sub]
    simpa only [A, hB, hC] using hh
  have htrip (i : Fin n) : D i + H i + J i = Real.pi := by
    have hh := angle_add_angle_sub_add_angle_sub_eq_pi
      (sub_ne_zero.mpr (hnep i)) (sub_ne_zero.mpr (hnep (R i)))
    have hH : H i = angle (u i - p) ((u i - p) - (u (R i) - p)) := by
      dsimp [H]
      rw [← angle_neg_neg, neg_sub, neg_sub]
      congr 1; abel
    have hJ : J i = angle (u (R i) - p) ((u (R i) - p) - (u i - p)) := by
      dsimp [J]
      rw [← angle_neg_neg, neg_sub, neg_sub]
      congr 1; abel
    simpa only [D, hH, hJ] using hh
  have hcorner (i : Fin n) : J (R.symm i) + H i < C (R.symm i) + B i := by
    have hprevnext : u (R.symm i) ≠ u (R i) := by
      intro hh
      have he := congrArg R (hinj hh)
      rw [R.apply_symm_apply] at he
      exact (finRotate_ne_and_twice_ne hn i).2 he.symm
    have hc := planar_corner_angle_lt_apex hd L hL (hprev i) (hedge i) hprevnext
    obtain ⟨s, t, hs, ht, heq⟩ := planar_interior_corner_positive_combination
      hd (hprev i) (hedge i) hprevnext hp
    have hsplit := angle_split_of_positive_combination
      (sub_ne_zero.mpr (hprev i).2.2.1.symm) (sub_ne_zero.mpr (hnep i).symm) hs ht heq
    dsimp only [J, H, C, B]
    rw [R.apply_symm_apply]
    rw [← hsplit] at hc
    simpa only [angle_comm] using hc
  have hs := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
    (fun i _ => hcorner i)
  simp only [Finset.sum_add_distrib, Equiv.sum_comp] at hs
  have ht := congrArg (fun f : Fin n → ℝ => ∑ i, f i) (funext htri)
  have hp' := congrArg (fun f : Fin n → ℝ => ∑ i, f i) (funext htrip)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at ht hp'
  change ∑ i, D i = 2 * Real.pi at hfan
  change ∑ i, A i < 2 * Real.pi
  linarith

/-- Every actual finite polygon in a plane separated from the apex has
an exhaustive edge cycle with strictly less than one full turn of apex angles. -/
theorem exists_polygon_cone_perimeter_lt [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hd : affineDimension P = 2)
    (L : E →L[ℝ] ℝ) (hL : ∀ x ∈ P, L x = 1)
    {p : E} (hp : p ∈ intrinsicInterior ℝ P) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ u : ℕ → E,
      u '' Iio n = P.extremePoints ℝ ∧ Set.InjOn u (Iio n) ∧ u n = u 0 ∧
      (∀ i < n, Edge P (u i) (u (i + 1))) ∧
      ∑ i ∈ Finset.range n, angle (u i) (u (i + 1)) < 2 * Real.pi := by
  obtain ⟨f, Q, him, hf0, hQ, hdQ, hQ0⟩ := exists_centered_complex_polytope hP hd hp
  obtain ⟨v, hcov, hinj, hcycle, _, hedge, ⟨fan⟩⟩ :=
    exists_planar_intrinsic_edge_ray_fan hQ hdQ hQ0
  let n := (vertices Q hQ).card
  have hn : 3 ≤ n := sphericalFanData_three_le fan
  let u : ℕ → E := fun i => f (v i)
  have hucycle : u n = u 0 := congrArg f hcycle
  have huinj : Set.InjOn u (Iio n) := fun i hi j hj heq => hinj hi hj (f.injective heq)
  have huedge : ∀ i < n, Edge P (u i) (u (i + 1)) := fun i hi =>
    him ▸ embedding_edge_image f (hedge i hi)
  have hangle (i : ℕ) : angle (u i - p) (u (i + 1) - p) = angle (v i) (v (i + 1)) := by
    have hf (z : ℂ) : f z - p = f.linearIsometry z := by
      simpa only [hf0, vsub_eq_sub, sub_zero] using (f.map_vsub z 0).symm
    rw [show u i = f (v i) from rfl, show u (i + 1) = f (v (i + 1)) from rfl, hf, hf]
    exact f.linearIsometry.angle_map _ _
  have hnext (i : Fin n) : u (finRotate n i) = u (i.val + 1) :=
    cycle_apply_finRotate (by omega) u hucycle i
  have hsum : ∑ i : Fin n, angle (u i - p) (u (finRotate n i) - p) = 2 * Real.pi := by
    simp_rw [hnext, hangle]
    rw [Fin.sum_univ_eq_sum_range (fun i => angle (v i) (v (i + 1))) n]
    exact (spherical_fan_closure fan).2
  have hlt := cyclic_polygon_cone_perimeter_lt hd L hL hp hn (fun i : Fin n => u i)
    (fun i j heq => Fin.ext (huinj i.isLt j.isLt heq))
    (fun i => by change Edge P (u i) (u (finRotate n i)); rw [hnext]; exact huedge i i.isLt) hsum
  simp_rw [hnext] at hlt
  rw [Fin.sum_univ_eq_sum_range (fun i => angle (u i) (u (i + 1))) n] at hlt
  refine ⟨n, hn, u, ?_, huinj, hucycle, huedge, hlt⟩
  change (fun i => f (v i)) '' Iio n = _
  rw [← Set.image_image f v]
  change f '' (v '' Iio (vertices Q hQ).card) = _
  rw [hcov, embedding_extremePoints, him]

/-- In particular, the actual transverse link at every polygon of an
actual unit-uniform five-polytope has strict spherical perimeter. -/
theorem unitUniform5_transverse_link_perimeter_lt {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) {c : Space 5} (hc : c ∈ G) :
    let hPP := uniform_finitePolytope hP.1
    let S := transverseLink hPP hG.1 hc
    ∃ n : ℕ, 3 ≤ n ∧ ∃ u : ℕ → (affineSpan ℝ G).directionᗮ,
      u '' Iio n = S.extremePoints ℝ ∧ Set.InjOn u (Iio n) ∧ u n = u 0 ∧
      (∀ i < n, Edge S (u i) (u (i + 1))) ∧
      ∑ i ∈ Finset.range n, angle (u i) (u (i + 1)) < 2 * Real.pi := by
  dsimp only
  obtain ⟨hS, hdS⟩ := unitUniform5_transverseLink hP hG hc
  apply exists_polygon_cone_perimeter_lt hS hdS (transverseCutHeight _ _ hc)
    (fun x hx => hx.2)
  exact (transverseCentroidPole_mem_intrinsicInterior (uniform_finitePolytope hP.1)
    (uniform_affineSpan_eq_top hP.1) hG.1 hc
    (by rw [hG.2.1, uniform_dimension hP.1]; norm_num)).2

/-- Two distinct edges at a planar polygon vertex exhaust all its edges. -/
theorem planar_edges_exhaust [FiniteDimensional ℝ E] {P : Set E}
    (hP : FinitePolytope P) (hd : affineDimension P = 2) {a b c : E}
    (hab : Edge P a b) (hac : Edge P a c) (hbc : b ≠ c) :
    ∀ z, Edge P a z → z = b ∨ z = c := by
  have hfac {z : E} (hz : Edge P a z) :
      Facet P (segment ℝ a z) ∧ ({a} : Set E) ⊆ segment ℝ a z := by
    refine ⟨⟨edge_isConvexFace hz, ⟨a, left_mem_segment ℝ a z⟩, ?_⟩, ?_⟩
    · rw [edge_dimension hz, hd]
    · exact singleton_subset_iff.mpr (left_mem_segment ℝ a z)
  have hinj {z w : E} (hz : Edge P a z) (hw : Edge P a w)
      (heq : segment ℝ a z = segment ℝ a w) : z = w := by
    have hzseg : z ∈ segment ℝ a w := heq ▸ right_mem_segment ℝ a z
    rcases (mem_extremePoints_iff_forall_segment.mp hz.2.1).2 a hw.1.1 w hw.2.1.1 hzseg with h | h
    · exact (hz.2.2.1 h).elim
    · exact h.symm
  have htwo := finitePolytope_ridge_two_facets hP
    ((singleton_face_iff_extremePoint P a).mpr hab.1) (singleton_nonempty a)
    (by rw [affineDimension_singleton, hd])
  have hex := two_members_exhaust _ htwo (hfac hab) (hfac hac)
    (fun heq => hbc (hinj hab hac heq))
  intro z hz
  rcases (hex (segment ℝ a z)).mp (hfac hz) with h | h
  · exact Or.inl (hinj hz hab h)
  · exact Or.inr (hinj hz hac h)

/-- The sum of any symmetric edge weight is independent of the chosen
exhaustive nonrepeating edge cycle of a planar polygon. -/
theorem polygon_cycle_sum_invariant [FiniteDimensional ℝ E] {P : Set E}
    (hP : FinitePolytope P) (hd : affineDimension P = 2)
    {n m : ℕ} (hn : 3 ≤ n) (hm : 3 ≤ m)
    (u : Fin n → E) (v : Fin m → E)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (huv : Set.range u = Set.range v)
    (heu : ∀ i, Edge P (u i) (u (finRotate n i)))
    (hev : ∀ j, Edge P (v j) (v (finRotate m j)))
    (w : E → E → ℝ) (hw : ∀ x y, w x y = w y x) :
    ∑ i, w (u i) (u (finRotate n i)) = ∑ j, w (v j) (v (finRotate m j)) := by
  classical
  let R := finRotate n
  let T := finRotate m
  have he : ∀ i, ∃ j, v j = u i := by
    intro i
    have hh : u i ∈ Set.range v := huv ▸ Set.mem_range_self i
    exact hh
  let f (i : Fin n) : Fin m := (he i).choose
  have hf (i : Fin n) : v (f i) = u i := (he i).choose_spec
  have hfi : Function.Injective f := fun i j hij => hu ((hf i).symm.trans ((congrArg v hij).trans (hf j)))
  have hfs : Function.Surjective f := by
    intro j
    have hh : v j ∈ Set.range u := huv.symm ▸ Set.mem_range_self j
    obtain ⟨i, hi⟩ := hh
    exact ⟨i, hv ((hf i).trans hi)⟩
  let e : Fin n ≃ Fin m := Equiv.ofBijective f ⟨hfi, hfs⟩
  have heq (i : Fin n) : v (e i) = u i := hf i
  have hprevu (i : Fin n) : Edge P (u i) (u (R.symm i)) := by
    have hh := heu (R.symm i)
    rw [R.apply_symm_apply] at hh
    exact ⟨hh.2.1, hh.1, hh.2.2.1.symm, by simpa only [segment_symm] using hh.2.2.2⟩
  have hprevv (j : Fin m) : Edge P (v j) (v (T.symm j)) := by
    have hh := hev (T.symm j)
    rw [T.apply_symm_apply] at hh
    exact ⟨hh.2.1, hh.1, hh.2.2.1.symm, by simpa only [segment_symm] using hh.2.2.2⟩
  have hprevnext {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
      (finRotate l).symm i ≠ finRotate l i := by
    intro hh
    have hh' := congrArg (finRotate l) hh
    rw [Equiv.apply_symm_apply] at hh'
    exact (finRotate_ne_and_twice_ne hl i).2 hh'.symm
  have hlocal (i : Fin n) :
      w (u i) (u (R.symm i)) + w (u i) (u (R i)) =
      w (v (e i)) (v (T.symm (e i))) + w (v (e i)) (v (T (e i))) := by
    have hnbr := planar_edges_exhaust hP hd (hprevv (e i)) (hev (e i))
      (fun hh => hprevnext hm (e i) (hv hh))
    have hp := hnbr (u (R.symm i)) (by rw [heq]; exact hprevu i)
    have hn' := hnbr (u (R i)) (by rw [heq]; exact heu i)
    have hdistinct : u (R.symm i) ≠ u (R i) := fun hh => hprevnext hn i (hu hh)
    rw [heq]
    rcases hp with hp | hp <;> rcases hn' with hn' | hn'
    · exact (hdistinct (hp.trans hn'.symm)).elim
    · rw [hp, hn']
    · rw [hp, hn', add_comm]
    · exact (hdistinct (hp.trans hn'.symm)).elim
  have hs := congrArg (fun g : Fin n → ℝ => ∑ i, g i) (funext hlocal)
  have hbacku : ∑ i, w (u i) (u (R.symm i)) = ∑ i, w (u i) (u (R i)) := by
    calc
      _ = ∑ i, w (u (R.symm i)) (u (R (R.symm i))) := by
        simp only [R.apply_symm_apply, hw]
      _ = _ := R.symm.sum_comp (fun i => w (u i) (u (R i)))
  have hbackv : ∑ j, w (v j) (v (T.symm j)) = ∑ j, w (v j) (v (T j)) := by
    calc
      _ = ∑ j, w (v (T.symm j)) (v (T (T.symm j))) := by
        simp only [T.apply_symm_apply, hw]
      _ = _ := T.symm.sum_comp (fun j => w (v j) (v (T j)))
  dsimp only at hs
  rw [e.sum_comp (fun j => w (v j) (v (T.symm j)) + w (v j) (v (T j)))] at hs
  simp only [Finset.sum_add_distrib] at hs
  rw [hbacku, hbackv] at hs
  linarith

/-- Every exhaustive actual edge cycle has the strict cone perimeter;
no angular ordering or fan hypothesis is required of the supplied cycle. -/
theorem polygon_cycle_perimeter_lt [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) (hd : affineDimension P = 2)
    (L : E →L[ℝ] ℝ) (hL : ∀ x ∈ P, L x = 1)
    {p : E} (hp : p ∈ intrinsicInterior ℝ P)
    {n : ℕ} (hn : 3 ≤ n) (u : Fin n → E) (hu : Function.Injective u)
    (hcov : Set.range u = P.extremePoints ℝ)
    (hedge : ∀ i, Edge P (u i) (u (finRotate n i))) :
    ∑ i, angle (u i) (u (finRotate n i)) < 2 * Real.pi := by
  obtain ⟨m, hm, v, hvcov, hvinj, hvcycle, hvedge, hvlt⟩ :=
    exists_polygon_cone_perimeter_lt hP hd L hL hp
  have hnext (j : Fin m) : v (finRotate m j) = v (j.val + 1) :=
    cycle_apply_finRotate (by omega) v hvcycle j
  have hvrange : Set.range (fun j : Fin m => v j) = v '' Iio m := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j, j.isLt, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
  have heq := polygon_cycle_sum_invariant hP hd hn hm u (fun j : Fin m => v j)
    hu (fun i j heq => Fin.ext (hvinj i.isLt j.isLt heq))
    (hcov.trans (hvrange.trans hvcov).symm) hedge
    (fun j => by change Edge P (v j) (v (finRotate m j)); rw [hnext]; exact hvedge j j.isLt)
    angle angle_comm
  rw [heq]
  simp_rw [hnext]
  rw [Fin.sum_univ_eq_sum_range (fun j => angle (v j) (v (j + 1))) m]
  exact hvlt

/-- The angles between the actual cell-centroid rays in any exhaustive
incident cell cycle have strict perimeter. All incidence and metric data
are the actual geometric objects, and no spherical-excess premise occurs. -/
theorem unitUniform5_cell_cycle_perimeter_lt {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    {n : ℕ} (hn : 3 ≤ n) (C : Fin n → Set (Space 5))
    (hC : ∀ i, IsConvexFace P (C i)) (hGC : ∀ i, G ⊆ C i)
    (hdC : ∀ i, affineDimension (C i) = 3) (hinj : Function.Injective C)
    (hcov : ∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i, C i = F)
    (hadj : ∀ i, ∃ F, Facet P F ∧ C i ⊆ F ∧ C (finRotate n i) ⊆ F) :
    let hPP := uniform_finitePolytope hP.1
    let hGne := polygonFace_nonempty hG
    let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
    let a := fun i => vertexCentroid (vertices (C i)
      (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
    ∑ i, angle (a i - f) (a (finRotate n i) - f) < 2 * Real.pi := by
  dsimp only
  classical
  let hPP := uniform_finitePolytope hP.1
  have hGne := polygonFace_nonempty hG
  let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
  have hf : f ∈ G := intrinsicInterior_subset (vertexCentroid_mem_intrinsicInterior _)
  let H := (affineSpan ℝ G).directionᗮ
  let S := transverseLink hPP hG.1 hf
  let L := transverseCutHeight hPP hG.1 hf
  obtain ⟨hS, hdS⟩ := unitUniform5_transverseLink hP hG hf
  have hex (i : Fin n) : ∃ v : H, v ∈ S.extremePoints ℝ ∧
      transverseProjection G f '' C i ∩ S = {v} :=
    transverseLink_cell_vertex hPP hG.1 hG.2.1 hf (hC i) (hGC i) (hdC i)
  let v (i : Fin n) : H := (hex i).choose
  have hv (i : Fin n) : v i ∈ S.extremePoints ℝ ∧
      transverseProjection G f '' C i ∩ S = {v i} := (hex i).choose_spec
  have hvinj : Function.Injective v := by
    intro i j heq
    obtain ⟨D, _, huniq⟩ := transverseLink_vertex_unique_cell hPP hG.1 hG.2.1 hf (hv i).1
    apply hinj
    exact (huniq (C i) ⟨hC i, hGC i, hdC i, (hv i).2⟩).trans
      (huniq (C j) ⟨hC j, hGC j, hdC j, by rw [heq]; exact (hv j).2⟩).symm
  have hvrange : Set.range v = S.extremePoints ℝ := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩; exact (hv i).1
    · intro hz
      obtain ⟨D, ⟨hD, hGD, hdD, hsection⟩, _⟩ :=
        transverseLink_vertex_unique_cell hPP hG.1 hG.2.1 hf hz
      obtain ⟨i, hi⟩ := hcov D hD hGD hdD
      refine ⟨i, ?_⟩
      have hs := (hv i).2
      rw [hi, hsection] at hs
      exact (singleton_injective hs).symm
  have hvedge (i : Fin n) : Edge S (v i) (v (finRotate n i)) := by
    obtain ⟨F, hF, hiF, hjF⟩ := hadj i
    have hdF : affineDimension F = 4 := by
      have hh := hF.2.2
      rw [uniform_dimension hP.1] at hh
      omega
    have hne : C i ≠ C (finRotate n i) := fun hh =>
      (finRotate_ne_and_twice_ne hn i).1 (hinj hh).symm
    obtain ⟨x, y, _, hx, hy, hseg⟩ := transverse_fourFace_twoCells_segment
      hPP hG.1 hG.2.1 hf hF.1 hdF (hC i) (hC (finRotate n i))
      (hGC i) (hGC (finRotate n i)) hiF hjF (hdC i) (hdC (finRotate n i)) hne
    have hx' : x = v i := singleton_injective (hx.symm.trans (hv i).2)
    have hy' : y = v (finRotate n i) := singleton_injective (hy.symm.trans (hv (finRotate n i)).2)
    rw [hx', hy'] at hseg
    let F' : {Q : GeometricFace P // G ⊆ Q.val} := ⟨⟨F, hF.1⟩, (hGC i).trans hiF⟩
    have hface := (transverseLinkFaceEquiv hPP hG.1 hf F').property
    have happ := transverseLinkFaceEquiv_apply hPP hG.1 hf F'
    change (transverseLinkFaceEquiv hPP hG.1 hf F').val = transverseProjection G f '' F ∩ S at happ
    rw [happ, hseg] at hface
    exact ⟨(hv i).1, (hv (finRotate n i)).1,
      fun hh => (finRotate_ne_and_twice_ne hn i).1 (hvinj hh).symm,
      finitePolytope_face_isExposed hS hface⟩
  have hp := (transverseCentroidPole_mem_intrinsicInterior hPP
    (uniform_affineSpan_eq_top hP.1) hG.1 hf
    (by rw [hG.2.1, uniform_dimension hP.1]; norm_num)).2
  have hlt := polygon_cycle_perimeter_lt hS hdS L (fun z hz => hz.2) hp hn v hvinj hvrange hvedge
  let a := fun i => vertexCentroid (vertices (C i)
    (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
  let q := transverseProjection G f
  have hq (i : Fin n) : (q (a i) : Space 5) = a i - f :=
    transverseProjection_coe_of_mem_orthogonal G f (a i)
      (uniform_nested_face_rays_mem_orthogonal hP.1 (hC i) hG.1 hGne (hGC i)).2
  have hray (i : Fin n) : 0 < L (q (a i)) ∧ q (a i) = L (q (a i)) • v i :=
    transverse_cell_centroid_ray hPP hG.1 hG.2.1 hf (hC i) (hGC i) (hdC i) (hv i).2
  have hang (i : Fin n) : angle (a i - f) (a (finRotate n i) - f) =
      angle (v i) (v (finRotate n i)) := by
    rw [← hq i, ← hq (finRotate n i)]
    change angle (H.subtypeₗᵢ (q (a i))) (H.subtypeₗᵢ (q (a (finRotate n i)))) = _
    rw [H.subtypeₗᵢ.angle_map]
    rw [(hray i).2, (hray (finRotate n i)).2,
      angle_smul_left_of_pos _ _ (hray i).1,
      angle_smul_right_of_pos _ _ (hray (finRotate n i)).1]
  change ∑ i, angle (a i - f) (a (finRotate n i) - f) < 2 * Real.pi
  simpa only [hang] using hlt

/-- Natural-index form for the existing actual closure cycle. -/
theorem unitUniform5_natural_cell_cycle_perimeter_lt {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    {n : ℕ} (hn : 3 ≤ n) (C : ℕ → Set (Space 5))
    (hC : ∀ i, IsConvexFace P (C i)) (hGC : ∀ i, G ⊆ C i)
    (hdC : ∀ i, affineDimension (C i) = 3) (hcycle : C n = C 0)
    (hinj : Set.InjOn C (Iio n))
    (hcov : ∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i < n, C i = F)
    (hadj : ∀ i < n, ∃ F, Facet P F ∧ G ⊆ F ∧ C i ⊆ F ∧ C (i + 1) ⊆ F) :
    let hPP := uniform_finitePolytope hP.1
    let hGne := polygonFace_nonempty hG
    let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
    let a := fun i => vertexCentroid (vertices (C i)
      (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
    ∑ i ∈ Finset.range n, angle (a i - f) (a (i + 1) - f) < 2 * Real.pi := by
  have hnext (i : Fin n) : C (finRotate n i) = C (i.val + 1) :=
    cycle_apply_finRotate (by omega) C hcycle i
  have hh := unitUniform5_cell_cycle_perimeter_lt hP hG hn (fun i : Fin n => C i)
    (fun i => hC i) (fun i => hGC i) (fun i => hdC i)
    (fun i j heq => Fin.ext (hinj i.isLt j.isLt heq))
    (fun F hF hGF hdF => by obtain ⟨i, hi, heq⟩ := hcov F hF hGF hdF; exact ⟨⟨i, hi⟩, heq⟩)
    (fun i => by
      obtain ⟨F, hF, _, hiF, hjF⟩ := hadj i i.isLt
      exact ⟨F, hF, hiF, by change C (finRotate n i) ⊆ F; rw [hnext]; exact hjF⟩)
  dsimp only at hh ⊢
  let hPP := uniform_finitePolytope hP.1
  let hGne := polygonFace_nonempty hG
  let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
  let a := fun i => vertexCentroid (vertices (C i)
    (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
  have ha : a n = a 0 := by dsimp only [a]; congr 2
  change ∑ i : Fin n, angle (a i - f) (a (finRotate n i) - f) < 2 * Real.pi at hh
  simp_rw [cycle_apply_finRotate (by omega : 2 ≤ n) a ha] at hh
  rw [Fin.sum_univ_eq_sum_range (fun i => angle (a i - f) (a (i + 1) - f)) n] at hh
  exact hh

/-- Every actual polygon has one complete actual cell cycle that satisfies
both strict spherical perimeter and the literal closure equation. -/
theorem unitUniform5_polygon_strict_closure {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ C : ℕ → Set (Space 5),
    ∃ hC : ∀ i, IsConvexFace P (C i), ∃ hGC : ∀ i, G ⊆ C i,
      (∀ i, affineDimension (C i) = 3) ∧ C n = C 0 ∧ Set.InjOn C (Iio n) ∧
      (∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 → ∃ i < n, C i = F) ∧
      (∀ i < n, ∃ F, Facet P F ∧ G ⊆ F ∧ C i ⊆ F ∧ C (i + 1) ⊆ F) ∧
      let hPP := uniform_finitePolytope hP.1
      let hGne := polygonFace_nonempty hG
      let o := vertexCentroid (vertices P hPP)
      let f := vertexCentroid (vertices G (finitePolytope_face hPP hG.1 hGne))
      let a := fun i => vertexCentroid (vertices (C i)
        (finitePolytope_face hPP (hC i) (hGne.mono (hGC i))))
      (∑ i ∈ Finset.range n, angle (a i - f) (a (i + 1) - f) < 2 * Real.pi) ∧
      ∃ R : ℝ, 0 < R ∧ (∀ x ∈ P.extremePoints ℝ, ‖x - o‖ ^ 2 = R ^ 2) ∧
        cycleClosureFunction n (unitPolygonRadius k) (fun i => ‖a i - f‖)
          (fun i => angle (a i - f) (a (i + 1) - f)) (1 / R) = 0 := by
  obtain ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj, hcov, hadj, hroot⟩ :=
    unitUniform5_polygon_closure hP hG
  exact ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj, hcov, hadj,
    unitUniform5_natural_cell_cycle_perimeter_lt hP hG hn C hC hGC hdC hcycle hinj hcov hadj,
    hroot⟩

end Uniform5.Composition
