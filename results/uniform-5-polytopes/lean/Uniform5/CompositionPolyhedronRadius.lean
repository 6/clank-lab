import Uniform5.CompositionClassificationInputs
import Uniform5.CompositionSphericalPerimeter
import Uniform5.CompositionCycleWords
import Uniform5.CaseBConfig
import Uniform5.CompositionPolygonChords

/-! The actual cyclic vertex configuration of a unit-uniform polyhedron
has the paper's circle root and intrinsic circumradius. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical InnerProductGeometry
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The relative interior center is strictly off every actual edge, so
the central angle of that edge is a strict minor angle. -/
theorem planar_edge_center_angle_lt_pi [FiniteDimensional ℝ E] {P : Set E}
    (hd : affineDimension P = 2) {p x y : E} (hp : p ∈ intrinsicInterior ℝ P)
    (he : Edge P x y) : angle (x - p) (y - p) < Real.pi := by
  apply lt_of_le_of_ne (angle_le_pi _ _)
  intro hangle
  obtain ⟨_, r, hr, heq⟩ := angle_eq_pi_iff.mp hangle
  obtain ⟨L, hLy, hL⟩ := edge_support_strict he
  have hnot := intrinsicInterior_not_mem_proper_face (edge_isConvexFace he)
    (edge_proper he (by omega)) hp
  have hLp := hL p (intrinsicInterior_subset hp) hnot
  have hh := congrArg L heq
  simp only [map_sub, map_smul, hLy, smul_eq_mul] at hh
  nlinarith

/-- The central angles of any exhaustive actual planar edge cycle sum
to a full turn about a relative interior point. -/
theorem polygon_cycle_center_angle_sum [FiniteDimensional ℝ E] {P : Set E}
    (hP : FinitePolytope P) (hd : affineDimension P = 2)
    {p : E} (hp : p ∈ intrinsicInterior ℝ P) {n : ℕ} (hn : 3 ≤ n)
    (u : Fin n → E) (hu : Function.Injective u)
    (hcov : Set.range u = P.extremePoints ℝ)
    (hedge : ∀ i, Edge P (u i) (u (finRotate n i))) :
    ∑ i, angle (u i - p) (u (finRotate n i) - p) = 2 * Real.pi := by
  obtain ⟨f, Q, him, hf0, hQ, hdQ, hQ0⟩ := exists_centered_complex_polytope hP hd hp
  obtain ⟨v, hvcov, hvinj, hvcycle, _, hvedge, ⟨fan⟩⟩ :=
    exists_planar_intrinsic_edge_ray_fan hQ hdQ hQ0
  let m := (vertices Q hQ).card
  have hm : 3 ≤ m := sphericalFanData_three_le fan
  let w : ℕ → E := fun j => f (v j)
  have hwcycle : w m = w 0 := congrArg f hvcycle
  have hnext (j : Fin m) : w (finRotate m j) = w (j.val + 1) :=
    cycle_apply_finRotate (by omega) w hwcycle j
  have hwcov : Set.range (fun j : Fin m => w j) = P.extremePoints ℝ := by
    have hh : Set.range (fun j : Fin m => w j) = (fun j => f (v j)) '' Iio m := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨j, j.isLt, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    rw [hh, ← Set.image_image f v]
    change f '' (v '' Iio (vertices Q hQ).card) = _
    rw [hvcov, embedding_extremePoints, him]
  have hwedge (j : Fin m) : Edge P (w j) (w (finRotate m j)) := by
    rw [hnext]
    exact him ▸ embedding_edge_image f (hvedge j j.isLt)
  have hang (j : ℕ) : angle (w j - p) (w (j + 1) - p) = angle (v j) (v (j + 1)) := by
    have hf (z : ℂ) : f z - p = f.linearIsometry z := by
      simpa only [hf0, vsub_eq_sub, sub_zero] using (f.map_vsub z 0).symm
    change angle (f (v j) - p) (f (v (j + 1)) - p) = _
    rw [hf, hf]
    exact f.linearIsometry.angle_map _ _
  rw [polygon_cycle_sum_invariant hP hd hn hm u (fun j : Fin m => w j) hu
    (fun i j heq => Fin.ext (hvinj i.isLt j.isLt (f.injective heq)))
    (hcov.trans hwcov.symm) hedge hwedge
    (fun x y => angle (x - p) (y - p)) (fun x y => angle_comm _ _)]
  simp_rw [hnext, hang]
  rw [Fin.sum_univ_eq_sum_range (fun j => angle (v j) (v (j + 1))) m]
  exact (spherical_fan_closure fan).2

/-- The actual unit-edge section has the prescribed circle radius in every
dimension; the center and sphere are derived from recursive uniformity. -/
theorem unitUniform_vertexFigure_circle {d : ℕ} {P : Set E}
    (hP : UnitUniform (d + 3) P) {v : E} (hv : v ∈ P.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    let R := intrinsicRadius P
    let a := c + figureCenter (v - c) R
    a ∈ intrinsicInterior ℝ (vertexFigure P v c) ∧
      ∀ x ∈ (vertexFigure P v c).extremePoints ℝ,
        ‖x - a‖ = Real.sqrt (1 - 1 / (4 * R ^ 2)) := by
  dsimp only
  obtain ⟨_, hR, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hRpos := uniform_intrinsicRadius_pos hP.1
  refine ⟨unitUniform_centroid_figureCenter_mem_intrinsicInterior hP _ hRpos hs hv, ?_⟩
  intro x hx
  rw [finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv _ (intrinsicRadius P) hs hP.2] at hx
  rw [← dist_eq_norm]
  apply translated_figure_radius
  · rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hR).mp (hs x hx.2.1)
  · rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hR).mp (hs v hv)
  · exact hRpos.ne'
  · rw [dist_comm]; exact hP.2 v x hx

/-- The actual configuration labels give the literal cosine chord lengths;
no catalogue matching is used to obtain the metric labels. -/
theorem vertexConfiguration_chord [FiniteDimensional ℝ E] {P F : Set E} {d : ℕ}
    (hP : UnitUniform (d + 3) P) {v x y : E} (hv : v ∈ P.extremePoints ℝ)
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    {k : ℕ} (hF : PolygonFace P F k) (hvF : v ∈ F)
    (hsection : F ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) = segment ℝ x y) :
    3 ≤ k ∧ dist x y = 2 * Real.cos (Real.pi / k) := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hext := finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv _ (intrinsicRadius P) hs hP.2
  have hxF : x ∈ F := (hsection.symm ▸ left_mem_segment ℝ x y).1
  have hyF : y ∈ F := (hsection.symm ▸ right_mem_segment ℝ x y).1
  have hx : Edge P v x := by have hh := he.1; rwa [hext] at hh
  have hy : Edge P v y := by have hh := he.2.1; rwa [hext] at hh
  exact ⟨(polygonFace_unitPolygon hP hF).1, polygonFace_neighbor_chord hP hF
    ((edge_face_iff (uniform_finitePolytope hP.1) hF.1 hvF hxF).mp hx)
    ((edge_face_iff (uniform_finitePolytope hP.1) hF.1 hvF hyF).mp hy) he.2.2.1⟩

private theorem foldr_max_lt_bound (l : List ℝ) {S : ℝ} (hS : 0 < S)
    (hl : ∀ x ∈ l, x < S) : l.foldr max 0 < S := by
  induction l with
  | nil => exact hS
  | cons x l ih =>
    exact max_lt (hl x (by simp)) (ih (fun y hy => hl y (by simp [hy])))

/-- The root used by B2 is forced by the actual vertex-figure circle of
any actual cyclic configuration of a unit-uniform polyhedron. -/
theorem actualVertexConfiguration_configRoot {P : Set (Space 3)}
    (hP : UnitUniform 3 P) {n : ℕ} {sizes : Fin n → ℕ}
    (hconfig : ActualVertexConfiguration P sizes) :
    let S := Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2))
    (∀ i, 3 ≤ sizes i) ∧ 3 ≤ n ∧ 0 < S ∧
      CaseB.ConfigRoot (CaseB.realConfig (List.ofFn sizes)) S := by
  obtain ⟨hPP, v, u, F, hv, hdQ, hn, hcov, hinj, hcycle, hedge, hF⟩ := hconfig
  let c := vertexCentroid (vertices P hPP)
  let R := intrinsicRadius P
  let a := c + figureCenter (v - c) R
  let Q := vertexFigure P v c
  let S := Real.sqrt (1 - 1 / (4 * R ^ 2))
  have hR : 0 < R := uniform_intrinsicRadius_pos hP.1
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hQ : FinitePolytope Q := finitePolytope_vertexFigure_of_positiveDimension hPP hv c R hs hP.2
    (by rw [uniform_dimension hP.1]; norm_num)
  have hcirc : a ∈ intrinsicInterior ℝ Q ∧ ∀ x ∈ Q.extremePoints ℝ, ‖x - a‖ = S :=
    unitUniform_vertexFigure_circle hP hv
  have hnorm (i : Fin n) : ‖u i - a‖ = S := hcirc.2 (u i) (hedge i i.isLt).1
  have hnormnext (i : Fin n) : ‖u (i.val + 1) - a‖ = S :=
    hcirc.2 _ (hedge i i.isLt).2.1
  have hS : 0 < S := by
    apply lt_of_le_of_ne (Real.sqrt_nonneg _)
    intro hz
    let i : Fin n := ⟨0, by omega⟩
    have hx : u i = a := sub_eq_zero.mp (norm_eq_zero.mp ((hnorm i).trans hz.symm))
    have hy : u (i.val + 1) = a := sub_eq_zero.mp (norm_eq_zero.mp ((hnormnext i).trans hz.symm))
    exact (hedge i i.isLt).2.2.1 (hx.trans hy.symm)
  have hrad : 0 < 1 - 1 / (4 * R ^ 2) := Real.sqrt_pos.mp hS
  have hSq : S ^ 2 = 1 - 1 / (4 * R ^ 2) := Real.sq_sqrt hrad.le
  have hS1 : S < 1 := by
    have hp : 0 < 1 / (4 * R ^ 2) := one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hR))
    nlinarith
  have hchord (i : Fin n) : 3 ≤ sizes i ∧
      dist (u i) (u (i.val + 1)) = 2 * CaseB.polygonCos (sizes i) :=
    vertexConfiguration_chord hP hv (hedge i i.isLt) (hF i).1 (hF i).2.1 (hF i).2.2
  have hang (i : Fin n) : angle (u i - a) (u (i.val + 1) - a) =
      CaseB.centralArc (CaseB.polygonCos (sizes i)) S :=
    CaseB.angle_eq_centralArc hS (CaseB.polygonCos_bounds (hchord i).1).1.le
      (hnorm i) (hnormnext i) (by simpa only [dist_sub_right] using (hchord i).2)
  have hcos (i : Fin n) : CaseB.polygonCos (sizes i) < S := by
    apply (CaseB.centralArc_lt_pi_iff hS).mp
    rw [← hang]
    exact planar_edge_center_angle_lt_pi hdQ hcirc.1 (hedge i i.isLt)
  have hnext (i : Fin n) : u (finRotate n i) = u (i.val + 1) :=
    cycle_apply_finRotate (by omega) u hcycle i
  have hurange : Set.range (fun i : Fin n => u i) = Q.extremePoints ℝ := by
    rw [← hcov]
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  have hsum := polygon_cycle_center_angle_sum hQ hdQ hcirc.1 hn (fun i : Fin n => u i)
    (fun i j heq => Fin.ext (hinj i.isLt j.isLt heq)) hurange
    (fun i => by change Edge Q (u i) (u (finRotate n i)); rw [hnext]; exact hedge i i.isLt)
  simp_rw [hnext, hang] at hsum
  refine ⟨fun i => (hchord i).1, hn, hS, ?_, hS1, ?_⟩
  · unfold CaseB.configMax CaseB.realConfig
    rw [List.map_map, List.map_ofFn]
    apply foldr_max_lt_bound _ hS
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hcos i
  · simpa [CaseB.configArcSum, CaseB.realConfig, List.map_map, List.map_ofFn,
      List.sum_ofFn, CaseB.centralArc, CaseB.polygonCos, S, R] using hsum

/-- A geometric circle root below one forces the angle condition,
including the degree bound five; neither is a separate premise. -/
theorem configRoot_angleCondition {c : List ℝ} (hq : ∀ q ∈ c, 3 ≤ q)
    (hn : 3 ≤ c.length) {S : ℝ} (hroot : CaseB.ConfigRoot c S) :
    CaseB.AngleCondition c := by
  letI : NeZero c.length := ⟨by omega⟩
  let f : Fin c.length → ℝ := fun i => Real.cos (Real.pi / c[i.val])
  have hfpos (i : Fin c.length) : 0 < f i :=
    (CaseB.configEntryCos_bounds (hq _ (List.getElem_mem i.isLt))).1
  have hf1 (i : Fin c.length) : f i < 1 :=
    (CaseB.configEntryCos_bounds (hq _ (List.getElem_mem i.isLt))).2
  obtain ⟨hmem, hsum⟩ := (CaseB.configRoot_iff_finite hq S).mp hroot
  have hlt := CaseB.arcSum_strictAntiOn hfpos (Ioo_subset_Icc_self hmem)
    (show (1 : ℝ) ∈ Icc (CaseB.maxCos f) 1 from ⟨(CaseB.maxCos_lt_one hf1).le, le_rfl⟩) hmem.2
  have hangle : (c.map (fun q => 1 - 2 / q)).sum < 2 := by
    rw [hsum] at hlt
    rw [← CaseB.configArcSum_eq_arcSum, CaseB.configArcSum_one hq] at hlt
    nlinarith [Real.pi_pos]
  have hlower : (c.length : ℝ) * (1 / 3) ≤ (c.map (fun q => 1 - 2 / q)).sum := by
    rw [← Fin.sum_univ_fun_getElem c (fun q => 1 - 2 / q)]
    calc
      _ = ∑ i : Fin c.length, (1 / 3 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by
        have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
          (by norm_num : (0 : ℝ) < 3) (hq _ (List.getElem_mem i.isLt))
        linarith)
  have hlen : c.length < 6 := by
    have hh : (c.length : ℝ) < 6 := by linarith
    exact_mod_cast hh
  exact ⟨hq, hn, by omega, hangle⟩

/-- The analytic radius chosen by the Case B interface equals the actual
intrinsic circumradius, for every actual cyclic configuration. -/
theorem actualVertexConfiguration_radius {P : Set (Space 3)}
    (hP : UnitUniform 3 P) {n : ℕ} {sizes : Fin n → ℕ}
    (hconfig : ActualVertexConfiguration P sizes) :
    CaseB.configRadius (CaseB.realConfig (List.ofFn sizes)) = intrinsicRadius P := by
  obtain ⟨hq, hn, hS, hroot⟩ := actualVertexConfiguration_configRoot hP hconfig
  letI : NeZero (List.ofFn sizes).length := ⟨by simp only [List.length_ofFn]; omega⟩
  have hq' : ∀ q ∈ List.ofFn sizes, 3 ≤ q := by
    intro q hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
    exact hq i
  rw [CaseB.configRadius_realConfig_eq_of_root hq' hroot]
  exact (CaseB.height_eq_radiusFromCircle (uniform_intrinsicRadius_pos hP.1)
    hS.le hroot.2.1 (Real.sq_sqrt (Real.sqrt_pos.mp hS).le)).symm

/-- Every actual uniform-polyhedron vertex configuration is an admissible
Case B configuration and is strictly closable. -/
theorem actualVertexConfiguration_angleCondition_closable {P : Set (Space 3)}
    (hP : UnitUniform 3 P) {n : ℕ} {sizes : Fin n → ℕ}
    (hconfig : ActualVertexConfiguration P sizes) :
    CaseB.AngleCondition (CaseB.realConfig (List.ofFn sizes)) ∧
      CaseB.Closable (CaseB.realConfig (List.ofFn sizes)) := by
  obtain ⟨hq, hn, _, hroot⟩ := actualVertexConfiguration_configRoot hP hconfig
  have hq' : ∀ q ∈ CaseB.realConfig (List.ofFn sizes), 3 ≤ q := by
    intro q hmem
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
    exact_mod_cast hq i
  have hlen : 3 ≤ (CaseB.realConfig (List.ofFn sizes)).length := by
    simpa only [CaseB.realConfig, List.length_map, List.length_ofFn] using hn
  letI : NeZero (CaseB.realConfig (List.ofFn sizes)).length := ⟨by omega⟩
  exact ⟨configRoot_angleCondition hq' hlen hroot, CaseB.closable_of_ConfigRoot hq' hroot⟩

/-- Every actual unit-uniform polyhedron supplies an admissible, strictly
closable cyclic configuration with its actual intrinsic radius. -/
theorem unitUniform3_exists_admissible_configuration {P : Set (Space 3)}
    (hP : UnitUniform 3 P) :
    ∃ n : ℕ, ∃ sizes : Fin n → ℕ, ActualVertexConfiguration P sizes ∧
      CaseB.AngleCondition (CaseB.realConfig (List.ofFn sizes)) ∧
      CaseB.Closable (CaseB.realConfig (List.ofFn sizes)) ∧
      CaseB.configRadius (CaseB.realConfig (List.ofFn sizes)) = intrinsicRadius P := by
  obtain ⟨n, sizes, hconfig⟩ := unitUniform3_exists_vertexConfiguration hP
  obtain ⟨ha, hc⟩ := actualVertexConfiguration_angleCondition_closable hP hconfig
  exact ⟨n, sizes, hconfig, ha, hc, actualVertexConfiguration_radius hP hconfig⟩

end Uniform5.Composition
