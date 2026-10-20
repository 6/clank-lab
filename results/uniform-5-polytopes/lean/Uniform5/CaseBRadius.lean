import Uniform5.Closure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.IntermediateValue

/-!
# Case B: type (i) radius and closability

The analytic statements concern the actual sum of minor central angles, not
an abstract monotone function. `polygonCos q = cos (pi/q)` and the chord is
`2 * polygonCos q`. The finite maximum is taken internally.

The geometric bridge below uses the project's existing `SphericalFanData`:
constructing that ordered once-around lift from a convex polytope remains an
external geometric obligation. Unit rays, common axial projection, and chord
lengths are metric inputs; no closure equation or closability is an input.
-/
noncomputable section
namespace Uniform5.CaseB
open Set InnerProductGeometry
open scoped BigOperators RealInnerProductSpace

/-- Half the chord of the regular polygon at a unit-edge vertex. -/
noncomputable def polygonCos (q : ℕ) : ℝ := Real.cos (Real.pi / (q : ℝ))
noncomputable def polygonChord (q : ℕ) : ℝ := 2 * polygonCos q
/-- Minor central angle subtending a chord of length `2*c` on radius `S`. -/
noncomputable def centralArc (c S : ℝ) : ℝ := 2 * Real.arcsin (c / S)
/-- The paper's exact type-(i) closure function. -/
noncomputable def arcSum {ι : Type*} [Fintype ι] (c : ι → ℝ) (S : ℝ) : ℝ :=
  ∑ i, centralArc (c i) S
/-- The actual finite maximum of the half-chords. -/
noncomputable def maxCos {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty c
/-- Configuration radius associated with a circle radius `S < 1`. -/
noncomputable def radiusFromCircle (S : ℝ) : ℝ := 1 / (2 * Real.sqrt (1 - S ^ 2))
/-- Circumradius of a unit-edge regular polygon. -/
noncomputable def regularPolygonRadiusNat (q : ℕ) : ℝ := 1 / (2 * Real.sin (Real.pi / (q : ℝ)))

section Analytic
variable {ι : Type*} [Fintype ι] [Nonempty ι] {c : ι → ℝ}

theorem le_maxCos (c : ι → ℝ) (i : ι) : c i ≤ maxCos c :=
  Finset.le_sup' c (Finset.mem_univ i)

theorem maxCos_pos (hc : ∀ i, 0 < c i) : 0 < maxCos c := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (hc i).trans_le (le_maxCos c i)

theorem maxCos_lt_one (hc : ∀ i, c i < 1) : maxCos c < 1 := by
  exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (by simpa using hc)

theorem ratio_mem {S : ℝ} (hc : ∀ i, 0 < c i) (hS : maxCos c ≤ S) (i : ι) :
    c i / S ∈ Icc (-1 : ℝ) 1 := by
  have hpos : 0 < S := (maxCos_pos hc).trans_le hS
  exact ⟨le_trans (by norm_num) (le_of_lt (div_pos (hc i) hpos)), (div_le_one hpos).mpr ((le_maxCos c i).trans hS)⟩

theorem arcSum_continuousOn (hc : ∀ i, 0 < c i) :
    ContinuousOn (arcSum c) (Icc (maxCos c) 1) := by
  apply continuousOn_finset_sum
  intro i _
  exact continuousOn_const.mul (Real.continuous_arcsin.continuousOn.comp
    (continuousOn_const.div continuousOn_id (fun S hS =>
      ne_of_gt ((maxCos_pos hc).trans_le hS.1))) (fun _ _ => mem_univ _))

theorem arcSum_strictAntiOn (hc : ∀ i, 0 < c i) :
    StrictAntiOn (arcSum c) (Icc (maxCos c) 1) := by
  intro S hS T hT hST
  have hSpos : 0 < S := (maxCos_pos hc).trans_le hS.1
  have hTpos : 0 < T := hSpos.trans hST
  have hterm : ∀ i, centralArc (c i) T < centralArc (c i) S := by
    intro i
    apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
    exact Real.strictMonoOn_arcsin (ratio_mem hc hT.1 i) (ratio_mem hc hS.1 i)
      (div_lt_div_of_pos_left (hc i) hSpos hST)
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hterm i)

/-- With the strict upper endpoint condition, closability is exactly existence
of a unique interior root. -/
theorem unique_root_iff (hc : ∀ i, 0 < c i) (hc1 : ∀ i, c i < 1)
    (hupper : arcSum c 1 < 2 * Real.pi) :
    (∃! S, S ∈ Ioo (maxCos c) 1 ∧ arcSum c S = 2 * Real.pi) ↔
      2 * Real.pi < arcSum c (maxCos c) := by
  have hm := (maxCos_lt_one hc1).le
  have hanti := arcSum_strictAntiOn hc
  constructor
  · rintro ⟨S, ⟨hS, hroot⟩, _⟩
    rw [← hroot]
    exact hanti ⟨le_rfl, hm⟩ (Ioo_subset_Icc_self hS) hS.1
  · intro hlower
    obtain ⟨S, hS, hroot⟩ := intermediate_value_Ioo' hm
      (arcSum_continuousOn hc) ⟨hupper, hlower⟩
    refine ⟨S, ⟨hS, hroot⟩, ?_⟩
    intro T hT
    exact hanti.injOn (Ioo_subset_Icc_self hT.1) (Ioo_subset_Icc_self hS)
      (hT.2.trans hroot.symm)

/-- Any admissible geometric root forces strict closability; equality at the
lower endpoint cannot occur for an interior root. -/
theorem closable_of_root (hc : ∀ i, 0 < c i) {S : ℝ}
    (hS : S ∈ Ioo (maxCos c) 1) (hroot : arcSum c S = 2 * Real.pi) :
    2 * Real.pi < arcSum c (maxCos c) := by
  rw [← hroot]
  exact arcSum_strictAntiOn hc ⟨le_rfl, hS.1.le.trans hS.2.le⟩
    (Ioo_subset_Icc_self hS) hS.1

omit [Nonempty ι] in
/-- Relabelling the entries preserves the function, hence also its unique root. -/
theorem arcSum_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (S : ℝ) :
    arcSum (c ∘ e) S = arcSum c S := by
  exact Equiv.sum_comp e (fun i => centralArc (c i) S)

end Analytic

/-- Basic domain bounds for the exact polygon constants. -/
theorem polygonAngle_bounds {q : ℕ} (hq : 3 ≤ q) :
    0 < Real.pi / (q : ℝ) ∧ Real.pi / (q : ℝ) < Real.pi / 2 := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast (by omega : 2 < q)
  exact ⟨div_pos Real.pi_pos (by linarith),
    div_lt_div_of_pos_left Real.pi_pos (by norm_num) hq'⟩

theorem polygonCos_bounds {q : ℕ} (hq : 3 ≤ q) :
    0 < polygonCos q ∧ polygonCos q < 1 := by
  obtain ⟨h0, h1⟩ := polygonAngle_bounds hq
  constructor
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      (by linarith [Real.pi_pos] : Real.pi / (q : ℝ) ≤ Real.pi) h0
    simpa [polygonCos] using h

/-- Exact evaluation of the upper endpoint in the paper. -/
theorem centralArc_polygon_one {q : ℕ} (hq : 3 ≤ q) :
    centralArc (polygonCos q) 1 = Real.pi * (1 - 2 / (q : ℝ)) := by
  obtain ⟨h0, h1⟩ := polygonAngle_bounds hq
  rw [centralArc, div_one, polygonCos, Real.arcsin_eq_pi_div_two_sub_arccos,
    Real.arccos_cos h0.le (by linarith [Real.pi_pos])]
  ring

theorem arcSum_polygon_one {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ i, 3 ≤ q i) :
    arcSum (fun i => polygonCos (q i)) 1 =
      Real.pi * ∑ i, (1 - 2 / (q i : ℝ)) := by
  simp only [arcSum, centralArc_polygon_one (hq _), Finset.mul_sum]

/-- The formula has a positive radicand throughout the admissible interval. -/
theorem radius_radicand_pos {S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1) :
    0 < 1 - S ^ 2 := by nlinarith

theorem radiusFromCircle_pos {S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1) :
    0 < radiusFromCircle S := by
  exact one_div_pos.mpr (mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (radius_radicand_pos hS0 hS1)))

theorem radiusFromCircle_sq {S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1) :
    radiusFromCircle S ^ 2 = 1 / (4 * (1 - S ^ 2)) := by
  rw [radiusFromCircle, div_pow, mul_pow, Real.sq_sqrt
    (radius_radicand_pos hS0 hS1).le]
  norm_num

/-- Increasing the circle radius increases the forced configuration radius. -/
theorem radiusFromCircle_mono {a S : ℝ} (ha : 0 ≤ a) (haS : a ≤ S) (hS : S < 1) :
    radiusFromCircle a ≤ radiusFromCircle S := by
  apply one_div_le_one_div_of_le
  · exact mul_pos (by norm_num) (Real.sqrt_pos.mpr
      (radius_radicand_pos (ha.trans haS) hS))
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.sqrt_le_sqrt
    nlinarith

/-- At the half-chord threshold the radius is the regular polygon radius. -/
theorem radiusFromCircle_polygonCos {q : ℕ} (hq : 3 ≤ q) :
    radiusFromCircle (polygonCos q) = regularPolygonRadiusNat q := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (polygonAngle_bounds hq).1
    (by linarith [(polygonAngle_bounds hq).2, Real.pi_pos])
  have ht := Real.sin_sq_add_cos_sq (Real.pi / (q : ℝ))
  have heq : 1 - polygonCos q ^ 2 = Real.sin (Real.pi / (q : ℝ)) ^ 2 := by
    dsimp [polygonCos]; linarith
  rw [radiusFromCircle, heq, Real.sqrt_sq_eq_abs, abs_of_pos hs, regularPolygonRadiusNat]

/-- In fact the bound holds for every entry, so in particular for a largest q. -/
theorem regularPolygonRadiusNat_le_radiusFromCircle {q : ℕ} {S : ℝ} (hq : 3 ≤ q)
    (hchord : polygonCos q ≤ S) (hS : S < 1) :
    regularPolygonRadiusNat q ≤ radiusFromCircle S := by
  rw [← radiusFromCircle_polygonCos hq]
  exact radiusFromCircle_mono (polygonCos_bounds hq).1.le hchord hS

/-- Solve the cone identity for the positive axial height. -/
theorem height_eq_radiusFromCircle {h S : ℝ} (hh : 0 < h)
    (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hcone : S ^ 2 = 1 - 1 / (4 * h ^ 2)) : h = radiusFromCircle S := by
  have hn := radius_radicand_pos hS0 hS1
  have hr := Real.sq_sqrt hn.le
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hid : 4 * h ^ 2 * (1 - S ^ 2) = 1 := by
    rw [hcone]
    field_simp
  have hp := Real.sqrt_pos.mpr hn
  have heq : 2 * h * Real.sqrt (1 - S ^ 2) = 1 := by
    have hsquare : (2 * h * Real.sqrt (1 - S ^ 2)) ^ 2 = 1 := by
      calc
        _ = 4 * h ^ 2 * (Real.sqrt (1 - S ^ 2)) ^ 2 := by ring
        _ = 1 := by rw [hr]; exact hid
    have hprod := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hh) hp
    nlinarith
  apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) hp))).mpr
  change h * (2 * Real.sqrt (1 - S ^ 2)) = 1
  nlinarith

/-- Pythagoras transfers the configuration radius to the full radius. -/
theorem full_radius_sq {R r h S : ℝ} (hh : 0 < h)
    (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hcone : S ^ 2 = 1 - 1 / (4 * h ^ 2))
    (horth : R ^ 2 = r ^ 2 + h ^ 2) :
    R ^ 2 = r ^ 2 + radiusFromCircle S ^ 2 := by
  rw [← height_eq_radiusFromCircle hh hS0 hS1 hcone]
  exact horth


/-- The two nonmaximal arcs at the diameter threshold detect a positive
Pythagorean deficit. Includes equality cases at the boundary. -/
theorem arcsin_pair_criterion {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.pi / 2 < Real.arcsin x + Real.arcsin y ↔ 1 < x ^ 2 + y ^ 2 := by
  have hyangle : Real.arccos y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.arccos_nonneg y, Real.pi_pos],
      Real.arccos_le_pi_div_two.mpr hy0⟩
  have he : Real.pi / 2 < Real.arcsin x + Real.arcsin y ↔
      Real.sqrt (1 - y ^ 2) < x := by
    calc
      _ ↔ Real.arccos y < Real.arcsin x := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]; constructor <;> intro h <;> linarith
      _ ↔ _ := by
        rw [Real.lt_arcsin_iff_sin_lt hyangle ⟨by linarith, hx1⟩,
          Real.sin_arccos]
  rw [he]
  have hy2 : 0 ≤ 1 - y ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hy2
  have hs0 := Real.sqrt_nonneg (1 - y ^ 2)
  constructor <;> intro h <;> nlinarith

/-- Three positive half-chords, with `d` maximal: the exact endpoint test is
precisely the acute-triangle squared-side inequality at the longest side. -/
theorem triple_endpoint_criterion {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (had : a ≤ d) (hbd : b ≤ d) :
    2 * Real.pi < arcSum ![a, b, d] d ↔ d ^ 2 < a ^ 2 + b ^ 2 := by
  have hd : 0 < d := ha.trans_le had
  have he := arcsin_pair_criterion (div_nonneg ha.le hd.le)
    ((div_le_one hd).mpr had) (div_nonneg hb.le hd.le) ((div_le_one hd).mpr hbd)
  have hf : arcSum ![a, b, d] d =
      2 * (Real.arcsin (a / d) + Real.arcsin (b / d)) + Real.pi := by
    simp [arcSum, centralArc, Fin.sum_univ_succ, ne_of_gt hd, Real.arcsin_one]
    ring
  rw [hf]
  calc
    _ ↔ Real.pi / 2 < Real.arcsin (a / d) + Real.arcsin (b / d) := by
      constructor <;> intro h <;> linarith
    _ ↔ 1 < (a / d) ^ 2 + (b / d) ^ 2 := he
    _ ↔ d ^ 2 < a ^ 2 + b ^ 2 := by
      rw [div_pow, div_pow, ← add_div, lt_div_iff₀ (sq_pos_of_pos hd)]
      simp

theorem maxCos_triple {a b d : ℝ} (had : a ≤ d) (hbd : b ≤ d) :
    maxCos ![a, b, d] = d := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty ![a, b, d]).mpr
    intro i _
    fin_cases i <;> simp_all
  · exact le_maxCos ![a, b, d] 2

/-- Closability for three entries is the strict squared-side criterion. -/
theorem triple_closable_iff {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (had : a ≤ d) (hbd : b ≤ d) :
    2 * Real.pi < arcSum ![a, b, d] (maxCos ![a, b, d]) ↔
      (2 * d) ^ 2 < (2 * a) ^ 2 + (2 * b) ^ 2 := by
  rw [maxCos_triple had hbd, triple_endpoint_criterion ha hb had hbd]
  constructor <;> intro h <;> nlinarith

section TriangleGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Acuteness expressed by the actual three Euclidean angles. -/
noncomputable def AcuteTriangle (x y z : E) : Prop :=
  angle (y - x) (z - x) < Real.pi / 2 ∧
  angle (x - y) (z - y) < Real.pi / 2 ∧
  angle (x - z) (y - z) < Real.pi / 2

/-- An actual vector angle is acute exactly when its dot product is positive. -/
theorem angle_acute_iff_inner_pos (u v : E) :
    angle u v < Real.pi / 2 ↔ 0 < ⟪u, v⟫ := by
  rw [angle, Real.arccos_lt_pi_div_two]
  constructor
  · intro h
    exact (div_pos_iff.mp h).elim (fun h => h.1)
      (fun h => False.elim (not_lt_of_ge (mul_nonneg (norm_nonneg u) (norm_nonneg v)) h.2))
  · intro h
    have hu : 0 < ‖u‖ := norm_pos_iff.mpr (by intro hu; simp [hu] at h)
    have hv : 0 < ‖v‖ := norm_pos_iff.mpr (by intro hv; simp [hv] at h)
    exact div_pos h (mul_pos hu hv)

/-- Squared-side criterion derived from the inner-product cosine law. -/
theorem angle_acute_iff_sq (x y z : E) :
    angle (y - x) (z - x) < Real.pi / 2 ↔
      dist y z ^ 2 < dist x y ^ 2 + dist x z ^ 2 := by
  rw [angle_acute_iff_inner_pos]
  have h := norm_sub_sq_real (y - x) (z - x)
  have hv : (y - x) - (z - x) = y - z := by abel
  rw [hv, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm,
    dist_comm y x, dist_comm z x] at h
  constructor <;> intro hi <;> linarith

/-- For a longest side it suffices to test its opposite angle; positivity
of the shorter lengths rules out zero sides. -/
theorem acuteTriangle_iff_longest {x y z : E} {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (had : a ≤ d) (hbd : b ≤ d)
    (hxy : dist x y = 2 * a) (hxz : dist x z = 2 * b)
    (hyz : dist y z = 2 * d) :
    AcuteTriangle x y z ↔ (2 * d) ^ 2 < (2 * a) ^ 2 + (2 * b) ^ 2 := by
  have hd : 0 < d := ha.trans_le had
  simp only [AcuteTriangle, angle_acute_iff_sq, dist_comm y x, dist_comm z x,
    dist_comm z y, hxy, hxz, hyz]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by nlinarith, by nlinarith⟩

/-- The k=3 criterion for a genuine Euclidean chord triangle, with the longest
half-chord listed last. No acuteness or centre-interiority premise is used. -/
theorem triple_closable_iff_acute {x y z : E} {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (had : a ≤ d) (hbd : b ≤ d)
    (hxy : dist x y = 2 * a) (hxz : dist x z = 2 * b)
    (hyz : dist y z = 2 * d) :
    (2 * Real.pi < arcSum ![a, b, d] (maxCos ![a, b, d])) ↔
      AcuteTriangle x y z := by
  rw [triple_closable_iff ha hb had hbd,
    acuteTriangle_iff_longest ha hb had hbd hxy hxz hyz]

end TriangleGeometry

section CircleGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The minor central angle is recovered from the actual chord and radius. -/
theorem angle_eq_centralArc {u v : E} {c S : ℝ} (hS : 0 < S) (hc : 0 ≤ c)
    (hu : ‖u‖ = S) (hv : ‖v‖ = S) (hchord : dist u v = 2 * c) :
    angle u v = centralArc c S := by
  have hbound := norm_sub_le u v
  rw [← dist_eq_norm, hchord, hu, hv] at hbound
  have hrat0 : 0 ≤ c / S := div_nonneg hc hS.le
  have hrat1 : c / S ≤ 1 := (div_le_one hS).mpr (by linarith)
  have hn := norm_sub_sq_real u v
  rw [← dist_eq_norm, hchord, hu, hv] at hn
  apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩
    ⟨by exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr hrat0),
      by dsimp [centralArc]; linarith [Real.arcsin_le_pi_div_two (c / S)]⟩
  rw [cos_angle, hu, hv, centralArc, Real.cos_two_mul, Real.cos_arcsin,
    Real.sq_sqrt (by nlinarith : 0 ≤ 1 - (c / S) ^ 2)]
  field_simp
  nlinarith

/-- Common axial projection gives the actual transverse circle radius. -/
theorem common_projection_tangent_norm {w u : E} {a S : ℝ}
    (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (hproj : ⟪u, w⟫ = a)
    (hS : 0 ≤ S) (hcircle : S ^ 2 = 1 - a ^ 2) :
    ‖sphericalTangent w u‖ = S := by
  have h := sphericalTangent_inner (u := u) (v := u) hw
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hproj] at h
  nlinarith [norm_nonneg (sphericalTangent w u)]

/-- Translation to the transverse circle preserves chords. -/
theorem common_projection_tangent_dist {w u v : E} {a : ℝ}
    (hu : ⟪u, w⟫ = a) (hv : ⟪v, w⟫ = a) :
    dist (sphericalTangent w u) (sphericalTangent w v) = dist u v := by
  simp only [sphericalTangent, hu, hv, dist_sub_right]

/-- A positive chord between unit rays with equal axial projection excludes
a collapsed transverse circle; this is metric, independent of the fan lift. -/
theorem tangent_ne_zero_of_positive_chord {w u v : E}
    (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hproj : ⟪u, w⟫ = ⟪v, w⟫) (hchord : 0 < dist u v) :
    sphericalTangent w u ≠ 0 := by
  have hnu := sphericalTangent_inner (w := w) (u := u) (v := u) hw
  have hnv := sphericalTangent_inner (w := w) (u := v) (v := v) hw
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hproj] at hnu
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv] at hnv
  intro hz
  rw [hz, norm_zero] at hnu
  have hzv : sphericalTangent w v = 0 := norm_eq_zero.mp (by
    nlinarith [norm_nonneg (sphericalTangent w v)])
  have hd := common_projection_tangent_dist (a := ⟪u, w⟫) rfl hproj.symm
  rw [hz, hzv, dist_self] at hd
  linarith

/-- A strict minor arc forces the circle radius strictly above its half-chord. -/
theorem centralArc_lt_pi_iff {c S : ℝ} (hS : 0 < S) :
    centralArc c S < Real.pi ↔ c < S := by
  have he : centralArc c S < Real.pi ↔ Real.arcsin (c / S) < Real.pi / 2 := by
    dsimp [centralArc]; constructor <;> intro h <;> linarith
  rw [he, Real.arcsin_lt_pi_div_two, div_lt_one hS]

/-- A circle fan with the existing project's once-around lift has the actual
arcsine closure equation. Chords and norms alone determine every summand. -/
theorem circle_fan_arcs {n : ℕ} {v : ℕ → E} {c : ℕ → ℝ} {S : ℝ}
    (hS : 0 < S) (hv : ∀ i ≤ n, ‖v i‖ = S)
    (hc : ∀ i < n, 0 < c i)
    (hchord : ∀ i < n, dist (v i) (v (i + 1)) = 2 * c i)
    (fan : SphericalFanData n (fun i => angle (v i) (v (i + 1)))) :
    (∀ i < n, c i < S) ∧
      (∑ i ∈ Finset.range n, centralArc (c i) S) = 2 * Real.pi := by
  have hangle : ∀ i < n, angle (v i) (v (i + 1)) = centralArc (c i) S := by
    intro i hi
    exact angle_eq_centralArc hS (hc i hi).le (hv i (by omega))
      (hv (i + 1) (by omega)) (hchord i hi)
  constructor
  · intro i hi
    apply (centralArc_lt_pi_iff hS).mp
    rw [← hangle i hi]
    exact ((spherical_fan_closure fan).1 i hi).2
  · rw [← (spherical_fan_closure fan).2]
    exact Finset.sum_congr rfl (fun i hi => (hangle i (Finset.mem_range.mp hi)).symm)

/-- For unit rays with a common projection onto a unit pole, all transverse
norms and the closure function are derived from the ambient metric data. -/
theorem unit_ray_fan_arcs {n : ℕ} {w : E} {u : ℕ → E} {c : ℕ → ℝ} {a S : ℝ}
    (hw : ‖w‖ = 1) (hu : ∀ i ≤ n, ‖u i‖ = 1)
    (hproj : ∀ i ≤ n, ⟪u i, w⟫ = a)
    (hS : 0 < S) (hcircle : S ^ 2 = 1 - a ^ 2)
    (hc : ∀ i < n, 0 < c i)
    (hchord : ∀ i < n, dist (u i) (u (i + 1)) = 2 * c i)
    (fan : SphericalFanData n
      (fun i => angle (sphericalTangent w (u i)) (sphericalTangent w (u (i + 1))))) :
    (∀ i < n, c i < S) ∧
      (∑ i ∈ Finset.range n, centralArc (c i) S) = 2 * Real.pi := by
  apply circle_fan_arcs hS
    (fun i hi => common_projection_tangent_norm hw (hu i hi) (hproj i hi) hS.le hcircle) hc
    (fun i hi => ?_) fan
  rw [common_projection_tangent_dist (hproj i (by omega)) (hproj (i + 1) (by omega))]
  exact hchord i hi

end CircleGeometry

/-- Specialization to configurations of regular polygons. The paper's angle
condition supplies the strict upper endpoint inequality exactly. -/
theorem polygon_unique_root_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℕ) (hq : ∀ i, 3 ≤ q i)
    (hangle : ∑ i, (1 - 2 / (q i : ℝ)) < 2) :
    (∃! S, S ∈ Ioo (maxCos (fun i => polygonCos (q i))) 1 ∧
      arcSum (fun i => polygonCos (q i)) S = 2 * Real.pi) ↔
      2 * Real.pi < arcSum (fun i => polygonCos (q i))
        (maxCos (fun i => polygonCos (q i))) := by
  apply unique_root_iff (fun i => (polygonCos_bounds (hq i)).1)
    (fun i => (polygonCos_bounds (hq i)).2)
  rw [arcSum_polygon_one q hq]
  nlinarith [Real.pi_pos]

/-- The function and its maximum are invariant under any finite relabelling. -/
theorem maxCos_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (c : ι → ℝ) (e : κ ≃ ι) : maxCos (c ∘ e) = maxCos c := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (c ∘ e)).mpr
    exact fun i _ => le_maxCos c (e i)
  · apply (Finset.sup'_le_iff Finset.univ_nonempty c).mpr
    intro i _
    simpa only [Function.comp_apply, e.apply_symm_apply] using le_maxCos (c ∘ e) (e.symm i)

/-- Equal configurations up to permutation force the same circle radius and
therefore the same configuration radius. -/
theorem radius_unique_up_to_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] {c : ι → ℝ} (e : κ ≃ ι)
    (hc : ∀ i, 0 < c i) {S T : ℝ}
    (hS : S ∈ Ioo (maxCos c) 1) (hT : T ∈ Ioo (maxCos (c ∘ e)) 1)
    (hrS : arcSum c S = 2 * Real.pi) (hrT : arcSum (c ∘ e) T = 2 * Real.pi) :
    S = T ∧ radiusFromCircle S = radiusFromCircle T := by
  rw [maxCos_equiv c e] at hT
  rw [arcSum_equiv e] at hrT
  have heq := (arcSum_strictAntiOn hc).injOn
    (Ioo_subset_Icc_self hS) (Ioo_subset_Icc_self hT) (hrS.trans hrT.symm)
  exact ⟨heq, congrArg radiusFromCircle heq⟩

section TypeIGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sphere equation for a unit step perpendicular to the face plane
is exactly the axial projection equation used by the type-(i) argument. -/
theorem cospherical_unit_step_iff {x W u : E} (hu : ‖u‖ = 1)
    (horth : ⟪u, x⟫ = 0) :
    ‖x + u - W‖ ^ 2 = ‖x - W‖ ^ 2 ↔ ⟪u, W⟫ = 1 / 2 := by
  have hn := norm_add_sq_real u (x - W)
  have hv : u + (x - W) = x + u - W := by abel
  rw [hv, hu, inner_sub_right, horth] at hn
  constructor <;> intro h <;> nlinarith

/-- Positive height, normalized pole, and the transverse circle identity are
derived from unit-ray metric data. -/
theorem unit_ray_circle_identity {W u : E}
    (hu : ‖u‖ = 1) (hproj : ⟪u, W⟫ = 1 / 2) :
    0 < ‖W‖ ∧ ‖‖W‖⁻¹ • W‖ = 1 ∧
      ‖sphericalTangent (‖W‖⁻¹ • W) u‖ ^ 2 = 1 - 1 / (4 * ‖W‖ ^ 2) := by
  have hh : 0 < ‖W‖ := norm_pos_iff.mpr (by intro h; simp [h] at hproj)
  have hw := normalized_center_unit (w := W) rfl hh
  have hp : ⟪u, ‖W‖⁻¹ • W⟫ = 1 / (2 * ‖W‖) := by
    rw [real_inner_smul_right, hproj]; field_simp; ring
  refine ⟨hh, hw, ?_⟩
  have ht := sphericalTangent_inner (w := ‖W‖⁻¹ • W) (u := u) (v := u) hw
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hp] at ht
  rw [ht]
  ring

/-- The type-(i) analytic consequences of actual unit rays and chords. The
only global angular input is the pre-existing once-around fan lift. The
circle radius is the norm of the first projected ray, not an assumed root.
A positive chord excludes the collapsed circle without a nonzero-tangent
premise. -/
theorem typeI_from_unit_rays {n : ℕ} [NeZero n] {W : E} {u : ℕ → E} {c : ℕ → ℝ}
    (hu : ∀ i ≤ n, ‖u i‖ = 1)
    (hproj : ∀ i ≤ n, ⟪u i, W⟫ = 1 / 2)
    (hc : ∀ i < n, 0 < c i)
    (hchord : ∀ i < n, dist (u i) (u (i + 1)) = 2 * c i)
    (fan : SphericalFanData n
      (fun i => angle (sphericalTangent (‖W‖⁻¹ • W) (u i))
        (sphericalTangent (‖W‖⁻¹ • W) (u (i + 1))))) :
    let cf : Fin n → ℝ := fun i => c i
    let S := ‖sphericalTangent (‖W‖⁻¹ • W) (u 0)‖
    S ∈ Ioo (maxCos cf) 1 ∧ arcSum cf S = 2 * Real.pi ∧
      2 * Real.pi < arcSum cf (maxCos cf) ∧
      arcSum cf 1 < 2 * Real.pi ∧
      (∀ T ∈ Ioo (maxCos cf) 1, arcSum cf T = 2 * Real.pi → T = S) ∧
      ‖W‖ = radiusFromCircle S := by
  dsimp only
  let w := ‖W‖⁻¹ • W
  let S := ‖sphericalTangent w (u 0)‖
  obtain ⟨hh, hw, hcircle⟩ := unit_ray_circle_identity (hu 0 (by omega)) (hproj 0 (by omega))
  have hproj' : ∀ i ≤ n, ⟪u i, w⟫ = 1 / (2 * ‖W‖) := by
    intro i hi
    dsimp [w]
    rw [real_inner_smul_right, hproj i hi]; field_simp; ring
  have hdist : 0 < dist (u 0) (u 1) := by
    rw [hchord 0 (by have := NeZero.pos n; omega)]
    exact mul_pos (by norm_num) (hc 0 (by have := NeZero.pos n; omega))
  have ht := tangent_ne_zero_of_positive_chord hw (hu 0 (by omega))
    (hu 1 (by have := NeZero.pos n; omega))
    ((hproj' 0 (by omega)).trans (hproj' 1 (by have := NeZero.pos n; omega)).symm) hdist
  have hS : 0 < S := norm_pos_iff.mpr ht
  have hS1 : S < 1 := by
    have hp : 0 < 1 / (4 * ‖W‖ ^ 2) := by positivity
    change S ^ 2 = 1 - 1 / (4 * ‖W‖ ^ 2) at hcircle
    nlinarith
  have hcircle' : S ^ 2 = 1 - (1 / (2 * ‖W‖)) ^ 2 := by
    rw [hcircle]; ring
  obtain ⟨hminor, hsum⟩ := unit_ray_fan_arcs hw hu hproj' hS hcircle' hc hchord fan
  let cf : Fin n → ℝ := fun i => c i
  have hcf : ∀ i, 0 < cf i := fun i => hc i i.isLt
  have hmax : maxCos cf < S :=
    (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ => hminor i i.isLt)
  have hroot : arcSum cf S = 2 * Real.pi := by
    change (∑ i : Fin n, (fun j : ℕ => centralArc (c j) S) i.val) = 2 * Real.pi
    exact (Fin.sum_univ_eq_sum_range (fun j => centralArc (c j) S) n).trans hsum
  have hmem : S ∈ Ioo (maxCos cf) 1 := ⟨hmax, hS1⟩
  have hupper : arcSum cf 1 < 2 * Real.pi := by
    rw [← hroot]
    exact arcSum_strictAntiOn hcf (Ioo_subset_Icc_self hmem)
      ⟨hmax.le.trans hS1.le, le_rfl⟩ hS1
  refine ⟨hmem, hroot, closable_of_root hcf hmem hroot, hupper, ?_, ?_⟩
  · intro T hT hrT
    exact (arcSum_strictAntiOn hcf).injOn (Ioo_subset_Icc_self hT)
      (Ioo_subset_Icc_self hmem) (hrT.trans hroot.symm)
  · exact height_eq_radiusFromCircle hh hS.le hS1 hcircle

/-- The full-radius identity follows from genuine orthogonal displacements. -/
theorem orthogonal_full_radius_sq {x W : E} {S : ℝ}
    (hh : 0 < ‖W‖) (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hcircle : S ^ 2 = 1 - 1 / (4 * ‖W‖ ^ 2)) (horth : ⟪x, W⟫ = 0) :
    ‖x - W‖ ^ 2 = ‖x‖ ^ 2 + radiusFromCircle S ^ 2 := by
  rw [norm_sub_sq_real, horth, ← height_eq_radiusFromCircle hh hS0 hS1 hcircle]
  ring

end TypeIGeometry

/-- Degeneracy at the endpoint allows no other root in the admissible closed
interval, so in particular no strictly interior geometric fan. -/
theorem degenerate_root_only_at_max {ι : Type*} [Fintype ι] [Nonempty ι]
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) (hm : maxCos c ≤ 1)
    (hdegenerate : arcSum c (maxCos c) = 2 * Real.pi)
    {S : ℝ} (hS : S ∈ Icc (maxCos c) 1) (hroot : arcSum c S = 2 * Real.pi) :
    S = maxCos c :=
  (arcSum_strictAntiOn hc).injOn hS ⟨le_rfl, hm⟩ (hroot.trans hdegenerate.symm)

/-- Polygon half-chords increase with the number of sides. -/
theorem polygonCos_mono {q r : ℕ} (hq : 3 ≤ q) (hqr : q ≤ r) :
    polygonCos q ≤ polygonCos r := by
  have hr : 3 ≤ r := hq.trans hqr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqr' : (q : ℝ) ≤ r := by exact_mod_cast hqr
  apply Real.strictAntiOn_cos.antitoneOn
    ⟨(polygonAngle_bounds hr).1.le, by linarith [(polygonAngle_bounds hr).2, Real.pi_pos]⟩
    ⟨(polygonAngle_bounds hq).1.le, by linarith [(polygonAngle_bounds hq).2, Real.pi_pos]⟩
  exact div_le_div_of_nonneg_left Real.pi_pos.le hq0 hqr'

/-- The acute criterion specialized to regular polygon chords and a largest
polygon parameter. The triangle is an actual metric triangle in `E`. -/
theorem polygon_triple_closable_iff_acute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y z : E} {qa qb qd : ℕ} (ha : 3 ≤ qa) (hb : 3 ≤ qb)
    (had : qa ≤ qd) (hbd : qb ≤ qd)
    (hxy : dist x y = polygonChord qa) (hxz : dist x z = polygonChord qb)
    (hyz : dist y z = polygonChord qd) :
    (2 * Real.pi < arcSum ![polygonCos qa, polygonCos qb, polygonCos qd]
      (maxCos ![polygonCos qa, polygonCos qb, polygonCos qd])) ↔ AcuteTriangle x y z :=
  triple_closable_iff_acute (polygonCos_bounds ha).1 (polygonCos_bounds hb).1
    (polygonCos_mono ha had) (polygonCos_mono hb hbd) hxy hxz hyz

/-- Collect the exact polygon version: the unique interior root, strict
closability, the actual height formula, the bound for every entry (including
q_max), and the orthogonal full-radius identity. -/
theorem typeI_polygon_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [NeZero n] {x W : E} {u : ℕ → E} {q : ℕ → ℕ}
    (hu : ∀ i ≤ n, ‖u i‖ = 1)
    (hproj : ∀ i ≤ n, ⟪u i, W⟫ = 1 / 2)
    (hq : ∀ i < n, 3 ≤ q i)
    (hchord : ∀ i < n, dist (u i) (u (i + 1)) = polygonChord (q i))
    (fan : SphericalFanData n
      (fun i => angle (sphericalTangent (‖W‖⁻¹ • W) (u i))
        (sphericalTangent (‖W‖⁻¹ • W) (u (i + 1)))))
    (horth : ⟪x, W⟫ = 0) :
    let cf : Fin n → ℝ := fun i => polygonCos (q i)
    let S := ‖sphericalTangent (‖W‖⁻¹ • W) (u 0)‖
    (∃! T, T ∈ Ioo (maxCos cf) 1 ∧ arcSum cf T = 2 * Real.pi) ∧
      2 * Real.pi < arcSum cf (maxCos cf) ∧
      ‖W‖ = radiusFromCircle S ∧
      (∀ i < n, regularPolygonRadiusNat (q i) ≤ radiusFromCircle S) ∧
      ‖x - W‖ ^ 2 = ‖x‖ ^ 2 + radiusFromCircle S ^ 2 := by
  dsimp only
  let cf : Fin n → ℝ := fun i => polygonCos (q i)
  let S := ‖sphericalTangent (‖W‖⁻¹ • W) (u 0)‖
  obtain ⟨hmem, hroot, hclose, _, huniq, hheight⟩ := typeI_from_unit_rays hu hproj
    (fun i hi => (polygonCos_bounds (hq i hi)).1) hchord fan
  refine ⟨⟨S, ⟨hmem, hroot⟩, fun T hT => huniq T hT.1 hT.2⟩,
    hclose, hheight, ?_, ?_⟩
  · intro i hi
    apply regularPolygonRadiusNat_le_radiusFromCircle (hq i hi) _ hmem.2
    exact (le_maxCos cf ⟨i, hi⟩).trans hmem.1.le
  · calc
      _ = ‖x‖ ^ 2 + ‖W‖ ^ 2 := by rw [norm_sub_sq_real, horth]; ring
      _ = _ := congrArg (fun t : ℝ => ‖x‖ ^ 2 + t ^ 2) hheight

end Uniform5.CaseB
