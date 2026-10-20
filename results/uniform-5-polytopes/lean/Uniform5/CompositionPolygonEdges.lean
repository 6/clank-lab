import Uniform5.CompositionEmbeddingReverse
import Uniform5.CompositionPolygonSymmetry
import Uniform5.CaseBProducts

/-!
# Actual edges and unit-radius normalization of regular polygons

The first chord is nearest among all chords from its endpoint, by the
monotonicity and reflection symmetry of cosine. The previously proved
nearest-vertex theorem therefore makes it an actual exposed edge.
-/

noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace

/-- Squared chord length from the initial circular vertex. -/
theorem polygonPoint_dist_zero_sq {n : ℕ} [NeZero n] (r : ℝ) (i : Fin n) :
    dist (polygonPoint n r ⟨0, NeZero.pos n⟩) (polygonPoint n r i) ^ 2 =
      2 * r ^ 2 * (1 - Real.cos (2 * Real.pi * (i : ℕ) / n)) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [polygonPoint, Fin.sum_univ_two, PiLp.sub_apply,
    WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div,
    Real.cos_zero, Real.sin_zero, mul_one, zero_sub, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * (i : ℕ) / n)]

/-- The first side has the usual positive chord length. -/
theorem polygonPoint_first_dist (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    dist (polygonPoint n r ⟨0, by omega⟩) (polygonPoint n r ⟨1, by omega⟩) =
      2 * r * Real.sin (Real.pi / n) := by
  letI : NeZero n := ⟨by omega⟩
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : 0 < Real.sin (Real.pi / n) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hn')
  apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
  have hh := polygonPoint_dist_zero_sq r (⟨1, by omega⟩ : Fin n)
  have ha : 2 * Real.pi * (1 : ℕ) / n = 2 * (Real.pi / n) := by ring
  rw [ha, Real.cos_two_mul] at hh
  nlinarith [congrArg (fun x : ℝ => 4 * r ^ 2 * x)
    (Real.sin_sq_add_cos_sq (Real.pi / n))]

private theorem polygon_cos_le_first {n : ℕ} (hn : 3 ≤ n) (i : Fin n)
    (hi : (i : ℕ) ≠ 0) :
    Real.cos (2 * Real.pi * (i : ℕ) / n) ≤ Real.cos (2 * Real.pi / n) := by
  let θ : ℝ := 2 * Real.pi / n
  have hn' : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have ht : 0 < θ := div_pos (mul_pos (by norm_num) Real.pi_pos) (by linarith)
  have htπ : θ < Real.pi := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    nlinarith [Real.pi_pos]
  have hi1 : (1 : ℝ) ≤ (i : ℕ) := by exact_mod_cast (show 1 ≤ (i : ℕ) by omega)
  have hin : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have hθn : θ * n = 2 * Real.pi := div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hlow : θ ≤ θ * (i : ℕ) := le_mul_of_one_le_right ht.le hi1
  have hupp : θ * (i : ℕ) ≤ 2 * Real.pi - θ := by
    have hh := mul_le_mul_of_nonneg_left hin ht.le
    nlinarith
  have ha : 2 * Real.pi * (i : ℕ) / n = θ * (i : ℕ) := by dsimp [θ]; ring
  rw [ha]
  change Real.cos (θ * (i : ℕ)) ≤ Real.cos θ
  by_cases hhalf : θ * (i : ℕ) ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi ht.le hhalf hlow
  · have hh := Real.cos_le_cos_of_nonneg_of_le_pi ht.le
      (show 2 * Real.pi - θ * (i : ℕ) ≤ Real.pi by linarith)
      (show θ ≤ 2 * Real.pi - θ * (i : ℕ) by linarith)
    simpa only [Real.cos_two_pi_sub] using hh

/-- The first circular chord is shortest among distinct vertices from the
initial vertex; the final vertex may tie it. -/
theorem polygonPoint_first_nearest (n : ℕ) (r : ℝ) (hn : 3 ≤ n)
    (i : Fin n) (hi : polygonPoint n r i ≠ polygonPoint n r ⟨0, by omega⟩) :
    dist (polygonPoint n r ⟨0, by omega⟩) (polygonPoint n r ⟨1, by omega⟩) ≤
      dist (polygonPoint n r ⟨0, by omega⟩) (polygonPoint n r i) := by
  letI : NeZero n := ⟨by omega⟩
  have hi0 : (i : ℕ) ≠ 0 := by
    intro hh
    apply hi
    have he : i = ⟨0, by omega⟩ := Fin.ext hh
    exact congrArg (polygonPoint n r) he
  have hcos := polygon_cos_le_first hn i hi0
  have h0 := polygonPoint_dist_zero_sq r (⟨1, by omega⟩ : Fin n)
  have h1 := polygonPoint_dist_zero_sq r i
  simp only [Nat.cast_one, mul_one] at h0
  have hr2 := sq_nonneg r
  have hmul := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * r ^ 2 by positivity)
  nlinarith [dist_nonneg (x := polygonPoint n r ⟨0, by omega⟩)
    (y := polygonPoint n r ⟨1, by omega⟩),
    dist_nonneg (x := polygonPoint n r ⟨0, by omega⟩) (y := polygonPoint n r i)]

/-- Every circular generator is an actual extreme point. -/
theorem polygon_extremePoints (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (polygon n r).extremePoints ℝ = Set.range (polygonPoint n r) := by
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  apply CaseB.cospherical_extremePoints (c := (0 : Plane)) (R := r)
  rintro x ⟨i, rfl⟩
  rw [Metric.mem_sphere, dist_zero_right]
  exact (sq_eq_sq₀ (norm_nonneg _) hr).mp (polygonPoint_norm_sq n r i)

/-- The initial consecutive chord is an actual exposed edge, not an edge
label supplied as input. -/
theorem polygon_first_edge (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    Edge (polygon n r) (polygonPoint n r ⟨0, by omega⟩)
      (polygonPoint n r ⟨1, by omega⟩) := by
  classical
  let V : Finset Plane := Finset.univ.image (polygonPoint n r)
  have hV : (V : Set Plane) = Set.range (polygonPoint n r) := by simp [V]
  have hv : polygonPoint n r ⟨0, by omega⟩ ∈ V := by simp [V]
  have hw : polygonPoint n r ⟨1, by omega⟩ ∈ V := by simp [V]
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : 0 < Real.sin (Real.pi / n) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hn')
  have hdist : 0 < dist (polygonPoint n r ⟨0, by omega⟩)
      (polygonPoint n r ⟨1, by omega⟩) := by
    rw [polygonPoint_first_dist n r hn hr]
    positivity
  have he := nearest_isEdge V (c := (0 : Plane)) (R := r)
    (fun x hx => by
      change x ∈ (V : Set Plane) at hx
      rw [hV] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa only [sub_zero] using polygonPoint_norm_sq n r i)
    hv hw (dist_pos.mp hdist) (fun x hx hne => by
      change x ∈ (V : Set Plane) at hx
      rw [hV] at hx
      obtain ⟨i, rfl⟩ := hx
      exact polygonPoint_first_nearest n r hn i hne)
  refine ⟨?_, ?_, he.2.2.1, ?_⟩
  · rw [polygon_extremePoints n r hr.le]
    exact Set.mem_range_self _
  · rw [polygon_extremePoints n r hr.le]
    exact Set.mem_range_self _
  · simpa only [polygon, hV] using he.2.2.2

/-- Every consecutive chord, including the closing chord, is an actual
exposed edge by the proved ambient rotations. -/
theorem polygon_consecutive_edge {n : ℕ} [NeZero n] (r : ℝ)
    (hn : 3 ≤ n) (hr : 0 < r) (i : Fin n) :
    Edge (polygon n r) (polygonPoint n r i) (polygonPoint n r (i + 1)) := by
  let g := planeRotation (2 * Real.pi * (i : ℕ) / n)
  have hz : (0 : Fin n) = ⟨0, by omega⟩ := by ext; simp
  have ho : (1 : Fin n) = ⟨1, by omega⟩ := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  have he := edge_image g (polygon_first_edge n r hn hr)
  rw [← hz, ← ho] at he
  have hgP : g '' polygon n r = polygon n r := polygon_rotation_image r i
  have hg0 : g (polygonPoint n r 0) = polygonPoint n r i := by
    simpa using polygon_rotation_index r i 0
  have hg1 : g (polygonPoint n r 1) = polygonPoint n r (i + 1) :=
    polygon_rotation_index r i 1
  rwa [hgP, hg0, hg1] at he

/-- All consecutive sides have the same exact positive chord length. -/
theorem polygon_consecutive_dist {n : ℕ} [NeZero n] (r : ℝ)
    (hn : 3 ≤ n) (hr : 0 < r) (i : Fin n) :
    dist (polygonPoint n r i) (polygonPoint n r (i + 1)) =
      2 * r * Real.sin (Real.pi / n) := by
  let g := planeRotation (2 * Real.pi * (i : ℕ) / n)
  have hz : (0 : Fin n) = ⟨0, by omega⟩ := by ext; simp
  have ho : (1 : Fin n) = ⟨1, by omega⟩ := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  have hg0 : g (polygonPoint n r 0) = polygonPoint n r i := by
    simpa using polygon_rotation_index r i 0
  have hg1 : g (polygonPoint n r 1) = polygonPoint n r (i + 1) :=
    polygon_rotation_index r i 1
  rw [← hg0, ← hg1, g.dist_map, hz, ho]
  exact polygonPoint_first_dist n r hn hr

/-- Unit length of actual edges forces the paper's prescribed circumradius. -/
theorem polygon_radius_eq_unit (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r)
    (hunit : UnitEdges (polygon n r)) : r = unitPolygonRadius n := by
  have hd := hunit _ _ (polygon_first_edge n r hn hr)
  rw [polygonPoint_first_dist n r hn hr] at hd
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : 0 < Real.sin (Real.pi / n) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hn')
  unfold unitPolygonRadius
  apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) hs))).mpr
  nlinarith

/-- Every two-dimensional unit uniform hull is an actual isometric image
of one of the explicit unit-radius regular polygons. -/
theorem unitUniform_two_unitPolygon {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {P : Set E}
    (hP : UnitUniform 2 P) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ f : Plane →ᵃⁱ[ℝ] E, P = f '' unitPolygon n := by
  obtain ⟨hu, he⟩ := hP
  rw [Uniform] at hu
  obtain ⟨n, hn, r, hr, f, rfl⟩ := hu
  have hun := embedding_unitEdges_reflect f he
  have hrad := polygon_radius_eq_unit n r hn hr hun
  exact ⟨n, hn, f, by rw [hrad]; rfl⟩

/-- The intrinsic form of unit-polygon normalization. -/
theorem unitUniform_two_congruent_unitPolygon {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {P : Set E}
    (hP : UnitUniform 2 P) : ∃ n : ℕ, 3 ≤ n ∧ Congruent P (unitPolygon n) := by
  obtain ⟨n, hn, f, rfl⟩ := unitUniform_two_unitPolygon hP
  exact ⟨n, hn, congruent_symm (congruent_affineIsometry_image f _)⟩

end Uniform5.Composition
