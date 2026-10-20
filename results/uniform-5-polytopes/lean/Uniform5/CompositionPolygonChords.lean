import Uniform5.CompositionPolygonIncidence
import Uniform5.CompositionFigureRidgeCorrespondence

/-!
# Chords between actual polygon neighbors

The two distinct edge neighbors of a vertex of a unit regular k-gon have
mutual distance `2 cos (π/k)`. The result applies to actual edges of actual
polygon faces of a unit-uniform polytope, without an assumed cyclic labeling.
-/

noncomputable section
namespace Uniform5.Composition
open Set

/-- The chord that skips one circular vertex has the double-angle length. -/
theorem polygonPoint_second_dist (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    dist (polygonPoint n r ⟨0, by omega⟩) (polygonPoint n r ⟨2, by omega⟩) =
      2 * r * Real.sin (2 * Real.pi / n) := by
  letI : NeZero n := ⟨by omega⟩
  have hn' : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have htpos : 0 < 2 * Real.pi / n := by positivity
  have htpi : 2 * Real.pi / n < Real.pi := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    nlinarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi htpos htpi
  apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
  have hh := polygonPoint_dist_zero_sq r (⟨2, by omega⟩ : Fin n)
  have ha : 2 * Real.pi * (2 : ℕ) / n = 2 * (2 * Real.pi / n) := by ring
  rw [ha, Real.cos_two_mul] at hh
  nlinarith [congrArg (fun x : ℝ => 4 * r ^ 2 * x)
    (Real.sin_sq_add_cos_sq (2 * Real.pi / n))]

/-- In a unit polygon the chord across two consecutive sides has length
`2 cos (π/n)`, including the triangular case. -/
theorem unitPolygon_second_dist {n : ℕ} (hn : 3 ≤ n) :
    dist (polygonPoint n (unitPolygonRadius n) ⟨0, by omega⟩)
      (polygonPoint n (unitPolygonRadius n) ⟨2, by omega⟩) =
      2 * Real.cos (Real.pi / n) := by
  rw [polygonPoint_second_dist n _ hn (unitPolygonRadius_pos hn)]
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := ne_of_gt <|
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (div_lt_self Real.pi_pos hn')
  rw [show 2 * Real.pi / n = 2 * (Real.pi / n) by ring, Real.sin_two_mul]
  unfold unitPolygonRadius
  field_simp
  ring

/-- The two actual polygon edges at the vertex with index one span its plane. -/
theorem polygon_second_neighbors_span (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    Submodule.span ℝ ({
      polygonPoint n r ⟨0, by omega⟩ - polygonPoint n r ⟨1, by omega⟩,
      polygonPoint n r ⟨2, by omega⟩ - polygonPoint n r ⟨1, by omega⟩} : Set Plane) = ⊤ := by
  let p₀ := polygonPoint n r ⟨0, by omega⟩
  let p₁ := polygonPoint n r ⟨1, by omega⟩
  let p₂ := polygonPoint n r ⟨2, by omega⟩
  let M := Submodule.span ℝ ({p₀ - p₁, p₂ - p₁} : Set Plane)
  have h₀ : p₀ - p₁ ∈ M := Submodule.subset_span (Set.mem_insert _ _)
  have h₂ : p₂ - p₁ ∈ M :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  change M = ⊤
  apply top_unique
  rw [← polygon_first_differences_span n r hn hr]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  fin_cases i
  · change p₁ - p₀ ∈ M
    simpa only [neg_sub] using M.neg_mem h₀
  · change p₂ - p₀ ∈ M
    simpa only [sub_sub_sub_cancel_right] using M.sub_mem h₂ h₀

/-- The chord length is determined by two distinct actual incident edges;
there is no input choosing their cyclic labels. -/
theorem unitPolygon_neighbor_chord {n : ℕ} (hn : 3 ≤ n) {v a b : Plane}
    (ha : Edge (unitPolygon n) v a) (hb : Edge (unitPolygon n) v b) (hab : a ≠ b) :
    dist a b = 2 * Real.cos (Real.pi / n) := by
  letI : NeZero n := ⟨by omega⟩
  let r := unitPolygonRadius n
  have hr : 0 < r := unitPolygonRadius_pos hn
  obtain ⟨i, rfl⟩ := (polygon_extremePoints n r hr.le) ▸ ha.1
  let j : Fin n := i - 1
  let g := planeRotation (2 * Real.pi * (j : ℕ) / n)
  have h₁ : (1 : Fin n) = ⟨1, by omega⟩ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  have h₂ : (2 : Fin n) = ⟨2, by omega⟩ := by
    apply Fin.ext
    change 2 % n = 2
    exact Nat.mod_eq_of_lt (show 2 < n by omega)
  have hg1 : g (polygonPoint n r ⟨1, by omega⟩) = polygonPoint n r i := by
    rw [← h₁]
    simpa [j] using polygon_rotation_index r j 1
  have hgP : g '' polygon n r = polygon n r := polygon_rotation_image r j
  have hgP' : g.symm '' polygon n r = polygon n r := by
    conv_lhs => rw [← hgP]
    exact affineIsometry_symm_image_image g _
  have hae := edge_image g.symm ha
  have hbe := edge_image g.symm hb
  change Edge (g.symm '' polygon n r) _ _ at hae hbe
  rw [hgP', ← hg1, g.symm_apply_apply] at hae hbe
  have he0 : Edge (polygon n r) (polygonPoint n r ⟨1, by omega⟩)
      (polygonPoint n r ⟨0, by omega⟩) := by
    have h := polygon_first_edge n r hn hr
    refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
    rw [segment_symm]
    exact h.2.2.2
  have he2 : Edge (polygon n r) (polygonPoint n r ⟨1, by omega⟩)
      (polygonPoint n r ⟨2, by omega⟩) := by
    have h := polygon_consecutive_edge r hn hr (1 : Fin n)
    have hh : (1 : Fin n) + 1 = (2 : Fin n) := by
      apply Fin.ext
      rw [Fin.val_add, h₁, h₂]
      exact Nat.mod_eq_of_lt (show 2 < n by omega)
    rw [hh, h₁, h₂] at h
    exact h
  have h02 : polygonPoint n r ⟨0, by omega⟩ ≠ polygonPoint n r ⟨2, by omega⟩ := by
    intro h
    have hi := polygonPoint_injective n r hn hr h
    have hv := congrArg Fin.val hi
    norm_num at hv
  have haends := edge_of_two_spanning_edges he0 he2 h02
    (polygon_second_neighbors_span n r hn hr) hae
  have hbends := edge_of_two_spanning_edges he0 he2 h02
    (polygon_second_neighbors_span n r hn hr) hbe
  have hab' : g.symm a ≠ g.symm b := fun h => hab (g.symm.injective h)
  rw [← g.symm.dist_map]
  rcases haends with ha0 | ha2 <;> rcases hbends with hb0 | hb2
  · exact (hab' (ha0.trans hb0.symm)).elim
  · rw [ha0, hb2]
    exact unitPolygon_second_dist hn
  · rw [ha2, hb0, dist_comm]
    exact unitPolygon_second_dist hn
  · exact (hab' (ha2.trans hb2.symm)).elim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Two distinct actual neighbors in an actual k-gonal face of a unit-uniform
polytope have the chord length used for the vertex-figure metric. -/
theorem polygonFace_neighbor_chord {n k : ℕ} {P F : Set E}
    (hP : UnitUniform (n + 3) P) (hF : PolygonFace P F k) {v a b : E}
    (ha : Edge F v a) (hb : Edge F v b) (hab : a ≠ b) :
    dist a b = 2 * Real.cos (Real.pi / k) := by
  obtain ⟨hk, f, hrep⟩ := polygonFace_unitPolygon hP hF
  have hv := ha.1.1
  have ha' := ha.2.1.1
  have hb' := hb.2.1.1
  rw [hrep] at hv ha' hb'
  obtain ⟨v₀, hv₀, rfl⟩ := hv
  obtain ⟨a₀, ha₀, rfl⟩ := ha'
  obtain ⟨b₀, hb₀, rfl⟩ := hb'
  rw [hrep] at ha hb
  rw [f.dist_map]
  exact unitPolygon_neighbor_chord hk (embedding_edge_reflect f ha)
    (embedding_edge_reflect f hb) (fun h => hab (congrArg f h))

/-- Every actual edge of the metric vertex figure has length `2 cos (π/k)`
for the actual vertex count of its corresponding polygon face. -/
theorem unitUniform5_vertexFigure_edge_length {P : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ) {x y : E}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y) :
    ∃ F k, PolygonFace P F k ∧ 3 ≤ k ∧
      dist x y = 2 * Real.cos (Real.pi / k) := by
  obtain ⟨F, k, hF, _, hx, hy, hxy, _⟩ :=
    unitUniform5_vertexFigure_edge_polygon hP hv he
  exact ⟨F, k, hF, (polygonFace_unitPolygon (n := 2) hP hF).1,
    polygonFace_neighbor_chord (n := 2) hP hF hx hy hxy⟩

/-- Each actual polygon face through the apex contributes a vertex-figure
edge with the corresponding cosine length. -/
theorem unitUniform5_polygon_vertexFigure_edge_length {P F : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    {k : ℕ} (hF : PolygonFace P F k) (hvF : v ∈ F) :
    ∃ x y, Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y ∧
      dist x y = 2 * Real.cos (Real.pi / k) := by
  obtain ⟨x, y, he, hx, hy, _⟩ := unitUniform5_polygon_vertexFigure_edge hP hv hF hvF
  exact ⟨x, y, he, polygonFace_neighbor_chord (n := 2) hP hF hx hy he.2.2.1⟩

end Uniform5.Composition
