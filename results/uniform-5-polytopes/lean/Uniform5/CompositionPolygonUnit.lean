import Uniform5.CompositionPolygonEdges

/-!
# All exposed edges of the explicit unit regular polygon are unit

Two distinct exposed edge directions spanning the ambient plane exhaust
all edge directions at their common vertex. Applying this geometric fact
to the two circular neighbors excludes nonconsecutive exposed chords.
-/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem edge_support {P : Set E} {v a : E} (h : Edge P v a) :
    ∃ l : E →L[ℝ] ℝ, l a = l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
      ∀ x ∈ P, l x = l v → x ∈ segment ℝ v a := by
  obtain ⟨l, hl⟩ := h.2.2.2 ⟨v, left_mem_segment ℝ v a⟩
  have hv : v ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
    rw [← hl]
    exact left_mem_segment ℝ v a
  have ha : a ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
    rw [← hl]
    exact right_mem_segment ℝ v a
  refine ⟨l, le_antisymm (hv.2 a ha.1) (ha.2 v hv.1), hv.2, ?_⟩
  intro x hx heq
  rw [hl]
  exact ⟨hx, fun y hy => heq ▸ hv.2 y hy⟩

private theorem extreme_segment_endpoints {P : Set E} {v a x : E}
    (hx : x ∈ P.extremePoints ℝ) (hv : v ∈ P) (ha : a ∈ P)
    (hseg : x ∈ segment ℝ v a) : x = v ∨ x = a := by
  obtain h | h := (mem_extremePoints_iff_forall_segment.mp hx).2 v hv a ha hseg
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- At a corner whose two distinct exposed edge directions span the
ambient space, these are all the exposed edges incident with that corner. -/
theorem edge_of_two_spanning_edges {P : Set E} {v a b z : E}
    (ha : Edge P v a) (hb : Edge P v b) (hab : a ≠ b)
    (hspan : Submodule.span ℝ ({a - v, b - v} : Set E) = ⊤)
    (hz : Edge P v z) : z = a ∨ z = b := by
  obtain ⟨l, hla, hlmax, hlface⟩ := edge_support ha
  obtain ⟨m, hmb, hmmax, hmface⟩ := edge_support hb
  have hlb : l b < l v := by
    refine lt_of_le_of_ne (hlmax b hb.2.1.1) ?_
    intro heq
    obtain h | h := extreme_segment_endpoints hb.2.1 ha.1.1 ha.2.1.1
      (hlface b hb.2.1.1 heq)
    · exact hb.2.2.1 h.symm
    · exact hab h.symm
  have hma : m a < m v := by
    refine lt_of_le_of_ne (hmmax a ha.2.1.1) ?_
    intro heq
    obtain h | h := extreme_segment_endpoints ha.2.1 hb.1.1 hb.2.1.1
      (hmface a ha.2.1.1 heq)
    · exact ha.2.2.1 h.symm
    · exact hab h
  have hmem : z - v ∈ Submodule.span ℝ ({a - v, b - v} : Set E) := by
    rw [hspan]
    trivial
  obtain ⟨α, β, hc⟩ := Submodule.mem_span_pair.mp hmem
  have hcl := congrArg l hc
  have hcm := congrArg m hc
  simp only [map_add, map_smul, map_sub, smul_eq_mul, hla, hmb,
    sub_self, mul_zero, zero_add, add_zero] at hcl hcm
  have hα : 0 ≤ α := by
    have hh := hmmax z hz.2.1.1
    nlinarith
  have hβ : 0 ≤ β := by
    have hh := hlmax z hz.2.1.1
    nlinarith
  by_cases ha0 : α = 0
  · have hmeq : m z = m v := by simp only [ha0, zero_mul] at hcm; linarith
    obtain h | h := extreme_segment_endpoints hz.2.1 hb.1.1 hb.2.1.1
      (hmface z hz.2.1.1 hmeq)
    · exact (hz.2.2.1 h.symm).elim
    · exact Or.inr h
  by_cases hb0 : β = 0
  · have hleq : l z = l v := by simp only [hb0, zero_mul] at hcl; linarith
    obtain h | h := extreme_segment_endpoints hz.2.1 ha.1.1 ha.2.1.1
      (hlface z hz.2.1.1 hleq)
    · exact (hz.2.2.1 h.symm).elim
    · exact Or.inl h
  have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm ha0)
  have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hb0)
  obtain ⟨k, hkz, hkmax, hkface⟩ := edge_support hz
  have hck := congrArg k hc
  simp only [map_add, map_smul, map_sub, smul_eq_mul, hkz, sub_self] at hck
  have hka : k a = k v := by
    have haa := hkmax a ha.2.1.1
    have hbb := hkmax b hb.2.1.1
    by_contra hh
    have hneg := mul_neg_of_pos_of_neg hαpos (sub_neg.mpr (lt_of_le_of_ne haa hh))
    have hnon := mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr hbb)
    linarith
  have hkb : k b = k v := by
    rw [hka] at hck
    have heq : β * (k b - k v) = 0 := by simpa using hck
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hb0)
  have haz : a = z := by
    obtain h | h := extreme_segment_endpoints ha.2.1 hz.1.1 hz.2.1.1
      (hkface a ha.2.1.1 hka)
    · exact (ha.2.2.1 h.symm).elim
    · exact h
  have hbz : b = z := by
    obtain h | h := extreme_segment_endpoints hb.2.1 hz.1.1 hz.2.1.1
      (hkface b hb.2.1.1 hkb)
    · exact (hb.2.2.1 h.symm).elim
    · exact h
  exact (hab (haz.trans hbz.symm)).elim

private theorem polygon_last_point (n : ℕ) (r : ℝ) (hn : 3 ≤ n) :
    polygonPoint n r ⟨n - 1, by omega⟩ =
      !₂[r * Real.cos (2 * Real.pi / n), -r * Real.sin (2 * Real.pi / n)] := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ha : 2 * Real.pi * ((n - 1 : ℕ) : ℝ) / n = 2 * Real.pi - 2 * Real.pi / n := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    field_simp
    ring
  simp [polygonPoint, ha, Real.cos_two_pi_sub, Real.sin_two_pi_sub, mul_neg]

/-- The two circular neighbor directions span the entire plane. -/
theorem polygon_neighbors_span (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    Submodule.span ℝ ({
      polygonPoint n r ⟨1, by omega⟩ - polygonPoint n r ⟨0, by omega⟩,
      polygonPoint n r ⟨n - 1, by omega⟩ - polygonPoint n r ⟨0, by omega⟩} : Set Plane) = ⊤ := by
  have hrel :
      polygonPoint n r ⟨2, by omega⟩ - polygonPoint n r ⟨0, by omega⟩ =
      (2 * Real.cos (2 * Real.pi / n) + 1) •
        (polygonPoint n r ⟨1, by omega⟩ - polygonPoint n r ⟨0, by omega⟩) +
        (polygonPoint n r ⟨n - 1, by omega⟩ - polygonPoint n r ⟨0, by omega⟩) := by
    have ha : 2 * Real.pi * (2 : ℕ) / n = 2 * (2 * Real.pi / n) := by ring
    have hp2 : polygonPoint n r ⟨2, by omega⟩ =
        !₂[r * (2 * Real.cos (2 * Real.pi / n) ^ 2 - 1),
          r * (2 * Real.sin (2 * Real.pi / n) * Real.cos (2 * Real.pi / n))] := by
      unfold polygonPoint Uniform5.regularPolygonVertex
      rw [ha, Real.cos_two_mul, Real.sin_two_mul]
    rw [hp2, polygon_last_point n r hn]
    ext i
    fin_cases i <;> simp [polygonPoint] <;> ring
  apply top_unique
  rw [← polygon_first_differences_span n r hn hr]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · simp only [Matrix.cons_val_one, Matrix.head_cons]
    rw [hrel]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem polygon_neighbors_ne (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    polygonPoint n r ⟨1, by omega⟩ ≠ polygonPoint n r ⟨n - 1, by omega⟩ := by
  have hn' : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have htpos : 0 < 2 * Real.pi / n := by positivity
  have htpi : 2 * Real.pi / n < Real.pi := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    nlinarith [Real.pi_pos]
  have hs := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi htpos htpi)
  intro hh
  rw [polygon_last_point n r hn] at hh
  have hy := congrArg (fun x : Plane => x 1) hh
  simp [polygonPoint] at hy
  linarith

private theorem polygon_left_edge (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    Edge (polygon n r) (polygonPoint n r ⟨0, by omega⟩)
      (polygonPoint n r ⟨n - 1, by omega⟩) := by
  letI : NeZero n := ⟨by omega⟩
  let j : Fin n := ⟨n - 1, by omega⟩
  have hj : j + 1 = ⟨0, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_add]
    have h1 : ((1 : Fin n) : ℕ) = 1 := by simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
    rw [h1]
    change (n - 1 + 1) % n = 0
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  have he := polygon_consecutive_edge r hn hr j
  rw [hj] at he
  refine ⟨he.2.1, he.1, he.2.2.1.symm, ?_⟩
  rw [segment_symm]
  exact he.2.2.2

private theorem polygon_left_dist (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    dist (polygonPoint n r ⟨0, by omega⟩) (polygonPoint n r ⟨n - 1, by omega⟩) =
      2 * r * Real.sin (Real.pi / n) := by
  letI : NeZero n := ⟨by omega⟩
  have hsq := polygonPoint_dist_zero_sq r (⟨n - 1, by omega⟩ : Fin n)
  have hsq' := polygonPoint_dist_zero_sq r (⟨1, by omega⟩ : Fin n)
  have ha : 2 * Real.pi * ((n - 1 : ℕ) : ℝ) / n = 2 * Real.pi - 2 * Real.pi / n := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    field_simp
    ring
  rw [ha, Real.cos_two_pi_sub] at hsq
  simp only [Nat.cast_one, mul_one] at hsq'
  have heq := (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (hsq.trans hsq'.symm)
  rw [heq]
  exact polygonPoint_first_dist n r hn hr

/-- Every actual exposed edge of the explicit regular polygon has the
consecutive chord length. Nonconsecutive chords cannot be exposed edges. -/
theorem polygon_edge_length (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r)
    {v w : Plane} (he : Edge (polygon n r) v w) :
    dist v w = 2 * r * Real.sin (Real.pi / n) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨i, rfl⟩ := (polygon_extremePoints n r hr.le) ▸ he.1
  let g := planeRotation (2 * Real.pi * (i : ℕ) / n)
  have hz : (0 : Fin n) = ⟨0, by omega⟩ := by ext; simp
  have hg0 : g (polygonPoint n r ⟨0, by omega⟩) = polygonPoint n r i := by
    rw [← hz]
    simpa using polygon_rotation_index r i 0
  have hgP : g '' polygon n r = polygon n r := polygon_rotation_image r i
  have hgP' : g.symm '' polygon n r = polygon n r := by
    conv_lhs => rw [← hgP]
    exact affineIsometry_symm_image_image g _
  have he' := edge_image g.symm he
  rw [hgP', ← hg0, g.symm_apply_apply] at he'
  have hends := edge_of_two_spanning_edges (polygon_first_edge n r hn hr)
    (polygon_left_edge n r hn hr) (polygon_neighbors_ne n r hn hr)
    (polygon_neighbors_span n r hn hr) he'
  rw [← g.symm.dist_map, ← hg0, g.symm_apply_apply]
  obtain h | h := hends
  · rw [h]
    exact polygonPoint_first_dist n r hn hr
  · rw [h]
    exact polygon_left_dist n r hn hr

/-- The explicit radius really makes every actual exposed edge unit. -/
theorem unitEdges_unitPolygon {n : ℕ} (hn : 3 ≤ n) : UnitEdges (unitPolygon n) := by
  intro v w he
  have hh := polygon_edge_length n (unitPolygonRadius n) hn (unitPolygonRadius_pos hn) he
  rw [hh]
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := ne_of_gt <| Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hn')
  unfold unitPolygonRadius
  field_simp

/-- Concrete unit regular polygons satisfy the complete recursive geometric
unit-uniform definition. -/
theorem unitUniform_unitPolygon {n : ℕ} (hn : 3 ≤ n) : UnitUniform 2 (unitPolygon n) :=
  ⟨uniform_unitPolygon hn, unitEdges_unitPolygon hn⟩

/-- The geometric two-dimensional unit-uniform predicate is exactly the
class of affine-isometric images of the explicit unit regular polygons. -/
theorem unitUniform_two_iff_unitPolygon {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (P : Set F) :
    UnitUniform 2 P ↔
      ∃ n : ℕ, 3 ≤ n ∧ ∃ f : Plane →ᵃⁱ[ℝ] F, P = f '' unitPolygon n := by
  constructor
  · exact unitUniform_two_unitPolygon
  · rintro ⟨n, hn, f, rfl⟩
    exact embedding_unitUniform_image f (unitUniform_unitPolygon hn)

/-- A concrete unit triangle passes the actual exposed-edge definition. -/
theorem unitUniform_unitTriangle : UnitUniform 2 (unitPolygon 3) :=
  unitUniform_unitPolygon (by omega)

/-- A concrete unit square passes the actual exposed-edge definition. -/
theorem unitUniform_unitSquare : UnitUniform 2 (unitPolygon 4) :=
  unitUniform_unitPolygon (by omega)

end Uniform5.Composition
