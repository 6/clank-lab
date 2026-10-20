import Uniform5.CompositionAntiprismLayers

/-! Exhaustive actual four-neighbor list at a concrete antiprism vertex. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- The two specified polygon sides at index one exhaust its edge star. -/
theorem unitPolygon_one_neighbors {n : ℕ} (hn : 3 ≤ n) :
    ∀ z, Edge (unitPolygon n) (polygonPoint n (unitPolygonRadius n) ⟨1, by omega⟩) z ↔
      z = polygonPoint n (unitPolygonRadius n) ⟨0, by omega⟩ ∨
      z = polygonPoint n (unitPolygonRadius n) ⟨2, by omega⟩ := by
  letI : NeZero n := ⟨by omega⟩
  have hr := unitPolygonRadius_pos hn
  have h01 := polygon_first_edge n (unitPolygonRadius n) hn hr
  have h10 : Edge (unitPolygon n) (polygonPoint n (unitPolygonRadius n) ⟨1, by omega⟩)
      (polygonPoint n (unitPolygonRadius n) ⟨0, by omega⟩) :=
    ⟨h01.2.1, h01.1, h01.2.2.1.symm, by rw [segment_symm]; exact h01.2.2.2⟩
  have h12 := polygon_consecutive_edge (unitPolygonRadius n) hn hr (⟨1, by omega⟩ : Fin n)
  have hi : (⟨1, by omega⟩ : Fin n) + 1 = ⟨2, by omega⟩ := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < n by omega)]
  rw [hi] at h12
  have h02 : polygonPoint n (unitPolygonRadius n) ⟨0, by omega⟩ ≠
      polygonPoint n (unitPolygonRadius n) ⟨2, by omega⟩ := by
    intro he
    have hh := congrArg Fin.val (polygonPoint_injective n _ hn hr he)
    norm_num at hh
  intro z
  constructor
  · exact edge_of_two_spanning_edges h10 h12 h02 (polygon_second_neighbors_span n _ hn hr)
  · rintro (rfl | rfl) <;> assumption

/-- The complete actual neighbor list is two upper and two lower vertices,
with no graph or adjacency oracle assumed. -/
theorem antiprism_one_neighbors {n : ℕ} (hn : 3 ≤ n)
    (hA : UnitUniform 3 (antiprismModel n)) :
    ∀ z, Edge (antiprismModel n) (antiprismPoint n false ⟨1, by omega⟩) z ↔
      z = antiprismPoint n false ⟨0, by omega⟩ ∨
      z = antiprismPoint n false ⟨2, by omega⟩ ∨
      z = antiprismPoint n true ⟨0, by omega⟩ ∨
      z = antiprismPoint n true ⟨1, by omega⟩ := by
  let f := antiprismLayerSlice n false
  have hf := antiprism_layer_face hn false
  rw [antiprismLayer_eq_image] at hf
  have hmem (i : Fin n) : antiprismPoint n false i ∈ f '' unitPolygon n := by
    refine ⟨polygonPoint n (unitPolygonRadius n) i, ?_, antiprismLayerSlice_point n false i⟩
    exact subset_convexHull ℝ _ ⟨i, rfl⟩
  have htop (i : Fin n) :
      Edge (antiprismModel n) (antiprismPoint n false ⟨1, by omega⟩) (antiprismPoint n false i) ↔
      antiprismPoint n false i = antiprismPoint n false ⟨0, by omega⟩ ∨
      antiprismPoint n false i = antiprismPoint n false ⟨2, by omega⟩ := by
    rw [edge_face_iff (uniform_finitePolytope hA.1) hf (hmem _) (hmem i)]
    have he : Edge (f '' unitPolygon n) (antiprismPoint n false ⟨1, by omega⟩)
        (antiprismPoint n false i) ↔
        Edge (unitPolygon n) (polygonPoint n (unitPolygonRadius n) ⟨1, by omega⟩)
          (polygonPoint n (unitPolygonRadius n) i) := by
      rw [← antiprismLayerSlice_point n false ⟨1, by omega⟩, ← antiprismLayerSlice_point n false i]
      exact ⟨embedding_edge_reflect f, embedding_edge_image f⟩
    rw [he, unitPolygon_one_neighbors hn]
    simp only [← antiprismLayerSlice_point n false, (antiprismLayerSlice n false).injective.eq_iff]
  intro z
  constructor
  · intro he
    have hz := he.2.1
    rw [antiprism_extremePoints] at hz
    obtain ⟨⟨b, i⟩, rfl⟩ := hz
    cases b
    · exact (htop i).mp he |>.elim Or.inl (fun h => Or.inr (Or.inl h))
    · have hi := (antiprism_one_cross_edge_iff hn hA i).mp he
      rcases hi with hi | hi
      · exact Or.inr (Or.inr (Or.inl (congrArg (antiprismPoint n true) (Fin.ext hi))))
      · exact Or.inr (Or.inr (Or.inr (congrArg (antiprismPoint n true) (Fin.ext hi))))
  · rintro (rfl | rfl | rfl | rfl)
    · exact (htop _).mpr (Or.inl rfl)
    · exact (htop _).mpr (Or.inr rfl)
    · exact (antiprism_one_cross_edge_iff hn hA _).mpr (Or.inl rfl)
    · exact (antiprism_one_cross_edge_iff hn hA _).mpr (Or.inr rfl)

end Uniform5.Composition
