import Uniform5.CompositionWedgeActualGeometry
import Uniform5.CompositionTypeIFanMetrics
import Uniform5.CompositionTypeILateralPolygon

/-! Literal Type I W shapes from coherent actual fan charts. Reindexing
keeps the actual cyclic incidences, allowing either orientation. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

/-- Vertex and facet labels are linked by actual cycle incidence, including
reflection. No geometric or W conclusion is part of this data. -/
structure CyclicLabels (c : List Wedge.Parameter) (q : Fin D.length → ℕ) where
  vertex : Fin c.length ≃ Fin D.length
  facet : Fin c.length → Fin D.length
  incidence : ∀ i,
    (vertex i = facet i ∧ vertex (finRotate c.length i) = finRotate D.length (facet i)) ∨
    (vertex (finRotate c.length i) = facet i ∧ vertex i = finRotate D.length (facet i))
  parameter : ∀ i, c.get i = some (q (facet i) : ℝ)

variable {c : List Wedge.Parameter} {q : Fin D.length → ℕ}

theorem labels_length (L : CyclicLabels (D := D) c q) : c.length = D.length := by
  have hh := Fintype.card_congr L.vertex
  simpa using hh

noncomputable def wedgeShape (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    (L : CyclicLabels (D := D) c q) : Wedge.TypeIShape (some (n : ℝ)) c where
  length_ge := by rw [labels_length L]; exact D.length_ge
  length_le := by rw [labels_length L]; exact hlen
  a := T.a
  b := T.b
  x := fun i => T.lateral (L.vertex i)
  ab := T.chord_ab
  cross_a := fun i => (T.cross_dist hP hG hn hn4 hvG _ (hq _) (hmodel _)).1
  cross_b := fun i => (T.cross_dist hP hG hn hn4 hvG _ (hq _) (hmodel _)).2
  consecutive := by
    intro i
    rw [L.parameter i]
    change dist (T.lateral (L.vertex i)) (T.lateral (L.vertex (finRotate c.length i))) = _
    rcases L.incidence i with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha, hb]
      exact T.lateral_dist hP hG hn hn4 hvG _ (hq _) (hmodel _)
    · rw [ha, hb, dist_comm]
      exact T.lateral_dist hP hG hn hn4 hvG _ (hq _) (hmodel _)
  planar := by
    have hr : Set.range (fun i => T.lateral (L.vertex i)) = Set.range T.lateral :=
      L.vertex.surjective.range_comp T.lateral
    rw [hr]
    exact T.lateralHull_dimension hP hG hn hn4 hvG q hq hmodel hcell
  vertices := by
    have hr : Set.range (fun i => T.lateral (L.vertex i)) = Set.range T.lateral :=
      L.vertex.surjective.range_comp T.lateral
    rw [hr]
    exact T.lateralHull_extremePoints hP
  cyclic_edges := by
    intro i
    have hr : Set.range (fun i => T.lateral (L.vertex i)) = Set.range T.lateral :=
      L.vertex.surjective.range_comp T.lateral
    rw [hr]
    rcases L.incidence i with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha, hb]
      exact T.lateralHull_cycle_edge hP hG hvG _
    · rw [ha, hb]
      exact chart_edge_symm (T.lateralHull_cycle_edge hP hG hvG _)
  injective := T.lateral_injective.comp L.vertex.injective

/-- Every literal shape vertex is an actual parent figure vertex. -/
theorem wedgeShape_points (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    (L : CyclicLabels (D := D) c q) :
    ((T.wedgeShape hP hG hn hn4 hvG hlen hq hmodel hcell L).points : Set (Space 5)) ⊆
      (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
  let i₀ : Fin D.length := ⟨0, by have := D.length_ge; omega⟩
  intro x hx
  simp only [Wedge.TypeIShape.points, Finset.mem_coe, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with (rfl | rfl) | ⟨i, rfl⟩
  · exact (T.parent_figure_edge hP hG hvG i₀ (by simp) (by simp) T.ab_ne).1
  · exact (T.parent_figure_edge hP hG hvG i₀ (by simp) (by simp) T.ab_ne).2.1
  · exact (T.parent_figure_edge hP hG hvG (L.vertex i) (by simp) (by simp)
      (T.lateral_ne_a (L.vertex i))).1

/-- Whole literal fan facets are actual incident facet sections. -/
theorem wedgeShape_facets (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    (L : CyclicLabels (D := D) c q) :
    ∀ B ∈ (T.wedgeShape hP hG hn hn4 hvG hlen hq hmodel hcell L).facets,
    ∃ K, Facet P K ∧ v ∈ K ∧ B = K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := by
  rintro B ⟨i, rfl⟩
  refine ⟨D.facet (L.facet i), (D.facet_incidence _).1,
    (D.facet_incidence _).2.1 hvG.1, ?_⟩
  rw [T.facet_figure hP hG hvG]
  change convexHull ℝ {T.a,T.b,T.lateral (L.vertex i),
    T.lateral (L.vertex (finRotate c.length i))} = _
  rcases L.incidence i with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rw [ha, hb]
  · rw [ha, hb]
    congr 1
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto

end Uniform5.Composition.TypeIFanChart
