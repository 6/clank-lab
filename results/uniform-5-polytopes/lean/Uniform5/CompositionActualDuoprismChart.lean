import Uniform5.CompositionDuoprismChartTransport
import Uniform5.CompositionProductModelIncidence
import Uniform5.CompositionFigurePlacement

/-! F3 charts for an actual facet and its distinguished polygon. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every actual nonquadrilateral polygon in an actual duoprism facet
selects one factor; the complete F3 chart is transported with that polygon. -/
theorem unitUniform4_duoprism_neighbor_chart {K G : Set E} {v : E} {p q n : ℕ}
    (hK : UnitUniform 4 K) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel p q)) (hG : PolygonFace K G n)
    (hn : n ≠ 4) (hv : v ∈ G.extremePoints ℝ) :
    ∃ t : ℕ, 3 ≤ t ∧ ((n = p ∧ t = q) ∨ (n = q ∧ t = p)) ∧
      Nonempty (DuoprismNeighborChart K G v n t) := by
  have hKN := congruent_trans hmodel
    (congruent_affineIsometry_image (flattenProduct 2 2).toAffineIsometry _)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKN
  let j := f.comp (flattenProduct 2 2).toAffineIsometry
  have hj : j '' duoprismModel p q = K := by
    change (f ∘ flattenProduct 2 2) '' duoprismModel p q = K
    rw [Set.image_comp]
    exact hf
  have hM := (unitUniform_cross_congruent_iff hmodel 4).mp hK
  have hG' : PolygonFace (j '' duoprismModel p q) G n := hj ▸ hG
  let G₀ := j ⁻¹' G
  have hG₀ : PolygonFace (duoprismModel p q) G₀ n :=
    embedding_polygonFace_preimage j (uniform_finitePolytope hM.1) hG'
  have hGim : j '' G₀ = G := embedding_face_image_preimage j hG'.1
  have hvK := hG.1.2.extremePoints_subset_extremePoints hv
  rw [← hj, ← embedding_extremePoints] at hvK
  obtain ⟨v₀, hv₀, rfl⟩ := hvK
  have hvm : v₀ ∈ G₀ := hv.1
  rw [duoprismModel, product_extremePoints] at hv₀
  obtain ⟨x, hx, y, hy, he⟩ := hv₀
  subst v₀
  rcases duoprism_nonquadrilateral_polygon_slices hp hq hG₀ hn with
    ⟨hnp, y₀, hy₀, hs⟩ | ⟨hnq, x₀, hx₀, hs⟩
  · have hyEq : y = y₀ := by
      rw [hs, productPoint_mem_product] at hvm
      exact hvm.2
    subst y₀
    obtain ⟨D⟩ := duoprism_left_neighbor_chart hp hq (uniform_finitePolytope hM.1) hx hy
    have hd := D.map j
    rw [← hs, hj, hGim, ← hnp] at hd
    exact ⟨q, hq, Or.inl ⟨hnp, rfl⟩, ⟨hd⟩⟩
  · have hxEq : x = x₀ := by
      rw [hs, productPoint_mem_product] at hvm
      exact hvm.1
    subst x₀
    obtain ⟨D⟩ := duoprism_right_neighbor_chart hp hq (uniform_finitePolytope hM.1) hx hy
    have hd := D.map j
    rw [← hs, hj, hGim, ← hnq] at hd
    exact ⟨p, hp, Or.inr ⟨hnq, rfl⟩, ⟨hd⟩⟩

/-- When the observed polygon is the named first factor, the other chord
uses exactly the named second parameter, even when the factors coincide. -/
theorem unitUniform4_duoprism_neighbor_chart_parameters {K G : Set E} {v : E} {n q : ℕ}
    (hK : UnitUniform 4 K) (hn : 3 ≤ n) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel n q)) (hG : PolygonFace K G n)
    (hn4 : n ≠ 4) (hv : v ∈ G.extremePoints ℝ) :
    Nonempty (DuoprismNeighborChart K G v n q) := by
  obtain ⟨t, _, ht, D⟩ := unitUniform4_duoprism_neighbor_chart hK hn hq hmodel hG hn4 hv
  have he : t = q := ht.elim (fun h => h.2) (fun h => h.2.trans h.1)
  rwa [he] at D

/-- In a uniform five-polytope the actual facet section is precisely the
four-neighbor hull with the F3 metric and the selected polygon edge. -/
theorem unitUniform5_duoprism_facet_figure {P K G : Set E} {v : E} {p q n : ℕ}
    (hP : UnitUniform 5 P) (hK : Facet P K) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel p q)) (hG : PolygonFace K G n)
    (hn : n ≠ 4) (hv : v ∈ G.extremePoints ℝ) :
    ∃ t : ℕ, 3 ≤ t ∧ ∃ D : DuoprismNeighborChart K G v n t,
      K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
        convexHull ℝ ({D.a, D.b, D.g, D.d} : Set E) := by
  have hKU := unitUniform_facet hP hK
  obtain ⟨t, ht, _, D⟩ := unitUniform4_duoprism_neighbor_chart hKU hp hq hmodel hG hn hv
  obtain ⟨D⟩ := D
  refine ⟨t, ht, D, ?_⟩
  rw [uniform_vertexFigure_face_inter hP.1 hK.1 hK.2.1 (hG.1.2.1 hv.1)]
  exact D.figure_eq hKU (hG.1.2.extremePoints_subset_extremePoints hv)

omit [FiniteDimensional ℝ E] in
/-- The four actual neighbors are affinely independent, so the displayed
hull is a tetrahedron rather than a collapsed four-point hull. -/
theorem duoprism_chart_affineIndependent {K G : Set E} {v : E} {n q : ℕ}
    (D : DuoprismNeighborChart K G v n q)
    (hd : affineDimension (convexHull ℝ ({D.a, D.b, D.g, D.d} : Set E)) = 3) :
    AffineIndependent ℝ ![D.a, D.b, D.g, D.d] := by
  apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ (show Fintype.card (Fin 4) = 3 + 1 by decide)).mpr
  have hr : Set.range ![D.a, D.b, D.g, D.d] = ({D.a, D.b, D.g, D.d} : Set E) := by
    ext z
    simp [Set.mem_range, Fin.exists_fin_succ, or_comm, or_left_comm]
  rw [hr]
  unfold affineDimension Uniform5.affineDimension at hd
  rw [affineSpan_convexHull (𝕜 := ℝ), direction_affineSpan] at hd
  exact hd

/-- Complete F3 duoprism chart for an actual facet of the five-polytope,
including its genuine tetrahedral dimension. -/
theorem unitUniform5_duoprism_facet_tetrahedron {P K G : Set (Space 5)} {v : Space 5}
    {p q n : ℕ} (hP : UnitUniform 5 P) (hK : Facet P K) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel p q)) (hG : PolygonFace K G n)
    (hn : n ≠ 4) (hv : v ∈ G.extremePoints ℝ) :
    ∃ t : ℕ, 3 ≤ t ∧ ∃ D : DuoprismNeighborChart K G v n t,
      K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
        convexHull ℝ ({D.a, D.b, D.g, D.d} : Set (Space 5)) ∧
      AffineIndependent ℝ ![D.a, D.b, D.g, D.d] := by
  obtain ⟨t, ht, D, he⟩ := unitUniform5_duoprism_facet_figure hP hK hp hq hmodel hG hn hv
  refine ⟨t, ht, D, he, duoprism_chart_affineIndependent D ?_⟩
  have hd := (unitUniform5_facet_figure_placement hP hK
    (hG.1.2.extremePoints_subset_extremePoints hv)).2.2.2.1
  rwa [he] at hd

/-- Parameter-preserving form used when the actual facet is already named
as the product of the selected n-gon and a q-gon. -/
theorem unitUniform5_duoprism_facet_tetrahedron_parameters
    {P K G : Set (Space 5)} {v : Space 5} {n q : ℕ}
    (hP : UnitUniform 5 P) (hK : Facet P K) (hn : 3 ≤ n) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel n q)) (hG : PolygonFace K G n)
    (hn4 : n ≠ 4) (hv : v ∈ G.extremePoints ℝ) :
    ∃ D : DuoprismNeighborChart K G v n q,
      K ∩ vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
        convexHull ℝ ({D.a, D.b, D.g, D.d} : Set (Space 5)) ∧
      AffineIndependent ℝ ![D.a, D.b, D.g, D.d] := by
  have hKU := unitUniform_facet hP hK
  obtain ⟨D⟩ := unitUniform4_duoprism_neighbor_chart_parameters hKU hn hq hmodel hG hn4 hv
  have hvK := hG.1.2.extremePoints_subset_extremePoints hv
  have he : K ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) =
      convexHull ℝ ({D.a, D.b, D.g, D.d} : Set (Space 5)) := by
    rw [uniform_vertexFigure_face_inter hP.1 hK.1 hK.2.1 (hG.1.2.1 hv.1)]
    exact D.figure_eq hKU hvK
  refine ⟨D, he, duoprism_chart_affineIndependent D ?_⟩
  have hd := (unitUniform5_facet_figure_placement hP hK hvK).2.2.2.1
  rwa [he] at hd

end Uniform5.Composition
