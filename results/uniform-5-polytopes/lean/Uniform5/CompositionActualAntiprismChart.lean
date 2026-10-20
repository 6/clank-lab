import Uniform5.CompositionAntiprismChartTransport
import Uniform5.CompositionProductModelIncidence

/-! Actual antiprism charts respecting any selected large polygon face. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- A vertex on the upper layer cannot lie on the lower layer. -/
theorem antiprism_top_not_mem_bottom {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    antiprismPoint n false i ∉ antiprismLayer n true := by
  rw [antiprismLayer_eq_image]
  rintro ⟨x, hx, he⟩
  have hh := congrArg (fun z : Space 3 => z 2) he
  change -(antiprismHeight n / 2) = antiprismHeight n / 2 at hh
  linarith [antiprismHeight_pos hn]

/-- The actual model chart at an arbitrary vertex carries the distinguished
large polygon, using vertex transitivity and the proved layer classification. -/
theorem antiprism_neighbor_chart {n k : ℕ} (hn : 3 ≤ n) (hk : 5 ≤ k)
    (hA : UnitUniform 3 (antiprismModel n)) {G : Set (Space 3)} {v : Space 3}
    (hG : PolygonFace (antiprismModel n) G k) (hv : v ∈ G.extremePoints ℝ) :
    k = n ∧ Nonempty (AntiprismNeighborChart (antiprismModel n) G v n) := by
  let u := antiprismPoint n false ⟨1, by omega⟩
  have hu : u ∈ (antiprismModel n).extremePoints ℝ := by
    rw [antiprism_extremePoints]
    exact ⟨(false, ⟨1, by omega⟩), rfl⟩
  obtain ⟨g, hg, hgv⟩ := uniform_vertexTransitive hA.1 u hu v
    (hG.1.2.extremePoints_subset_extremePoints hv)
  change g.toAffineIsometry '' antiprismModel n = antiprismModel n at hg
  have hGi : PolygonFace (g.toAffineIsometry '' antiprismModel n) G k := by rw [hg]; exact hG
  have hG' := embedding_polygonFace_preimage g.toAffineIsometry
    (uniform_finitePolytope hA.1) hGi
  have him := embedding_face_image_preimage g.toAffineIsometry hGi.1
  have hum : u ∈ g.toAffineIsometry ⁻¹' G := by change g u ∈ G; rw [hgv]; exact hv.1
  have hlayer : g.toAffineIsometry ⁻¹' G = antiprismLayer n false := by
    rcases antiprism_polygon_is_layer hn hk hG' with h | h
    · exact h
    · rw [h] at hum
      exact False.elim (antiprism_top_not_mem_bottom hn _ hum)
  have hk' := polygonFace_extremePoints_ncard hG'
  rw [hlayer, polygonFace_extremePoints_ncard (antiprism_layer_polygonFace hn false)] at hk'
  refine ⟨hk'.symm, ?_⟩
  obtain ⟨D⟩ := antiprism_one_chart hn hA
  have hd := D.map g.toAffineIsometry
  have him' : g.toAffineIsometry '' antiprismLayer n false = G := by
    rw [← hlayer]; exact him
  rw [hg, him', show g.toAffineIsometry (antiprismPoint n false ⟨1, by omega⟩) = v from hgv] at hd
  exact ⟨hd⟩

end Uniform5.Composition
