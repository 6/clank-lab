import Uniform5.CompositionActualDuoprismChart

/-! The F3 metric is independent of either choice of ordering in a
polygon-neighbor pair or the complementary lateral-neighbor pair. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace DuoprismNeighborChart
variable {K G : Set E} {v : E} {n q : ℕ} (T : DuoprismNeighborChart K G v n q)

theorem outside_neighbor_pair {z : E} (he : Edge K v z) (hz : z ∉ G) :
    z = T.g ∨ z = T.d := by
  have ha : T.a ∈ G := ((T.polygon_neighbors T.a).mpr (Or.inl rfl)).2.1.1
  have hb : T.b ∈ G := ((T.polygon_neighbors T.b).mpr (Or.inr rfl)).2.1.1
  rcases (T.neighbors z).mp he with rfl | rfl | hz | hz
  · exact (hz ha).elim
  · exact (hz hb).elim
  · exact Or.inl hz
  · exact Or.inr hz

include T in
theorem polygon_lateral_dist {a z : E} (ha : Edge G v a) (hz : Edge K v z)
    (hout : z ∉ G) : dist a z = Real.sqrt 2 := by
  rcases (T.polygon_neighbors a).mp ha with rfl | rfl <;>
    rcases T.outside_neighbor_pair hz hout with rfl | rfl
  · exact T.cross_ag
  · exact T.cross_ad
  · exact T.cross_bg
  · exact T.cross_bd

include T in
theorem lateral_dist {z w : E} (hz : Edge K v z) (hw : Edge K v w)
    (hzout : z ∉ G) (hwout : w ∉ G) (hne : z ≠ w) : dist z w = CaseB.chord q := by
  rcases T.outside_neighbor_pair hz hzout with rfl | rfl <;>
    rcases T.outside_neighbor_pair hw hwout with rfl | rfl
  · exact (hne rfl).elim
  · exact T.chord_gg
  · simpa only [dist_comm] using T.chord_gg
  · exact (hne rfl).elim

end DuoprismNeighborChart
end Uniform5.Composition
