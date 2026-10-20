import Uniform5.CompositionActualAntiprismChart
import Uniform5.CompositionIntervalNeighbor
import Uniform5.CompositionDuoprismChart

/-! The complete square-pyramid F3 chart of an antiprism prism. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The base is an actual antiprism cell chart; the fifth neighbor is the
apex, at distance square-root two from every base vertex. -/
structure AntiprismPrismNeighborChart (K C G : Set E) (v : E) (n : ℕ) where
  base : AntiprismNeighborChart C G v n
  apex : E
  neighbors : ∀ z, Edge K v z ↔
    z = base.a ∨ z = base.b ∨ z = base.x ∨ z = base.y ∨ z = apex
  apex_a : dist base.a apex = Real.sqrt 2
  apex_b : dist base.b apex = Real.sqrt 2
  apex_x : dist base.x apex = Real.sqrt 2
  apex_y : dist base.y apex = Real.sqrt 2

/-- The five-point hull is the whole intrinsic figure. -/
theorem AntiprismPrismNeighborChart.figure_eq [FiniteDimensional ℝ E]
    {K C G : Set E} {v : E} {n : ℕ} (D : AntiprismPrismNeighborChart K C G v n)
    (hK : UnitUniform 4 K) (hv : v ∈ K.extremePoints ℝ) :
    vertexFigure K v (vertexCentroid (vertices K (uniform_finitePolytope hK.1))) =
      convexHull ℝ ({D.base.a, D.base.b, D.base.x, D.base.y, D.apex} : Set E) := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hK.1
  rw [finitePolytope_unit_vertexFigure (uniform_finitePolytope hK.1) hv _ (intrinsicRadius K) hs hK.2]
  congr 1
  ext z
  exact D.neighbors z

/-- The product edge theorem proves that the four base neighbors and the
interval neighbor exhaust the actual model edge star. -/
theorem antiprismPrism_product_chart {n : ℕ} {A G : Set (Space 3)} {v : Space 3}
    (D : AntiprismNeighborChart A G v n) (hA : UnitUniform 3 A)
    (hfin : FinitePolytope (product A unitInterval)) (hv : v ∈ A.extremePoints ℝ)
    {s : Space 1} (hs : s ∈ unitInterval.extremePoints ℝ) :
    Nonempty (AntiprismPrismNeighborChart (product A unitInterval)
      (product A {s}) (product G {s}) (productPoint v s) n) := by
  obtain ⟨t, ht, hst, hpair⟩ := unitInterval_neighbor hs
  suffices Nonempty (AntiprismPrismNeighborChart (product A unitInterval)
      (productLeftSlice s '' A) (productLeftSlice s '' G) (productPoint v s) n) by
    simpa only [product_left_slice_image] using this
  let B := D.map (productLeftSlice s)
  have hva : dist v D.a = 1 := hA.2 _ _ ((D.neighbors _).mpr (Or.inl rfl))
  have hvb : dist v D.b = 1 := hA.2 _ _ ((D.neighbors _).mpr (Or.inr (Or.inl rfl)))
  have hvx : dist v D.x = 1 := hA.2 _ _ ((D.neighbors _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hvy : dist v D.y = 1 := hA.2 _ _ ((D.neighbors _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨{
    base := B, apex := productPoint v t, neighbors := ?_,
    apex_a := product_neighbor_cross_dist hva hst,
    apex_b := product_neighbor_cross_dist hvb hst,
    apex_x := product_neighbor_cross_dist hvx hst,
    apex_y := product_neighbor_cross_dist hvy hst }⟩
  intro z
  rw [← productPoint_projections z, product_edge_iff
    (uniform_finitePolytope hA.1) unitInterval_finitePolytope hfin, D.neighbors, hpair]
  constructor
  · rintro (⟨he, _, ha | hb | hx | hy⟩ | ⟨he, _, ht⟩)
    · left; rw [← he, ha]; rfl
    · right; left; rw [← he, hb]; rfl
    · right; right; left; rw [← he, hx]; rfl
    · right; right; right; left; rw [← he, hy]; rfl
    · right; right; right; right; rw [← he, ht]
  · rintro (he | he | he | he | he)
    · exact Or.inl ⟨(congrArg productRightProjection he).symm, hs,
        Or.inl (congrArg productLeftProjection he)⟩
    · exact Or.inl ⟨(congrArg productRightProjection he).symm, hs,
        Or.inr (Or.inl (congrArg productLeftProjection he))⟩
    · exact Or.inl ⟨(congrArg productRightProjection he).symm, hs,
        Or.inr (Or.inr (Or.inl (congrArg productLeftProjection he)))⟩
    · exact Or.inl ⟨(congrArg productRightProjection he).symm, hs,
        Or.inr (Or.inr (Or.inr (congrArg productLeftProjection he)))⟩
    · exact Or.inr ⟨(congrArg productLeftProjection he).symm, hv,
        congrArg productRightProjection he⟩

end Uniform5.Composition
