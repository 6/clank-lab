import Uniform5.CompositionProductEdges
import Uniform5.CompositionPolygonNeighborPair
import Uniform5.CompositionFacetFigures

/-! Exhaustive neighbor charts and exact metrics of duoprism vertex figures. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A geometric F3 chart records actual edges and exhausts the actual
neighbors. Its four points and all six distances are part of the conclusion. -/
structure DuoprismNeighborChart (K G : Set E) (v : E) (n q : ℕ) where
  a : E
  b : E
  g : E
  d : E
  ab_ne : a ≠ b
  gg_ne : g ≠ d
  neighbors : ∀ z, Edge K v z ↔ z = a ∨ z = b ∨ z = g ∨ z = d
  polygon_neighbors : ∀ z, Edge G v z ↔ z = a ∨ z = b
  chord_ab : dist a b = CaseB.chord n
  chord_gg : dist g d = CaseB.chord q
  cross_ag : dist a g = Real.sqrt 2
  cross_ad : dist a d = Real.sqrt 2
  cross_bg : dist b g = Real.sqrt 2
  cross_bd : dist b d = Real.sqrt 2
  perpendicular : ⟪b - a, d - g⟫ = 0

/-- A chart gives the whole actual vertex figure, not just four selected
points lying in it. -/
theorem DuoprismNeighborChart.figure_eq [FiniteDimensional ℝ E]
    {K G : Set E} {v : E} {n q : ℕ} (D : DuoprismNeighborChart K G v n q)
    (hK : UnitUniform 4 K) (hv : v ∈ K.extremePoints ℝ) :
    vertexFigure K v (vertexCentroid (vertices K (uniform_finitePolytope hK.1))) =
      convexHull ℝ ({D.a, D.b, D.g, D.d} : Set E) := by
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hK.1
  rw [finitePolytope_unit_vertexFigure (uniform_finitePolytope hK.1) hv _ (intrinsicRadius K) hs hK.2]
  congr 1
  ext z
  exact D.neighbors z

/-- The four cross distances follow from the orthogonal product metric. -/
theorem product_neighbor_cross_dist {a b : ℕ} {x u : Space a} {y w : Space b}
    (hu : dist x u = 1) (hw : dist y w = 1) :
    dist (productPoint u y) (productPoint x w) = Real.sqrt 2 := by
  apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [productPoint_dist_sq, dist_comm u x, hu, hw, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The literal duoprism has exactly the four factor-edge neighbors and
F3's metric, with the first polygon slice distinguished. -/
theorem duoprism_left_neighbor_chart {n q : ℕ} (hn : 3 ≤ n) (hq : 3 ≤ q)
    (hfin : FinitePolytope (duoprismModel n q)) {x y : Plane}
    (hx : x ∈ (unitPolygon n).extremePoints ℝ) (hy : y ∈ (unitPolygon q).extremePoints ℝ) :
    Nonempty (DuoprismNeighborChart (duoprismModel n q)
      (product (unitPolygon n) {y}) (productPoint x y) n q) := by
  obtain ⟨a, b, hab, hea, heb, hpair, hva, hvb, hch⟩ := unitPolygon_neighbor_pair hn hx
  obtain ⟨c, d, hcd, hec, hed, hpair', hvc, hvd, hch'⟩ := unitPolygon_neighbor_pair hq hy
  let A := productPoint a y
  let B := productPoint b y
  let C := productPoint x c
  let D := productPoint x d
  refine ⟨{
    a := A, b := B, g := C, d := D,
    ab_ne := fun he => hab (congrArg productLeftProjection he),
    gg_ne := fun he => hcd (congrArg productRightProjection he),
    neighbors := ?_, polygon_neighbors := ?_, chord_ab := ?_, chord_gg := ?_,
    cross_ag := product_neighbor_cross_dist hva hvc,
    cross_ad := product_neighbor_cross_dist hva hvd,
    cross_bg := product_neighbor_cross_dist hvb hvc,
    cross_bd := product_neighbor_cross_dist hvb hvd,
    perpendicular := ?_ }⟩
  · intro z
    rw [duoprismModel, ← productPoint_projections z, product_edge_iff
      (unitPolygon_finitePolytope hn) (unitPolygon_finitePolytope hq) hfin, hpair, hpair']
    constructor
    · rintro (⟨he, _, ha | hb⟩ | ⟨he, _, hc | hd⟩)
      · left; rw [← he, ha]
      · right; left; rw [← he, hb]
      · right; right; left; rw [← he, hc]
      · right; right; right; rw [← he, hd]
    · rintro (he | he | he | he)
      · exact Or.inl ⟨(congrArg productRightProjection he).symm, hy,
          Or.inl (congrArg productLeftProjection he)⟩
      · exact Or.inl ⟨(congrArg productRightProjection he).symm, hy,
          Or.inr (congrArg productLeftProjection he)⟩
      · exact Or.inr ⟨(congrArg productLeftProjection he).symm, hx,
          Or.inl (congrArg productRightProjection he)⟩
      · exact Or.inr ⟨(congrArg productLeftProjection he).symm, hx,
          Or.inr (congrArg productRightProjection he)⟩
  · intro z
    rw [← product_left_slice_image]
    constructor
    · intro he
      obtain ⟨z', hz', rfl⟩ := he.2.1.1
      have hf := embedding_edge_reflect (productLeftSlice y) he
      exact (hpair z').mp hf |>.elim (fun h => Or.inl (congrArg (productLeftSlice y) h))
        (fun h => Or.inr (congrArg (productLeftSlice y) h))
    · rintro (rfl | rfl)
      · exact embedding_edge_image (productLeftSlice y) hea
      · exact embedding_edge_image (productLeftSlice y) heb
  · exact ((productLeftSlice y).dist_map a b).trans hch
  · exact ((productRightSlice x).dist_map c d).trans hch'
  · simp [A, B, C, D, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fintype.sum_sum_type, productPoint]

end Uniform5.Composition
