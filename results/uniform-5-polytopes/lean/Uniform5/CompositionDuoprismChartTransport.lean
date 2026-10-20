import Uniform5.CompositionDuoprismChart
import Uniform5.CompositionCaseBProductSlices

/-! One ambient embedding transports the complete actual F3 chart. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The chart's edge incidences, exhaustive neighbor list and metric use
one and the same isometric embedding. -/
noncomputable def DuoprismNeighborChart.map {K G : Set E} {v : E} {n q : ℕ}
    (D : DuoprismNeighborChart K G v n q) (f : E →ᵃⁱ[ℝ] F) :
    DuoprismNeighborChart (f '' K) (f '' G) (f v) n q where
  a := f D.a
  b := f D.b
  g := f D.g
  d := f D.d
  ab_ne := fun h => D.ab_ne (f.injective h)
  gg_ne := fun h => D.gg_ne (f.injective h)
  neighbors := by
    intro z
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := he.2.1.1
      have hh := (D.neighbors x).mp (embedding_edge_reflect f he)
      rcases hh with h | h | h | h
      · exact Or.inl (congrArg f h)
      · exact Or.inr (Or.inl (congrArg f h))
      · exact Or.inr (Or.inr (Or.inl (congrArg f h)))
      · exact Or.inr (Or.inr (Or.inr (congrArg f h)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact embedding_edge_image f ((D.neighbors D.a).mpr (Or.inl rfl))
      · exact embedding_edge_image f ((D.neighbors D.b).mpr (Or.inr (Or.inl rfl)))
      · exact embedding_edge_image f ((D.neighbors D.g).mpr (Or.inr (Or.inr (Or.inl rfl))))
      · exact embedding_edge_image f ((D.neighbors D.d).mpr (Or.inr (Or.inr (Or.inr rfl))))
  polygon_neighbors := by
    intro z
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := he.2.1.1
      have hh := (D.polygon_neighbors x).mp (embedding_edge_reflect f he)
      exact hh.elim (fun h => Or.inl (congrArg f h)) (fun h => Or.inr (congrArg f h))
    · rintro (rfl | rfl)
      · exact embedding_edge_image f ((D.polygon_neighbors D.a).mpr (Or.inl rfl))
      · exact embedding_edge_image f ((D.polygon_neighbors D.b).mpr (Or.inr rfl))
  chord_ab := (f.dist_map _ _).trans D.chord_ab
  chord_gg := (f.dist_map _ _).trans D.chord_gg
  cross_ag := (f.dist_map _ _).trans D.cross_ag
  cross_ad := (f.dist_map _ _).trans D.cross_ad
  cross_bg := (f.dist_map _ _).trans D.cross_bg
  cross_bd := (f.dist_map _ _).trans D.cross_bd
  perpendicular := by
    have h₁ : f D.b - f D.a = f.linearIsometry (D.b - D.a) := (f.map_vsub D.b D.a).symm
    have h₂ : f D.d - f D.g = f.linearIsometry (D.d - D.g) := (f.map_vsub D.d D.g).symm
    rw [h₁, h₂, f.linearIsometry.inner_map_map]
    exact D.perpendicular

/-- Swap the two literal planar coordinate factors. -/
noncomputable def planarProductSwap :
    EuclideanSpace ℝ (Fin 2 ⊕ Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2 ⊕ Fin 2) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sumComm (Fin 2) (Fin 2))).toAffineIsometryEquiv

@[simp] theorem planarProductSwap_point (x y : Plane) :
    planarProductSwap (productPoint x y) = productPoint y x := by
  ext i
  cases i <;> rfl

@[simp] theorem planarProductSwap_image (P Q : Set Plane) :
    planarProductSwap '' product P Q = product Q P := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, x, hx, planarProductSwap_point x y⟩
  · rintro ⟨y, hy, x, hx, rfl⟩
    exact ⟨productPoint x y, ⟨x, hx, y, hy, rfl⟩, planarProductSwap_point x y⟩

/-- The other polygon slice is covered by the same exact chart after the
literal coordinate swap. -/
theorem duoprism_right_neighbor_chart {n q : ℕ} (hn : 3 ≤ n) (hq : 3 ≤ q)
    (hfin : FinitePolytope (duoprismModel n q)) {x y : Plane}
    (hx : x ∈ (unitPolygon n).extremePoints ℝ) (hy : y ∈ (unitPolygon q).extremePoints ℝ) :
    Nonempty (DuoprismNeighborChart (duoprismModel n q)
      (product {x} (unitPolygon q)) (productPoint x y) q n) := by
  have hf : FinitePolytope (duoprismModel q n) := by
    simpa only [duoprismModel, AffineIsometryEquiv.coe_toAffineIsometry, planarProductSwap_image] using
      (finitePolytope_affineIsometry_image_iff planarProductSwap.toAffineIsometry _).mpr hfin
  obtain ⟨D⟩ := duoprism_left_neighbor_chart hq hn hf hy hx
  have hd := D.map planarProductSwap.toAffineIsometry
  simpa only [duoprismModel, AffineIsometryEquiv.coe_toAffineIsometry,
    planarProductSwap_image, planarProductSwap_point] using (show Nonempty _ from ⟨hd⟩)

end Uniform5.Composition
