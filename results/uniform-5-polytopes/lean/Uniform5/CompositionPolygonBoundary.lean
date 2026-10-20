import Uniform5.CompositionPolygonIncidence
import Uniform5.CompositionCycleReindex

/-! A finite cyclic boundary means the actual vertices of a planar convex
hull, each visited once, with every consecutive pair an actual exposed edge.
The dimension condition rules out a Hamiltonian cycle in a higher-dimensional
polytope. The last point is adjacent to the first through `finRotate`. -/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Geometric correctness of a finite cyclic polygon boundary. -/
structure CyclicPolygonBoundary (P : Set E) {n : ℕ} (point : Fin n → E) : Prop where
  length_ge : 3 ≤ n
  hull : P = convexHull ℝ (Set.range point)
  dimension : affineDimension P = 2
  injective : Function.Injective point
  vertices : Set.range point = P.extremePoints ℝ
  consecutive : ∀ i, Edge P (point i) (point (finRotate n i))

namespace CyclicPolygonBoundary
variable {P : Set E} {n : ℕ} {point : Fin n → E}

theorem finitePolytope (h : CyclicPolygonBoundary P point) : FinitePolytope P := by
  classical
  refine ⟨Finset.univ.image point, ?_, ?_⟩
  · exact ⟨point ⟨0, by have := h.length_ge; omega⟩, Finset.mem_image.mpr
      ⟨⟨0, by have := h.length_ge; omega⟩, Finset.mem_univ _, rfl⟩⟩
  · simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using h.hull

theorem nonempty (h : CyclicPolygonBoundary P point) : P.Nonempty := by
  have hi : point ⟨0, by have := h.length_ge; omega⟩ ∈ P.extremePoints ℝ := by
    rw [← h.vertices]
    exact Set.mem_range_self _
  exact ⟨_, hi.1⟩

/-- Repeated points cannot be certified as a cyclic boundary. -/
theorem point_ne (h : CyclicPolygonBoundary P point) {i j : Fin n} (hij : i ≠ j) :
    point i ≠ point j := fun he => hij (h.injective he)

/-- Reversing the orientation preserves the exact polygon and its sides. -/
theorem reverse [NeZero n] (h : CyclicPolygonBoundary P point) :
    CyclicPolygonBoundary P (fun i => point (-i)) := by
  have hr : Set.range (fun i : Fin n => point (-i)) = Set.range point := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨-i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨-i, by simp⟩
  refine ⟨h.length_ge, hr.symm ▸ h.hull, h.dimension,
    h.injective.comp (Equiv.neg (Fin n)).injective, hr.trans h.vertices, ?_⟩
  intro i
  have he := h.consecutive (-(finRotate n i))
  have hi : finRotate n (-(finRotate n i)) = -i := by
    simp only [finRotate_eq_add_one]
    abel
  rw [hi] at he
  exact ⟨he.2.1, he.1, Ne.symm he.2.2.1,
    by simpa only [segment_symm] using he.2.2.2⟩

end CyclicPolygonBoundary

/-- Sanity family: every explicit regular polygon, with its usual circular
enumeration, has an actual cyclic boundary. -/
theorem polygon_cyclicBoundary (n : ℕ) (r : ℝ) (hn : 3 ≤ n) (hr : 0 < r) :
    CyclicPolygonBoundary (polygon n r) (polygonPoint n r) := by
  letI : NeZero n := ⟨by omega⟩
  refine ⟨hn, rfl, affineDimension_polygon n r hn hr,
    polygonPoint_injective n r hn hr, (polygon_extremePoints n r hr.le).symm, ?_⟩
  intro i
  simpa only [finRotate_eq_add_one] using polygon_consecutive_edge r hn hr i

theorem triangle_cyclicBoundary :
    CyclicPolygonBoundary (polygon 3 1) (polygonPoint 3 1) :=
  polygon_cyclicBoundary 3 1 (by decide) (by norm_num)

theorem square_cyclicBoundary :
    CyclicPolygonBoundary (polygon 4 1) (polygonPoint 4 1) :=
  polygon_cyclicBoundary 4 1 (by decide) (by norm_num)

theorem no_two_point_cyclicBoundary (P : Set E) (point : Fin 2 → E) :
    ¬ CyclicPolygonBoundary P point := by
  intro h
  have := h.length_ge
  omega

end Uniform5.Composition
