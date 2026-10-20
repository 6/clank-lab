import Uniform5.CompositionCellTypes
import Uniform5.CompositionLibraryNames

/-! The named LIB input: coordinate, radius and actual word-angle balls.
No catalogue completeness or certified incidence-table linkage is included. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry

/-- An exact rational midpoint and radius, as in the numerical export. -/
structure RationalBall where
  midpoint : ℚ
  radius : ℚ

namespace RationalBall
noncomputable def Contains (B : RationalBall) (x : ℝ) : Prop :=
  0 ≤ B.radius ∧ |x - (B.midpoint : ℝ)| ≤ (B.radius : ℝ)

noncomputable def lower (B : RationalBall) : ℝ := (B.midpoint : ℝ) - (B.radius : ℝ)
noncomputable def upper (B : RationalBall) : ℝ := (B.midpoint : ℝ) + (B.radius : ℝ)

theorem bounds {B : RationalBall} {x : ℝ} (h : B.Contains x) :
    B.lower ≤ x ∧ x ≤ B.upper := by
  obtain ⟨hl, hu⟩ := abs_le.mp h.2
  unfold lower upper
  constructor <;> linarith

theorem singleton_contains (q : ℚ) :
    (⟨q, 0⟩ : RationalBall).Contains (q : ℝ) := by
  simp [Contains]
end RationalBall

/-- Raw data only. Validity of the selected models and every enclosure
belongs to the named LIB hypothesis, not to an additional data premise. -/
structure LibraryNumericalData where
  model : CanonicalFacetName → Set (Space 4)
  vertexSet : CanonicalFacetName → Finset (Space 4)
  radiusBall : CanonicalFacetName → RationalBall
  coordinateBall : CanonicalFacetName → Space 4 → Fin 4 → RationalBall
  angleBall : CanonicalFacetName → ℕ → CellType → CellType → RationalBall

/-- The geometric angle between the two actual cell-centroid rays at an
actual polygon. No uniformity or word formula is built into this definition. -/
noncomputable def geometricPolygonAngle {K G A B : Set (Space 4)} {k : ℕ}
    (hK : FinitePolytope K) (hG : PolygonFace K G k)
    (hA : Facet K A) (hB : Facet K B) : ℝ :=
  let f := vertexCentroid (vertices G (finitePolytope_face hK hG.1 (polygonFace_nonempty hG)))
  let a := vertexCentroid (vertices A (finitePolytope_facet hK hA))
  let b := vertexCentroid (vertices B (finitePolytope_facet hK hB))
  angle (a - f) (b - f)

/-- Computation LIB: for each of the 181 canonical types, its model is
constructed with enclosed vertex coordinates, and its circumradius and
all polygon-orbit dihedral angles are enclosed. Angles are actual geometric
angles; the radius-word formula is derived below. Uniformity itself and
arbitrary-facet coverage are not asserted by this input. -/
structure LIB (D : LibraryNumericalData) : Prop where
  model_named : ∀ n, FacetLibraryModel n.val (D.model n)
  model_hull : ∀ n, D.model n = convexHull ℝ (D.vertexSet n : Set (Space 4))
  vertices_exact : ∀ n, (D.vertexSet n : Set (Space 4)) = extremePoints ℝ (D.model n)
  radius_enclosed : ∀ n, ∃ r, HasIntrinsicRadius (D.model n) r ∧
    (D.radiusBall n).Contains r
  coordinates_enclosed : ∀ n, ∀ v ∈ D.vertexSet n, ∀ j,
    (D.coordinateBall n v j).Contains (v j)
  angles_enclosed : ∀ n (hK : FinitePolytope (D.model n)) (k : ℕ)
    (G A B : Set (Space 4)) (hG : PolygonFace (D.model n) G k)
    (hA : Facet (D.model n) A) (hB : Facet (D.model n) B),
    G ⊆ A → G ⊆ B → A ≠ B → ∀ a b,
    Congruent A (cellTypeModel a) → Congruent B (cellTypeModel b) →
    (D.angleBall n k a b).Contains (geometricPolygonAngle hK hG hA hB)

namespace LIB
variable {D : LibraryNumericalData} (h : LIB D)
include h

theorem radius_of_congruent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {P : Set E} {n : CanonicalFacetName}
    (hP : Congruent P (D.model n)) : (D.radiusBall n).Contains (intrinsicRadius P) := by
  rw [intrinsicRadius_cross_congruent hP]
  obtain ⟨r, hr, hb⟩ := h.radius_enclosed n
  rwa [hr.eq_intrinsicRadius] at hb

theorem word_angle_enclosed {n : CanonicalFacetName} (hK : UnitUniform 4 (D.model n))
    {k : ℕ} {a b : CellType}
    (hw : ModelPolygonWord (D.model n) k (cellTypeModel a) (cellTypeModel b)) :
    (D.angleBall n k a b).Contains
      (facetWordAngle k (intrinsicRadius (D.model n))
        (intrinsicRadius (cellTypeModel a)) (intrinsicRadius (cellTypeModel b))) := by
  obtain ⟨G, A, B, hG, hA, hB, hGA, hGB, hAB, hAa, hBb⟩ := hw
  have he := h.angles_enclosed n (uniform_finitePolytope hK.1) k G A B hG hA hB
    hGA hGB hAB a b hAa hBb
  have hang : geometricPolygonAngle (uniform_finitePolytope hK.1) hG hA hB =
      facetWordAngle k (intrinsicRadius (D.model n)) (intrinsicRadius A) (intrinsicRadius B) :=
    unitUniform4_canonical_word_angle hK hG hA hB hGA hGB hAB
  rw [hang, intrinsicRadius_cross_congruent hAa, intrinsicRadius_cross_congruent hBb] at he
  exact he

/-- The certified lower endpoint really is a lower bound for every actual
occurrence of the semantic word, including repeated polygon orbits. -/
theorem lower_word_angle {n : CanonicalFacetName} (hK : UnitUniform 4 (D.model n))
    {k : ℕ} {a b : CellType}
    (hw : ModelPolygonWord (D.model n) k (cellTypeModel a) (cellTypeModel b)) :
    (D.angleBall n k a b).lower ≤ facetWordAngle k (intrinsicRadius (D.model n))
      (intrinsicRadius (cellTypeModel a)) (intrinsicRadius (cellTypeModel b)) :=
  (RationalBall.bounds (h.word_angle_enclosed hK hw)).1

end LIB
end Uniform5.Composition
