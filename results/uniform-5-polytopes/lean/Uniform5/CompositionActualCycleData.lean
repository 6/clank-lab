import Uniform5.CompositionClosureDomain
import Uniform5.CompositionCycleReindex
import Uniform5.CompositionSphericalPerimeter

/-! A single actual cycle supplies all geometric inputs to stage 1. -/
noncomputable section
namespace Uniform5.Composition
open Set InnerProductGeometry

/-- Actual incidence data, with no external type labels. -/
structure ActualPolygonCycle (P G : Set (Space 5)) where
  length : ℕ
  length_ge : 3 ≤ length
  cell : ℕ → Set (Space 5)
  cell_face : ∀ i, IsConvexFace P (cell i)
  cell_contains : ∀ i, G ⊆ cell i
  cell_dimension : ∀ i, affineDimension (cell i) = 3
  cell_closed : cell length = cell 0
  cell_injective : Set.InjOn cell (Iio length)
  cell_coverage : ∀ F, IsConvexFace P F → G ⊆ F → affineDimension F = 3 →
    ∃ i < length, cell i = F
  facet : Fin length → Set (Space 5)
  facet_incidence : ∀ i, Facet P (facet i) ∧ G ⊆ facet i ∧
    cell i ⊆ facet i ∧ cell (i.val + 1) ⊆ facet i
  facet_injective : Function.Injective facet
  facet_coverage : ∀ F, (Facet P F ∧ G ⊆ F) ↔ ∃ i, facet i = F
  facets_at_cell : ∀ i : Fin length, ∀ F, (Facet P F ∧ cell i ⊆ F) ↔
    F = facet ((finRotate length).symm i) ∨ F = facet i
  consecutive_unique : ∀ i : Fin length,
    ∃! F, Facet P F ∧ cell i ⊆ F ∧ cell (i.val + 1) ⊆ F

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

noncomputable def height (k : ℕ) (i : ℕ) : ℝ :=
  Real.sqrt ((intrinsicRadius (D.cell i)) ^ 2 - (unitPolygonRadius k) ^ 2)

noncomputable def wordAngle (k : ℕ) (i : ℕ) : ℝ :=
  if hi : i < D.length then facetWordAngle k (intrinsicRadius (D.facet ⟨i, hi⟩))
    (intrinsicRadius (D.cell i)) (intrinsicRadius (D.cell (i + 1))) else 0

theorem cell_unitUniform (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) (i : ℕ) :
    UnitUniform 3 (D.cell i) := by
  have hh := unitUniform_face hP (D.cell_face i)
    ((polygonFace_nonempty hG).mono (D.cell_contains i)) (by rw [D.cell_dimension]; omega)
  rwa [D.cell_dimension] at hh

theorem facet_unitUniform (hP : UnitUniform 5 P) (i : Fin D.length) :
    UnitUniform 4 (D.facet i) :=
  ⟨uniform_facets hP.1 (D.facet_incidence i).1,
    unitEdges_face (uniform_finitePolytope hP.1) (D.facet_incidence i).1.1 hP.2⟩

noncomputable def cellCenter (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    (i : ℕ) : Space 5 :=
  vertexCentroid (vertices (D.cell i) (finitePolytope_face (uniform_finitePolytope hP.1)
    (D.cell_face i) ((polygonFace_nonempty hG).mono (D.cell_contains i))))

noncomputable def polygonCenter (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) : Space 5 :=
  vertexCentroid (vertices G (finitePolytope_face (uniform_finitePolytope hP.1) hG.1
    (polygonFace_nonempty hG)))

theorem height_eq (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) (i : ℕ) :
    D.height k i = ‖D.cellCenter hP hG i - polygonCenter hP hG‖ :=
  (uniform_polygon_cell_offset hP hG (D.cell_face i) (D.cell_contains i) (D.cell_dimension i)).symm

theorem wordAngle_eq (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    {i : ℕ} (hi : i < D.length) : D.wordAngle k i =
      angle (D.cellCenter hP hG i - polygonCenter hP hG)
        (D.cellCenter hP hG (i + 1) - polygonCenter hP hG) := by
  let j : Fin D.length := ⟨i, hi⟩
  have hGj : PolygonFace (D.facet j) G k :=
    ⟨face_restrict hG.1 (D.facet_incidence j).1.1.2.1 (D.facet_incidence j).2.1, hG.2⟩
  have hCA : Facet (D.facet j) (D.cell i) :=
    ⟨face_restrict (D.cell_face i) (D.facet_incidence j).1.1.2.1 (D.facet_incidence j).2.2.1,
      (polygonFace_nonempty hG).mono (D.cell_contains i), by
        rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP j).1]⟩
  have hCB : Facet (D.facet j) (D.cell (i + 1)) :=
    ⟨face_restrict (D.cell_face (i + 1)) (D.facet_incidence j).1.1.2.1
        (D.facet_incidence j).2.2.2,
      (polygonFace_nonempty hG).mono (D.cell_contains (i + 1)), by
        rw [D.cell_dimension, uniform_dimension (D.facet_unitUniform hP j).1]⟩
  rw [wordAngle, dif_pos hi]
  exact (unitUniform4_canonical_word_angle (D.facet_unitUniform hP j) hGj hCA hCB
    (D.cell_contains i) (D.cell_contains (i + 1))
    (cell_cycle_consecutive_ne D.length_ge D.cell D.cell_closed D.cell_injective hi)).symm

theorem strict_perimeter (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    (∑ i ∈ Finset.range D.length, D.wordAngle k i) < 2 * Real.pi := by
  have hh := unitUniform5_natural_cell_cycle_perimeter_lt hP hG D.length_ge D.cell
    D.cell_face D.cell_contains D.cell_dimension D.cell_closed D.cell_injective D.cell_coverage
    (fun i hi => ⟨D.facet ⟨i, hi⟩, D.facet_incidence ⟨i, hi⟩⟩)
  change (∑ i ∈ Finset.range D.length,
    angle (D.cellCenter hP hG i - polygonCenter hP hG)
      (D.cellCenter hP hG (i + 1) - polygonCenter hP hG)) < 2 * Real.pi at hh
  have heq : (∑ i ∈ Finset.range D.length, D.wordAngle k i) =
      ∑ i ∈ Finset.range D.length,
        angle (D.cellCenter hP hG i - polygonCenter hP hG)
          (D.cellCenter hP hG (i + 1) - polygonCenter hP hG) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact D.wordAngle_eq hP hG (Finset.mem_range.mp hi)
  rwa [heq]

theorem geometric_domain (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    ClosureDomain D.length (unitPolygonRadius k) (D.height k) (D.wordAngle k)
      (1 / intrinsicRadius P) := by
  have hp (i : ℕ) : G ≠ D.cell i := by
    intro he
    have hh := D.cell_dimension i
    rw [← he, hG.2.1] at hh
    omega
  have hcp (i : ℕ) : D.cell i ≠ P := by
    intro he
    have hh := D.cell_dimension i
    rw [he, uniform_dimension hP.1] at hh
    omega
  have hh := actual_center_cycle_domain (n := D.length) hP hG D.cell
    D.cell_face D.cell_contains hp hcp
  change ClosureDomain D.length (unitPolygonRadius k)
    (fun i => ‖D.cellCenter hP hG i - polygonCenter hP hG‖)
    (fun i => angle (D.cellCenter hP hG i - polygonCenter hP hG)
      (D.cellCenter hP hG (i + 1) - polygonCenter hP hG)) (1 / intrinsicRadius P) at hh
  obtain ⟨h0, hs, ha⟩ := hh
  refine ⟨h0, ?_, ?_⟩
  · intro i hi
    rw [D.height_eq hP hG]
    exact hs i hi
  · intro i hi
    rw [D.height_eq hP hG, D.height_eq hP hG, D.wordAngle_eq hP hG hi]
    exact ha i hi

/-- All geometric properties required before the computed stage-1 input.
This package contains no library membership or classification conclusion. -/
structure Stage1Geometry (k : ℕ) : Prop where
  polygon_three : 3 ≤ k
  angle_bounds : ∀ i < D.length, 0 ≤ D.wordAngle k i ∧ D.wordAngle k i ≤ Real.pi
  parent_positive : 0 < intrinsicRadius P
  cell_positive : ∀ i, 0 < intrinsicRadius (D.cell i)
  facet_positive : ∀ i, 0 < intrinsicRadius (D.facet i)
  facet_strict : ∀ i, intrinsicRadius (D.facet i) < intrinsicRadius P
  perimeter : (∑ i ∈ Finset.range D.length, D.wordAngle k i) < 2 * Real.pi
  domain : ClosureDomain D.length (unitPolygonRadius k) (D.height k) (D.wordAngle k)
    (1 / intrinsicRadius P)
  closure : cycleClosureFunction D.length (unitPolygonRadius k) (D.height k) (D.wordAngle k)
    (1 / intrinsicRadius P) = 0

end ActualPolygonCycle

/-- An actual uniform five-polytope supplies a single complete incident
cycle, together with every geometric input to S1, with no extra premise. -/
theorem unitUniform5_stage1_geometry {P G : Set (Space 5)}
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k) :
    ∃ D : ActualPolygonCycle P G, D.Stage1Geometry k := by
  obtain ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj, hcov, A, hA, hAinj, hAcov,
    hAtwo, hAunique, hR, hRC, hRA, hzero⟩ := unitUniform5_actual_word_cycle hP hG
  let D : ActualPolygonCycle P G := ⟨n, hn, C, hC, hGC, hdC, hcycle, hinj,
    hcov, A, hA, hAinj, hAcov, hAtwo, hAunique⟩
  refine ⟨D, (polygonFace_unitPolygon hP hG).1, ?_, hR, hRC, hRA, ?_,
    D.strict_perimeter hP hG, D.geometric_domain hP hG, hzero⟩
  · intro i hi
    rw [D.wordAngle_eq hP hG hi]
    exact ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  intro i
  apply uniform_proper_face_intrinsicRadius_lt hP.1 (hA i).1.1 (hA i).1.2.1
  intro he
  have hh := (hA i).1.2.2
  rw [he] at hh
  omega

end Uniform5.Composition
