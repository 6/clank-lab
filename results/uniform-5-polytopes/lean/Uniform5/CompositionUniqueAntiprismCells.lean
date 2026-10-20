import Uniform5.CompositionProductSliceTransport
import Uniform5.CompositionUniqueLargeFaces
import Uniform5.CompositionAntiprismPrismSpecifiedCell

/-! Actual antiprism-cell uniqueness and selection in the one-large-polygon
case. The cycle count and actual vertex transitivity supply all incidences. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- Arbitrary actual antiprism three-faces through the same large polygon
are equal, by the proved at-most-one antiprism ray in its actual cycle. -/
theorem unitUniform5_antiprism_cell_unique
    (classification4D : CitedClassification4D)
    {P G C D : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hC : IsConvexFace P C) (hD : IsConvexFace P D)
    (hGC : G ⊆ C) (hGD : G ⊆ D)
    (hdC : affineDimension C = 3) (hdD : affineDimension D = 3)
    (hCA : Congruent C (antiprismModel n)) (hDA : Congruent D (antiprismModel n)) : C = D := by
  obtain ⟨A, _⟩ := unitUniform5_stage1_geometry hP hG
  obtain ⟨i, hi, hCi⟩ := A.cell_coverage C hC hGC hdC
  obtain ⟨j, hj, hDj⟩ := A.cell_coverage D hD hGD hdD
  have hcount := A.antiprism_count_le_one classification4D hP hG
    (large_polygon_nonexceptional hn)
  have hiA : (⟨i, hi⟩ : Fin A.length) ∈ A.antiprismRayIndices n := by
    simp only [ActualPolygonCycle.antiprismRayIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [hCi] using hCA
  have hjA : (⟨j, hj⟩ : Fin A.length) ∈ A.antiprismRayIndices n := by
    simp only [ActualPolygonCycle.antiprismRayIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [hDj] using hDA
  have he := (Finset.card_le_one.mp hcount) _ hiA _ hjA
  exact hCi.symm.trans ((congrArg A.cell (congrArg Fin.val he)).trans hDj)

/-- Every vertex of an actual antiprism cell lies on an actual n-gon
of that cell, transported from the literal model. -/
theorem antiprism_cell_polygon_through_vertex
    {P C : Set (Space 5)} (hP : UnitUniform 5 P) (hC : IsConvexFace P C)
    (hdC : affineDimension C = 3) {n : ℕ} (hn : 3 ≤ n)
    (hCA : Congruent C (antiprismModel n)) {v : Space 5}
    (hv : v ∈ C.extremePoints ℝ) :
    ∃ G, PolygonFace P G n ∧ G ⊆ C ∧ v ∈ G.extremePoints ℝ := by
  have hCU : UnitUniform 3 C := by
    have h := unitUniform_all_faces hP hC ⟨v, hv.1⟩
    rwa [hdC] at h
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model
    (uniform_finitePolytope hCU.1) hdC hCA
  obtain ⟨G, hG⟩ := antiprism_polygonFace hn
  have hGC : PolygonFace C (f '' G) n := by
    rw [← hf]
    exact embedding_polygonFace_image f hG
  obtain ⟨g, _, hGG, hvg⟩ := polygon_orbit_through_vertex
    (uniform_finitePolytope hCU.1) (uniform_vertexTransitive hCU.1) hGC hv
  exact ⟨g '' (f '' G), polygonFace_trans hC hGG, hGG.1.2.1, hvg⟩

/-- The selected large polygon at any vertex of an antiprism cell lies
inside that very cell. -/
theorem UniqueLargeFaceSelection.face_subset_antiprism
    {P C : Set (Space 5)} {n : ℕ} (L : UniqueLargeFaceSelection P n)
    (hP : UnitUniform 5 P) (hn : 17 ≤ n)
    (hC : IsConvexFace P C) (hdC : affineDimension C = 3)
    (hCA : Congruent C (antiprismModel n)) {v : Space 5}
    (hv : v ∈ P.extremePoints ℝ) (hvC : v ∈ C) : L.face v ⊆ C := by
  have hve : v ∈ C.extremePoints ℝ := by
    rw [face_extremePoints_eq hC]
    exact ⟨hvC, hv⟩
  obtain ⟨G, hG, hGC, hvG⟩ := antiprism_cell_polygon_through_vertex hP hC hdC
    (by omega) hCA hve
  rwa [L.unique v hv G n hG hn hvG] at hGC

/-- The chosen antiprism three-face at each actual vertex. -/
structure AntiprismCellSelection (P : Set (Space 5)) (n : ℕ) where
  cell : Space 5 → Set (Space 5)
  face : ∀ v ∈ P.extremePoints ℝ, IsConvexFace P (cell v)
  apex : ∀ v ∈ P.extremePoints ℝ, v ∈ cell v
  dimension : ∀ v ∈ P.extremePoints ℝ, affineDimension (cell v) = 3
  model : ∀ v ∈ P.extremePoints ℝ, Congruent (cell v) (antiprismModel n)

/-- Existence of one actual antiprism cell through the root propagates
by actual symmetries; uniqueness will identify all independent choices. -/
theorem unitUniform5_antiprism_cell_at_every_vertex
    {P C : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hC : IsConvexFace P C) (hdC : affineDimension C = 3)
    (hCA : Congruent C (antiprismModel n))
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvC : v ∈ C) :
    ∀ w ∈ P.extremePoints ℝ, ∃ D, IsConvexFace P D ∧ w ∈ D ∧
      affineDimension D = 3 ∧ Congruent D (antiprismModel n) := by
  intro w hw
  obtain ⟨g, hg, hgv⟩ := uniform_vertexTransitive hP.1 v hv w hw
  refine ⟨g '' C, ?_, ⟨v, hvC, hgv⟩, ?_, ?_⟩
  · simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hg] using embedding_face_image g.toAffineIsometry hC
  · rw [affineDimension_image, hdC]
  · exact congruent_trans (congruent_symm (congruent_affineIsometryEquiv_image g C)) hCA

noncomputable def unitUniform5_antiprismCellSelection
    {P C : Set (Space 5)} (hP : UnitUniform 5 P) {n : ℕ}
    (hC : IsConvexFace P C) (hdC : affineDimension C = 3)
    (hCA : Congruent C (antiprismModel n))
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvC : v ∈ C) :
    AntiprismCellSelection P n := by
  have h := unitUniform5_antiprism_cell_at_every_vertex hP hC hdC hCA hv hvC
  let A := fun w => if hw : w ∈ P.extremePoints ℝ then Classical.choose (h w hw) else C
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  all_goals
    intro w hw
    simp only [A, dif_pos hw]
    first | exact (Classical.choose_spec (h w hw)).1
          | exact (Classical.choose_spec (h w hw)).2.1
          | exact (Classical.choose_spec (h w hw)).2.2.1
          | exact (Classical.choose_spec (h w hw)).2.2.2

namespace AntiprismCellSelection
variable {P : Set (Space 5)} {n : ℕ} (A : AntiprismCellSelection P n)

theorem unique_at_vertex (classification4D : CitedClassification4D)
    (L : UniqueLargeFaceSelection P n) (hP : UnitUniform 5 P) (hn : 17 ≤ n)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) {C : Set (Space 5)}
    (hC : IsConvexFace P C) (hvC : v ∈ C) (hdC : affineDimension C = 3)
    (hCA : Congruent C (antiprismModel n)) : C = A.cell v :=
  unitUniform5_antiprism_cell_unique classification4D hP (L.polygon v hv) hn
    hC (A.face v hv)
    (L.face_subset_antiprism hP hn hC hdC hCA hv hvC)
    (L.face_subset_antiprism hP hn (A.face v hv) (A.dimension v hv) (A.model v hv) hv (A.apex v hv))
    hdC (A.dimension v hv) hCA (A.model v hv)

theorem equal_of_mem (classification4D : CitedClassification4D)
    (L : UniqueLargeFaceSelection P n) (hP : UnitUniform 5 P) (hn : 17 ≤ n)
    {v w : Space 5} (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hwC : w ∈ A.cell v) : A.cell w = A.cell v :=
  (A.unique_at_vertex classification4D L hP hn hw (A.face v hv) hwC
    (A.dimension v hv) (A.model v hv)).symm

theorem symmetry_image (classification4D : CitedClassification4D)
    (L : UniqueLargeFaceSelection P n) (hP : UnitUniform 5 P) (hn : 17 ≤ n)
    (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) (hg : g '' P = P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    g '' A.cell v = A.cell (g v) := by
  have hgv : g v ∈ P.extremePoints ℝ := by
    rw [← hg, ← affineIsometry_image_extremePoints]
    exact ⟨v, hv, rfl⟩
  apply A.unique_at_vertex classification4D L hP hn hgv
  · simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hg] using embedding_face_image g.toAffineIsometry (A.face v hv)
  · exact ⟨v, A.apex v hv, rfl⟩
  · rw [affineDimension_image, A.dimension v hv]
  · exact congruent_trans (congruent_symm (congruent_affineIsometryEquiv_image g _))
      (A.model v hv)

/-- Actual lateral three-faces at one root suffice for the global
orthogonal product. Their identification with the selected cells follows
from the actual cycle's uniqueness theorem, and transitivity propagates
all translations to the full edge graph. -/
theorem mem_K3_of_root_lateral_cells (classification4D : CitedClassification4D)
    (L : UniqueLargeFaceSelection P n) (hP : UnitUniform 5 P) (hn : 17 ≤ n)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hlateral : ∀ w, Edge P v w → ∃ d ∈ CaseB.normals (A.cell v),
      IsConvexFace P (CaseB.translate (A.cell v) d) ∧
      affineDimension (CaseB.translate (A.cell v) d) = 3 ∧
      Congruent (CaseB.translate (A.cell v) d) (antiprismModel n) ∧
      w ∈ CaseB.translate (A.cell v) d) : K3 P := by
  apply actual_three_cells_mem_K3 hP A.cell A.face A.apex ?_ hv (A.dimension v hv)
  intro a b he
  obtain ⟨g, hg, hgv⟩ := uniform_vertexTransitive hP.1 v hv a he.1
  have hgs : g.symm '' P = P := by
    calc
      g.symm '' P = g.symm '' (g '' P) := congrArg (fun S => g.symm '' S) hg.symm
      _ = P := affineIsometry_symm_image_image g P
  have heb : Edge P v (g.symm b) := by
    have hh := embedding_edge_image g.symm.toAffineIsometry he
    simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hgs, ← hgv,
      g.symm_apply_apply] using hh
  obtain ⟨d, hd, hF, hdim, hmodel, hbF⟩ := hlateral (g.symm b) heb
  have hc : g '' A.cell v = A.cell a := by
    simpa only [hgv] using A.symmetry_image classification4D L hP hn g hg hv
  have ht : g '' CaseB.translate (A.cell v) d =
      CaseB.translate (A.cell a) (g.linearIsometryEquiv d) := by
    simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hc] using
      embedding_translate g.toAffineIsometry (A.cell v) d
  refine Or.inr ⟨g.linearIsometryEquiv d, ?_, ?_⟩
  · simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hc] using
      embedding_mem_normals g.toAffineIsometry hd
  · symm
    apply A.unique_at_vertex classification4D L hP hn he.2.1
    · have hh : IsConvexFace (g '' P) (g '' CaseB.translate (A.cell v) d) :=
        embedding_face_image g.toAffineIsometry hF
      rwa [hg, ht] at hh
    · have hh : b ∈ g '' CaseB.translate (A.cell v) d :=
        ⟨g.symm b, hbF, g.apply_symm_apply b⟩
      rwa [ht] at hh
    · rw [← ht, affineDimension_image, hdim]
    · rw [← ht]
      exact congruent_trans (congruent_symm (congruent_affineIsometryEquiv_image g _)) hmodel

end AntiprismCellSelection
end Uniform5.Composition
