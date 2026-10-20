import Uniform5.CompositionFacetCellProducts
import Uniform5.CompositionProductSliceTransport

/-! A unique actual model face at one root gives a canonical face at every
vertex. Actual symmetries propagate uniqueness and local translations. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

structure UniqueModelCellSelection (P C : Set (Space 5)) where
  cell : Space 5 → Set (Space 5)
  face : ∀ v ∈ P.extremePoints ℝ, IsConvexFace P (cell v)
  apex : ∀ v ∈ P.extremePoints ℝ, v ∈ cell v
  model : ∀ v ∈ P.extremePoints ℝ, Congruent (cell v) C
  unique : ∀ v ∈ P.extremePoints ℝ, ∀ F, IsConvexFace P F → v ∈ F →
    Congruent F C → F = cell v

/-- Root uniqueness is enough: every other root is obtained by an actual
symmetry of the parent polytope. -/
theorem unitUniform5_unique_model_at_every_vertex
    {P C : Set (Space 5)} (hP : UnitUniform 5 P)
    (hC : IsConvexFace P C) {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvC : v ∈ C)
    (hunique : ∀ F, IsConvexFace P F → v ∈ F → Congruent F C → F = C) :
    ∀ w ∈ P.extremePoints ℝ, ∃ K, IsConvexFace P K ∧ w ∈ K ∧ Congruent K C ∧
      ∀ F, IsConvexFace P F → w ∈ F → Congruent F C → F = K := by
  intro w hw
  obtain ⟨g, hg, hgv⟩ := uniform_vertexTransitive hP.1 v hv w hw
  have hgs : g.symm '' P = P := by
    calc
      g.symm '' P = g.symm '' (g '' P) := congrArg (fun S => g.symm '' S) hg.symm
      _ = P := affineIsometry_symm_image_image g P
  refine ⟨g '' C, ?_, ⟨v, hvC, hgv⟩,
    congruent_symm (congruent_affineIsometryEquiv_image g C), ?_⟩
  · simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hg] using
      embedding_face_image g.toAffineIsometry hC
  · intro F hF hwF hmodel
    have hf : IsConvexFace P (g.symm '' F) := by
      simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hgs] using
        embedding_face_image g.symm.toAffineIsometry hF
    have he := hunique (g.symm '' F) hf ⟨w, hwF, by rw [← hgv, g.symm_apply_apply]⟩
      (congruent_trans (congruent_symm (congruent_affineIsometryEquiv_image g.symm F)) hmodel)
    rw [← he, affineIsometry_image_symm_image]

noncomputable def unitUniform5_uniqueModelCellSelection
    {P C : Set (Space 5)} (hP : UnitUniform 5 P)
    (hC : IsConvexFace P C) {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvC : v ∈ C)
    (hunique : ∀ F, IsConvexFace P F → v ∈ F → Congruent F C → F = C) :
    UniqueModelCellSelection P C := by
  have h := unitUniform5_unique_model_at_every_vertex hP hC hv hvC hunique
  let A := fun w => if hw : w ∈ P.extremePoints ℝ then Classical.choose (h w hw) else C
  refine { cell := A, face := ?_, apex := ?_, model := ?_, unique := ?_ }
  all_goals
    intro w hw
    simp only [A, dif_pos hw]
    first | exact (Classical.choose_spec (h w hw)).1
          | exact (Classical.choose_spec (h w hw)).2.1
          | exact (Classical.choose_spec (h w hw)).2.2.1
          | exact (Classical.choose_spec (h w hw)).2.2.2

namespace UniqueModelCellSelection
variable {P C : Set (Space 5)} (A : UniqueModelCellSelection P C)

theorem equal_of_mem {v w : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hw : w ∈ P.extremePoints ℝ) (hwC : w ∈ A.cell v) : A.cell w = A.cell v :=
  (A.unique w hw (A.cell v) (A.face v hv) hwC (A.model v hv)).symm

theorem symmetry_image (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) (hg : g '' P = P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) : g '' A.cell v = A.cell (g v) := by
  have hgv : g v ∈ P.extremePoints ℝ := by
    rw [← hg, ← affineIsometry_image_extremePoints]
    exact ⟨v, hv, rfl⟩
  apply A.unique (g v) hgv
  · simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hg] using
      embedding_face_image g.toAffineIsometry (A.face v hv)
  · exact ⟨v, A.apex v hv, rfl⟩
  · exact congruent_trans (congruent_symm (congruent_affineIsometryEquiv_image g _))
      (A.model v hv)

theorem dimension {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    affineDimension (A.cell v) = affineDimension C := by
  obtain ⟨g, hg⟩ := (congruent_iff_affineIsometryEquiv_image _ _).mp (A.model v hv)
  exact (affineDimension_image g (A.cell v)).symm.trans
    (congrArg affineDimension hg)

theorem transport_of_root_translates (hP : UnitUniform 5 P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hlateral : ∀ w, Edge P v w → ∃ d ∈ CaseB.normals (A.cell v),
      IsConvexFace P (CaseB.translate (A.cell v) d) ∧
      Congruent (CaseB.translate (A.cell v) d) C ∧ w ∈ CaseB.translate (A.cell v) d) :
    FaceCellTransport P A.cell := by
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
  obtain ⟨d, hd, hF, hmodel, hbF⟩ := hlateral (g.symm b) heb
  have hc : g '' A.cell v = A.cell a := by simpa only [hgv] using A.symmetry_image g hg hv
  have ht : g '' CaseB.translate (A.cell v) d =
      CaseB.translate (A.cell a) (g.linearIsometryEquiv d) := by
    simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hc] using
      embedding_translate g.toAffineIsometry (A.cell v) d
  refine Or.inr ⟨g.linearIsometryEquiv d, ?_, ?_⟩
  · simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hc] using
      embedding_mem_normals g.toAffineIsometry hd
  · symm
    apply A.unique b he.2.1
    · have hh : IsConvexFace (g '' P) (g '' CaseB.translate (A.cell v) d) :=
        embedding_face_image g.toAffineIsometry hF
      rwa [hg, ht] at hh
    · have hh : b ∈ g '' CaseB.translate (A.cell v) d := ⟨g.symm b, hbF, g.apply_symm_apply b⟩
      rwa [ht] at hh
    · rw [← ht]
      exact congruent_trans (congruent_symm (congruent_affineIsometryEquiv_image g _)) hmodel

end UniqueModelCellSelection

/-- The local unique four-face and its actual translations imply K2. -/
theorem unitUniform5_mem_K2_of_unique_root_cell
    {P C : Set (Space 5)} (hP : UnitUniform 5 P)
    (hC : IsConvexFace P C) (hdC : affineDimension C = 4)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvC : v ∈ C)
    (hunique : ∀ F, IsConvexFace P F → v ∈ F → Congruent F C → F = C)
    (hlateral : ∀ w, Edge P v w → ∃ d ∈ CaseB.normals C,
      IsConvexFace P (CaseB.translate C d) ∧ Congruent (CaseB.translate C d) C ∧
      w ∈ CaseB.translate C d) : K2 P := by
  let A := unitUniform5_uniqueModelCellSelection hP hC hv hvC hunique
  have hroot : C = A.cell v := A.unique v hv C hC hvC (congruent_refl C)
  apply actual_four_cells_mem_K2 hP A.cell A.face A.apex
    (A.transport_of_root_translates hP hv (hroot ▸ hlateral)) hv
  rw [A.dimension hv, hdC]

/-- The same proved transport gives K3 for a three-dimensional cell. -/
theorem unitUniform5_mem_K3_of_unique_root_cell
    {P C : Set (Space 5)} (hP : UnitUniform 5 P)
    (hC : IsConvexFace P C) (hdC : affineDimension C = 3)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ) (hvC : v ∈ C)
    (hunique : ∀ F, IsConvexFace P F → v ∈ F → Congruent F C → F = C)
    (hlateral : ∀ w, Edge P v w → ∃ d ∈ CaseB.normals C,
      IsConvexFace P (CaseB.translate C d) ∧ Congruent (CaseB.translate C d) C ∧
      w ∈ CaseB.translate C d) : K3 P := by
  let A := unitUniform5_uniqueModelCellSelection hP hC hv hvC hunique
  have hroot : C = A.cell v := A.unique v hv C hC hvC (congruent_refl C)
  apply actual_three_cells_mem_K3 hP A.cell A.face A.apex
    (A.transport_of_root_translates hP hv (hroot ▸ hlateral)) hv
  rw [A.dimension hv, hdC]

end Uniform5.Composition
