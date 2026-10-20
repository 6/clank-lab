import Uniform5.CompositionSingleFanCover
import Uniform5.CompositionActualCellProducts

/-! Actual unique-large-polygon assignments. Vertex transitivity supplies
the assignment at every vertex, and uniqueness proves its intrinsic
equivariance and the constant-cell part of the product argument. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem UniqueLargeFaceAt.image {P G : Set (Space 5)} {v : Space 5}
    (h : UniqueLargeFaceAt P v G) (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) :
    UniqueLargeFaceAt (g '' P) (g v) (g '' G) := by
  intro F k hF hk hvF
  have hback : PolygonFace P (g.symm '' F) k := by
    simpa only [affineIsometry_symm_image_image] using polygonFace_image g.symm hF
  have hvback : v ∈ (g.symm '' F).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints]
    exact ⟨g v, hvF, g.symm_apply_apply v⟩
  have he := h (g.symm '' F) k hback hk hvback
  calc
    F = g '' (g.symm '' F) := (affineIsometry_image_symm_image g F).symm
    _ = g '' G := congrArg (fun A => g '' A) he

/-- The one-large-face case at one vertex propagates to every vertex,
with the same actual polygon size. -/
theorem unitUniform5_unique_large_face_at_every_vertex
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hvG : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G) :
    ∀ w ∈ P.extremePoints ℝ,
      ∃ H, PolygonFace P H k ∧ w ∈ H.extremePoints ℝ ∧ UniqueLargeFaceAt P w H := by
  intro w hw
  obtain ⟨g, hg, hgv⟩ := uniform_vertexTransitive hP.1 v hv w hw
  refine ⟨g '' G, ?_, ?_, ?_⟩
  · simpa only [hg] using polygonFace_image g hG
  · rw [← affineIsometry_image_extremePoints]
    exact ⟨v, hvG, hgv⟩
  · simpa only [hg, hgv] using hu.image g

/-- An actual assignment with its proved incidence and uniqueness facts.
The construction below supplies this record from the original polytope. -/
structure UniqueLargeFaceSelection (P : Set (Space 5)) (k : ℕ) where
  face : Space 5 → Set (Space 5)
  polygon : ∀ v ∈ P.extremePoints ℝ, PolygonFace P (face v) k
  apex : ∀ v ∈ P.extremePoints ℝ, v ∈ (face v).extremePoints ℝ
  unique : ∀ v ∈ P.extremePoints ℝ, UniqueLargeFaceAt P v (face v)

noncomputable def unitUniform5_uniqueLargeFaceSelection
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hvG : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G) :
    UniqueLargeFaceSelection P k := by
  classical
  have h := unitUniform5_unique_large_face_at_every_vertex hP hG hv hvG hu
  let C : Space 5 → Set (Space 5) := fun w =>
    if hw : w ∈ P.extremePoints ℝ then Classical.choose (h w hw) else G
  refine ⟨C, ?_, ?_, ?_⟩
  · intro w hw
    simpa only [C, dif_pos hw] using (Classical.choose_spec (h w hw)).1
  · intro w hw
    simpa only [C, dif_pos hw] using (Classical.choose_spec (h w hw)).2.1
  · intro w hw
    simpa only [C, dif_pos hw] using (Classical.choose_spec (h w hw)).2.2

namespace UniqueLargeFaceSelection
variable {P : Set (Space 5)} {k : ℕ} (C : UniqueLargeFaceSelection P k)

/-- At any parent vertex in a selected polygon, uniqueness selects that
same polygon. No edge-connectivity or translation premise is needed. -/
theorem equal_of_mem (hk : 17 ≤ k) {v w : Space 5}
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hwC : w ∈ C.face v) : C.face w = C.face v := by
  have hwe : w ∈ (C.face v).extremePoints ℝ := by
    rw [face_extremePoints_eq (C.polygon v hv).1]
    exact ⟨hwC, hw⟩
  exact (C.unique w hw (C.face v) k (C.polygon v hv) hk hwe).symm

/-- Every actual ambient symmetry maps the selected whole polygon to
the selected polygon at the image vertex. -/
theorem symmetry_image (hk : 17 ≤ k) (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (hg : g '' P = P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    g '' C.face v = C.face (g v) := by
  have hgv : g v ∈ P.extremePoints ℝ := by
    rw [← hg, ← affineIsometry_image_extremePoints]
    exact mem_image_of_mem g hv
  apply C.unique (g v) hgv (g '' C.face v) k
  · simpa only [hg] using polygonFace_image g (C.polygon v hv)
  · exact hk
  · rw [← affineIsometry_image_extremePoints]
    exact mem_image_of_mem g (C.apex v hv)

/-- For the lateral edge case only the actual translated polygon face
and orthogonality remain to be supplied by the prism geometry. -/
theorem transport_of_lateral_faces (hk : 17 ≤ k)
    (hlateral : ∀ v w, Edge P v w → w ∉ C.face v →
      ∃ d ∈ CaseB.normals (C.face v),
        PolygonFace P (CaseB.translate (C.face v) d) k ∧
          w ∈ CaseB.translate (C.face v) d) : FaceCellTransport P C.face := by
  intro v w he
  by_cases hw : w ∈ C.face v
  · exact Or.inl (C.equal_of_mem hk he.1 he.2.1 hw)
  · obtain ⟨d, hd, hF, hwF⟩ := hlateral v w he hw
    have hwe : w ∈ (CaseB.translate (C.face v) d).extremePoints ℝ := by
      rw [face_extremePoints_eq hF.1]
      exact ⟨hwF, he.2.1⟩
    exact Or.inr ⟨d, hd,
      (C.unique w he.2.1 _ k hF hk hwe).symm⟩

theorem mem_K3_of_lateral_faces (hP : UnitUniform 5 P) (hk : 17 ≤ k)
    (hlateral : ∀ v w, Edge P v w → w ∉ C.face v →
      ∃ d ∈ CaseB.normals (C.face v),
        PolygonFace P (CaseB.translate (C.face v) d) k ∧
          w ∈ CaseB.translate (C.face v) d) : K3 P := by
  obtain ⟨v, hv⟩ := finitePolytope_extremePoints_nonempty (uniform_finitePolytope hP.1)
  exact actual_polygon_cells_mem_K3 hP C.face (fun w hw => (C.polygon w hw).1)
    (fun w hw => (C.apex w hw).1) (C.transport_of_lateral_faces hk hlateral)
    hv (C.polygon v hv).2.1

end UniqueLargeFaceSelection
end Uniform5.Composition
