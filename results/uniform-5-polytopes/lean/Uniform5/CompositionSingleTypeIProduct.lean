import Uniform5.CompositionUniqueLargeFaces
import Uniform5.CompositionDuoprismSliceFaces

/-! Actual product reconstruction in the single-large-polygon, type-I
case. Fan coverage supplies the incident duoprism, its coordinate slices
supply whole translated polygons, and transitivity propagates the rule. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem UniqueLargeFaceSelection.mem_K3_of_root_lateral_faces
    {P : Set (Space 5)} {k : ℕ} (C : UniqueLargeFaceSelection P k)
    (hP : UnitUniform 5 P) (hk : 17 ≤ k) {v : Space 5}
    (hv : v ∈ P.extremePoints ℝ)
    (hlateral : ∀ w, Edge P v w →
      ∃ d ∈ CaseB.normals (C.face v),
        PolygonFace P (CaseB.translate (C.face v) d) k ∧
          w ∈ CaseB.translate (C.face v) d) : K3 P := by
  apply C.mem_K3_of_lateral_faces hP hk
  intro a b he _
  obtain ⟨g, hg, hgv⟩ := uniform_vertexTransitive hP.1 v hv a he.1
  have hgs : g.symm '' P = P := by
    calc
      g.symm '' P = g.symm '' (g '' P) := congrArg (fun A => g.symm '' A) hg.symm
      _ = P := affineIsometry_symm_image_image g P
  have heb : Edge P v (g.symm b) := by
    have hh := embedding_edge_image g.symm.toAffineIsometry he
    simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hgs, ← hgv,
      g.symm_apply_apply] using hh
  obtain ⟨d, hd, hF, hbF⟩ := hlateral (g.symm b) heb
  have hc : g '' C.face v = C.face a := by
    simpa only [hgv] using C.symmetry_image hk g hg hv
  have ht : g '' CaseB.translate (C.face v) d =
      CaseB.translate (C.face a) (g.linearIsometryEquiv d) := by
    simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hc] using
      embedding_translate g.toAffineIsometry (C.face v) d
  refine ⟨g.linearIsometryEquiv d, ?_, ?_, ?_⟩
  · simpa only [AffineIsometryEquiv.coe_toAffineIsometry, hc] using
      embedding_mem_normals g.toAffineIsometry hd
  · have hh := polygonFace_image g hF
    rw [hg] at hh
    rwa [ht] at hh
  · have hh : b ∈ g '' CaseB.translate (C.face v) d :=
      ⟨g.symm b, hbF, g.apply_symm_apply b⟩
    rwa [ht] at hh

/-- The entire actual single-face type-I branch lies in K3. The only
inputs beyond geometric hypotheses are the paper's named finite-stage
and lower-dimensional classification assumptions already used by B2. -/
theorem unitUniform5_single_typeI_mem_K3
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    {P G : Set (Space 5)} (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) (hk : 17 ≤ k)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (hvG : v ∈ G.extremePoints ℝ) (hu : UniqueLargeFaceAt P v G)
    (D : ActualPolygonCycle P G) (hI : D.CaseBTypeI k) : K3 P := by
  let C := unitUniform5_uniqueLargeFaceSelection hP hG hv hvG hu
  have hCv : C.face v = G := hu _ k (C.polygon v hv) hk (C.apex v hv)
  apply C.mem_K3_of_root_lateral_faces hP hk hv
  intro w he
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hwV : w ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
    rw [finitePolytope_unit_vertexFigure_extremePoints
      (uniform_finitePolytope hP.1) hv _ (intrinsicRadius P) hs hP.2]
    exact he
  obtain ⟨i, hwi⟩ := unitUniform5_single_fan_vertex_cover
    classification3D classification4D N S hLIB hS1 hB2 hP hG hk hv hu D hwV
  have hK := (D.facet_incidence i).1
  have hwK : w ∈ (D.facet i).extremePoints ℝ := by
    rw [face_extremePoints_eq hK.1]
    exact ⟨hwi.1.1, he.2.1⟩
  obtain ⟨_, q, hq, _⟩ := hI
  have hKU := unitUniform_facet hP hK
  have hGK : PolygonFace (D.facet i) G k :=
    ⟨⟨hG.1.1, hG.1.2.mono hK.1.2.1 (D.facet_incidence i).2.1⟩, hG.2⟩
  obtain ⟨d, hd, hF, hwF⟩ := unitUniform4_duoprism_polygon_translate hKU
    (by omega : 3 ≤ k) (hq i).1 (hq i).2.1 hGK (by omega : k ≠ 4) hwK
  rw [hCv]
  exact ⟨d, hd, polygonFace_trans hK.1 hF, hwF⟩

end Uniform5.Composition
