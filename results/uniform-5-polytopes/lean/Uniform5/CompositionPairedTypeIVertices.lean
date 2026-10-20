import Uniform5.CompositionPairedTypeIActual
import Uniform5.CompositionPairedFacetUniqueness

/-! The two surviving three-slot actual Type I fans have the same fifth
vertex. Consequently every root neighbor is in the common facet or is
that single remaining vertex. -/
noncomputable section
namespace Uniform5.Composition
open Set
namespace TypeIFanChart
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

theorem three_fan_vertices_eq (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (hlen : D.length = 3) (j : Fin D.length) :
    actualPolygonFanVertices hP D v =
      insert (T.lateral (finRotate D.length (finRotate D.length j)))
        ((D.facet j ∩ vertexFigure P v
          (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ) := by
  ext x
  rw [T.mem_fan_vertices hP hG hvG, T.facet_figure_vertices hP hG hvG]
  constructor
  · rintro (rfl | rfl | ⟨i, rfl⟩)
    · simp
    · simp
    · rcases finRotate_three_enumeration hlen j i with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem remaining_not_facet_vertices (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ) (j : Fin D.length) :
    T.lateral (finRotate D.length (finRotate D.length j)) ∉
      (D.facet j ∩ vertexFigure P v
        (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
  rw [T.facet_figure_vertices hP hG hvG]
  rintro (ha | hb | hc | hd)
  · exact T.lateral_ne_a _ ha
  · exact T.lateral_ne_b _ hb
  · exact (finRotate_ne_and_twice_ne D.length_ge j).2 (T.lateral_injective hc)
  · exact (finRotate_ne_and_twice_ne D.length_ge (finRotate D.length j)).1
      (T.lateral_injective hd)

theorem remaining_eq_partner_remaining (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hvG : v ∈ G.extremePoints ℝ)
    {H : Set (Space 5)} {m : ℕ} (hH : PolygonFace P H m)
    (hvH : v ∈ H.extremePoints ℝ) (A : ActualPolygonCycle P H)
    (U : TypeIFanChart A v m) (hlenA : A.length = 3)
    (j : Fin D.length) (k : Fin A.length) (hfacet : D.facet j = A.facet k)
    (hmem : T.lateral (finRotate D.length (finRotate D.length j)) ∈
      actualPolygonFanVertices hP A v) :
    T.lateral (finRotate D.length (finRotate D.length j)) =
      U.lateral (finRotate A.length (finRotate A.length k)) := by
  rw [U.three_fan_vertices_eq hP hH hvH hlenA k] at hmem
  rcases hmem with he | he
  · exact he
  · exact (T.remaining_not_facet_vertices hP hG hvG j (hfacet.symm ▸ he)).elim

theorem paired_three_neighbor_coverage
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} {m : ℕ}
    (hH : PolygonFace P H m) (hvH : v ∈ H.extremePoints ℝ)
    (A : ActualPolygonCycle P H) (U : TypeIFanChart A v m)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 3) (hlenA : A.length = 3)
    (j : Fin D.length) (k : Fin A.length) (hfacet : D.facet j = A.facet k)
    (hcH : Edge H v (T.lateral j))
    (hdH : Edge H v (T.lateral (finRotate D.length j)))
    {w : Space 5} (hw : Edge P v w) :
    w ∈ D.facet j ∨ w = T.lateral (finRotate D.length (finRotate D.length j)) := by
  have hmem := T.paired_k3_lateral_mem_partner classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hvG hH A hcover hlen j hcH hdH
  have heq := T.remaining_eq_partner_remaining hP hG hvG hH hvH A U hlenA j k hfacet hmem
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hwV : w ∈ (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))).extremePoints ℝ := by
    rw [finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hP.1)
      hw.1 _ (intrinsicRadius P) hs hP.2]
    exact hw
  rcases unitUniform5_two_fan_vertex_cover classification3D classification4D N S
    hLIB hS1 hB2 hP hG hn hw.1 hcover D A hwV with hwD | hwA
  · change w ∈ actualPolygonFanVertices hP D v at hwD
    rw [T.three_fan_vertices_eq hP hG hvG hlen j] at hwD
    rcases hwD with he | he
    · exact Or.inr he
    · exact Or.inl he.1.1
  · change w ∈ actualPolygonFanVertices hP A v at hwA
    rw [U.three_fan_vertices_eq hP hH hvH hlenA k] at hwA
    rcases hwA with he | he
    · exact Or.inr (he.trans heq.symm)
    · exact Or.inl (hfacet.symm ▸ he.1.1)

end TypeIFanChart
end Uniform5.Composition
