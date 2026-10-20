import Uniform5.CompositionPolygonChords
import Uniform5.CompositionFaceOrbits
import Uniform5.CaseBMetric

/-!
# The actual long edges in Case B

The polygon chord formula identifies the threshold with a genuine polygon
having at least seventeen sides. Sphere and separation inputs of the Case B
matching lemma are derived from the actual parent polytope.
-/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Actual figure vertices lie one unit from the apex and retain the parent
polytope's separation; the figure itself need not be uniform. -/
theorem unitUniform5_vertexFigure_vertex_metric {P : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ) :
    let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    (∀ x ∈ Q.extremePoints ℝ, dist x v = 1) ∧
      (∀ x ∈ Q.extremePoints ℝ, ∀ y ∈ Q.extremePoints ℝ, x ≠ y → 1 ≤ dist x y) := by
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
    (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
  have hext := finitePolytope_unit_vertexFigure_extremePoints
    (uniform_finitePolytope hP.1) hv _ R hs hP.2
  dsimp only
  constructor
  · intro x hx
    rw [hext] at hx
    simpa only [dist_comm] using hP.2 _ _ hx
  · intro x hx y hy hxy
    rw [hext] at hx hy
    exact unitUniform_separated (n := 2) hP hx.2.1 hy.2.1 hxy

/-- A genuine long figure edge supplies a genuine large polygon of P. -/
theorem unitUniform5_largeFace_of_long_edge {P : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ) {x y : E}
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) : LargeFace P := by
  obtain ⟨F, k, hF, hk, hd⟩ := unitUniform5_vertexFigure_edge_length hP hv he
  refine ⟨F, k, hF, ?_⟩
  by_contra hn
  have hlt : (k : ℝ) < 17 := by exact_mod_cast (show k < 17 by omega)
  have hch := CaseB.chord_strictMono (by change (3 : ℝ) ≤ k; exact_mod_cast hk) (by norm_num) hlt
  rw [hd] at hlong
  exact (not_lt_of_ge hlong) hch

/-- Case B is equivalent to existence of a long edge in the actual figure
at any chosen vertex. Transitivity supplies the forward direction. -/
theorem unitUniform5_largeFace_iff_long_edge {P : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ) :
    LargeFace P ↔ ∃ x y, Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y ∧
      CaseB.chord 17 ≤ dist x y := by
  constructor
  · intro hlarge
    obtain ⟨F, k, hF, hk, hvF⟩ := unitUniform_largeFace_at_vertex hP hlarge hv
    obtain ⟨x, y, he, hd⟩ := unitUniform5_polygon_vertexFigure_edge_length hP hv hF hvF.1
    refine ⟨x, y, he, ?_⟩
    rw [hd]
    exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hk)
  · rintro ⟨x, y, he, hlong⟩
    exact unitUniform5_largeFace_of_long_edge hP hv he hlong

omit [FiniteDimensional ℝ E] in
/-- Distinct unoriented long edges of an actual figure have disjoint
endpoint sets. All metric premises of paper `lem:long` are discharged. -/
theorem unitUniform5_long_edges_disjoint {P : Set E}
    (hP : UnitUniform 5 P) {v : E} (hv : v ∈ P.extremePoints ℝ) {a b c d : E}
    (hab : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) a b)
    (hcd : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) c d)
    (hlong : CaseB.chord 17 ≤ dist a b) (hlong' : CaseB.chord 17 ≤ dist c d)
    (hne : ¬ (a = c ∧ b = d)) (hne' : ¬ (a = d ∧ b = c)) :
    Disjoint ({a, b} : Set E) {c, d} := by
  have hm := unitUniform5_vertexFigure_vertex_metric hP hv
  exact CaseB.long_edges_disjoint hm.1 (by norm_num) hm.2 hab.1 hab.2.1
    hcd.1 hcd.2.1 hlong hlong' hne hne'

end Uniform5.Composition
