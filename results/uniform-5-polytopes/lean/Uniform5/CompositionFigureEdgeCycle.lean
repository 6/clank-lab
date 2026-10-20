import Uniform5.CompositionFigureFaceOrder
import Uniform5.CompositionActualCycleData

/-! Complete geometric incidence cycles around actual vertex-figure edges.
Ridges and facets are actual convex faces, with exhaustive coverage and
cyclic adjacency; the parent polygon cycle supplies all these properties. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- A complete incidence cycle around an edge of a four-dimensional finite
polytope. Natural ridge indices include the repeated closing ridge. -/
structure ActualEdgeIncidenceCycle {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Q e : Set E) (n : ℕ) where
  polytope : FinitePolytope Q
  dimension : affineDimension Q = 4
  edge_face : IsConvexFace Q e
  edge_nonempty : e.Nonempty
  edge_dimension : affineDimension e = 1
  length_ge : 3 ≤ n
  ridge : ℕ → Set E
  ridge_face : ∀ i, IsConvexFace Q (ridge i)
  ridge_contains : ∀ i, e ⊆ ridge i
  ridge_dimension : ∀ i, affineDimension (ridge i) = 2
  ridge_closed : ridge n = ridge 0
  ridge_injective : Set.InjOn ridge (Iio n)
  ridge_coverage : ∀ H, IsConvexFace Q H → e ⊆ H → affineDimension H = 2 →
    ∃ i < n, ridge i = H
  facet : Fin n → Set E
  facet_incidence : ∀ i, Facet Q (facet i) ∧ e ⊆ facet i ∧
    ridge i ⊆ facet i ∧ ridge (i.val + 1) ⊆ facet i
  facet_injective : Function.Injective facet
  facet_coverage : ∀ H, (Facet Q H ∧ e ⊆ H) ↔ ∃ i, facet i = H
  facets_at_ridge : ∀ i : Fin n, ∀ H, (Facet Q H ∧ ridge i ⊆ H) ↔
    H = facet ((finRotate n).symm i) ∨ H = facet i
  consecutive_unique : ∀ i : Fin n,
    ∃! H, Facet Q H ∧ ridge i ⊆ H ∧ ridge (i.val + 1) ⊆ H

namespace ActualPolygonCycle

/-- Sectioning the original actual polygon cycle preserves the complete
cycle of actual cells/facets as actual ridges/facets around the figure edge.
The index sets and their cyclic order are unchanged. -/
noncomputable def figureEdgeCycle {P G : Set (Space 5)} (D : ActualPolygonCycle P G)
    (hP : UnitUniform 5 P) {k : ℕ} (hG : PolygonFace P G k)
    {v : Space 5} (hv : v ∈ G.extremePoints ℝ) :
    let Q := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
    ActualEdgeIncidenceCycle Q (G ∩ Q) D.length := by
  let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
  let Q := vertexFigure P v c
  have hvP := hG.1.2.extremePoints_subset_extremePoints hv
  have hc (i : ℕ) : v ∈ D.cell i := D.cell_contains i hv.1
  have ha (i : Fin D.length) : v ∈ D.facet i := (D.facet_incidence i).2.1 hv.1
  have hsection {A B : Set (Space 5)} (hA : IsConvexFace P A)
      (hB : IsConvexFace P B) (hvA : v ∈ A) (hvB : v ∈ B) :
      A ∩ Q ⊆ B ∩ Q ↔ A ⊆ B :=
    unitUniform_vertexFigure_section_subset_iff (n := 2) hP hvP hA hB hvA hvB
  have hrank := unitUniform_vertexFigure_face_correspondence (n := 2) hP hvP
  have hfac := unitUniform_vertexFigure_facet_correspondence (n := 2) hP hvP
  have he := (hrank 1).1 G hG.1 hv.1 hG.2.1
  have hcells (i : ℕ) := (hrank 2).1 (D.cell i) (D.cell_face i) (hc i) (D.cell_dimension i)
  have hfacets (i : Fin D.length) := hfac.1 (D.facet i) (D.facet_incidence i).1 (ha i)
  have hQdim : FinitePolytope Q ∧ affineDimension Q = 4 := by
    obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical
      (uniform_finitePolytope hP.1) (uniform_vertexTransitive hP.1)
    have hQ : FinitePolytope Q := finitePolytope_vertexFigure_of_positiveDimension
      (uniform_finitePolytope hP.1) hvP c R hs hP.2 (by rw [uniform_dimension hP.1]; omega)
    have hdQ : affineDimension Q = 4 := by
      have hh := finitePolytope_unit_vertexFigure_dimension
        (uniform_finitePolytope hP.1) hvP c R hs hP.2
        (by simpa using uniform_dimension hP.1) (by simp)
      simpa [Q, Space] using hh
    exact ⟨hQ, hdQ⟩
  refine {
    polytope := hQdim.1
    dimension := hQdim.2
    edge_face := he.1
    edge_nonempty := he.2.1
    edge_dimension := he.2.2
    length_ge := D.length_ge
    ridge := fun i => D.cell i ∩ Q
    ridge_face := fun i => (hcells i).1
    ridge_contains := fun i x hx => ⟨D.cell_contains i hx.1, hx.2⟩
    ridge_dimension := fun i => (hcells i).2.2
    ridge_closed := congrArg (fun A => A ∩ Q) D.cell_closed
    ridge_injective := ?_
    ridge_coverage := ?_
    facet := fun i => D.facet i ∩ Q
    facet_incidence := ?_
    facet_injective := ?_
    facet_coverage := ?_
    facets_at_ridge := ?_
    consecutive_unique := ?_ }
  · intro i hi j hj hij
    apply D.cell_injective hi hj
    exact ((hsection (D.cell_face i) (D.cell_face j) (hc i) (hc j)).mp hij.subset).antisymm
      ((hsection (D.cell_face j) (D.cell_face i) (hc j) (hc i)).mp hij.symm.subset)
  · intro H hH heH hdH
    obtain ⟨A, ⟨hA, hvA, hdA, hAH⟩, _⟩ := (hrank 2).2 H hH (he.2.1.mono heH) hdH
    have hGA : G ⊆ A := (hsection hG.1 hA hv.1 hvA).mp (hAH.symm ▸ heH)
    obtain ⟨i, hi, hiA⟩ := D.cell_coverage A hA hGA hdA
    exact ⟨i, hi, by rw [hiA]; exact hAH⟩
  · intro i
    exact ⟨hfacets i, fun x hx => ⟨(D.facet_incidence i).2.1 hx.1, hx.2⟩,
      fun x hx => ⟨(D.facet_incidence i).2.2.1 hx.1, hx.2⟩,
      fun x hx => ⟨(D.facet_incidence i).2.2.2 hx.1, hx.2⟩⟩
  · intro i j hij
    apply D.facet_injective
    exact ((hsection (D.facet_incidence i).1.1 (D.facet_incidence j).1.1
      (ha i) (ha j)).mp hij.subset).antisymm
      ((hsection (D.facet_incidence j).1.1 (D.facet_incidence i).1.1
        (ha j) (ha i)).mp hij.symm.subset)
  · intro H
    constructor
    · rintro ⟨hH, heH⟩
      obtain ⟨A, ⟨hA, hvA, hAH⟩, _⟩ := hfac.2 H hH
      have hGA : G ⊆ A := (hsection hG.1 hA.1 hv.1 hvA).mp (hAH.symm ▸ heH)
      obtain ⟨i, hi⟩ := (D.facet_coverage A).mp ⟨hA, hGA⟩
      exact ⟨i, by rw [hi]; exact hAH⟩
    · rintro ⟨i, rfl⟩
      exact ⟨hfacets i, fun x hx => ⟨(D.facet_incidence i).2.1 hx.1, hx.2⟩⟩
  · intro i H
    constructor
    · rintro ⟨hH, hCH⟩
      obtain ⟨A, ⟨hA, hvA, hAH⟩, _⟩ := hfac.2 H hH
      have hCA := (hsection (D.cell_face i) hA.1 (hc i) hvA).mp (hAH.symm ▸ hCH)
      rcases (D.facets_at_cell i A).mp ⟨hA, hCA⟩ with h | h
      · exact Or.inl (hAH.symm.trans (congrArg (fun A => A ∩ Q) h))
      · exact Or.inr (hAH.symm.trans (congrArg (fun A => A ∩ Q) h))
    · intro hh
      have hA : Facet P (D.facet ((finRotate D.length).symm i)) ∧
          D.cell i ⊆ D.facet ((finRotate D.length).symm i) :=
        (D.facets_at_cell i _).mpr (Or.inl rfl)
      rcases hh with rfl | rfl
      · exact ⟨hfacets _, fun x hx => ⟨hA.2 hx.1, hx.2⟩⟩
      · exact ⟨hfacets _, fun x hx => ⟨(D.facet_incidence i).2.2.1 hx.1, hx.2⟩⟩
  · intro i
    obtain ⟨A, ⟨hA, hCA, hCB⟩, huniq⟩ := D.consecutive_unique i
    have hvA : v ∈ A := hCA (hc i)
    refine ⟨A ∩ Q, ⟨hfac.1 A hA hvA,
      fun x hx => ⟨hCA hx.1, hx.2⟩, fun x hx => ⟨hCB hx.1, hx.2⟩⟩, ?_⟩
    rintro H ⟨hH, hCH, hCH'⟩
    obtain ⟨B, ⟨hB, hvB, hBH⟩, _⟩ := hfac.2 H hH
    have hBA : B = A := huniq B ⟨hB,
      (hsection (D.cell_face i) hB.1 (hc i) hvB).mp (hBH.symm ▸ hCH),
      (hsection (D.cell_face (i.val + 1)) hB.1 (hc _) hvB).mp (hBH.symm ▸ hCH')⟩
    exact hBH.symm.trans (congrArg (fun A => A ∩ Q) hBA)

@[simp] theorem figureEdgeCycle_ridge {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) {v : Space 5} (hv : v ∈ G.extremePoints ℝ) (i : ℕ) :
    (D.figureEdgeCycle hP hG hv).ridge i = D.cell i ∩
      vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := rfl

@[simp] theorem figureEdgeCycle_facet {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) (hP : UnitUniform 5 P) {k : ℕ}
    (hG : PolygonFace P G k) {v : Space 5} (hv : v ∈ G.extremePoints ℝ) (i : Fin D.length) :
    (D.figureEdgeCycle hP hG hv).facet i = D.facet i ∩
      vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) := rfl

end ActualPolygonCycle
end Uniform5.Composition
