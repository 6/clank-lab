import Uniform5.CompositionLibraryBalls

/-! Concrete library vertex-figure templates and actual model transport. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem embedding_vertexFigure (f : E →ᵃⁱ[ℝ] F) (P : Set E) (v c : E) :
    f '' vertexFigure P v c = vertexFigure (f '' P) (f v) (f c) := by
  have hh (x : E) : sphereHeight (f c - f v) (f x - f v) =
      sphereHeight (c - v) (x - v) := by
    change (2 : ℝ) * inner (f c - f v) (f x - f v) = (2 : ℝ) * inner (c - v) (x - v)
    have hc : f c - f v = f.linearIsometry (c - v) := (f.map_vsub c v).symm
    have hx : f x - f v = f.linearIsometry (x - v) := (f.map_vsub x v).symm
    rw [hc, hx, f.linearIsometry.inner_map_map]
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyL⟩, rfl⟩
    exact ⟨mem_image_of_mem f hy, (hh y).trans hyL⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyL⟩
    exact ⟨y, ⟨hy, (hh y).symm.trans hyL⟩, rfl⟩

variable [FiniteDimensional ℝ E]

/-- Vertex transitivity aligns a prescribed model vertex with a prescribed
actual vertex, while the same affine embedding matches the whole hull. -/
theorem exists_vertex_matched_embedding {n : ℕ} {P : Set E}
    (hP : UnitUniform (n + 3) P) {Q : Set (Space (n + 3))}
    (hPQ : Congruent P Q) {v : E} (hv : v ∈ P.extremePoints ℝ)
    {w : Space (n + 3)} (hw : w ∈ Q.extremePoints ℝ) :
    ∃ f : Space (n + 3) →ᵃⁱ[ℝ] E, f '' Q = P ∧ f w = v := by
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hP.1)
    (uniform_dimension hP.1) hPQ
  have hv' := hv
  rw [← hf, ← embedding_extremePoints] at hv'
  obtain ⟨x, hx, rfl⟩ := hv'
  have hQ := (unitUniform_cross_congruent_iff hPQ (n + 3)).mp hP
  obtain ⟨g, hg, hgw⟩ := uniform_vertexTransitive hQ.1 w hw x hx
  refine ⟨f.comp g.toAffineIsometry, ?_, ?_⟩
  · change (f ∘ g) '' Q = P
    rw [image_comp, hg, hf]
  · change f (g w) = f x
    rw [hgw]

/-- Intrinsic congruence of whole uniform polytopes preserves their actual
vertex figures at any selected pair of vertices. -/
theorem unitUniform_vertexFigure_model_congruent {n : ℕ} {P : Set E}
    (hP : UnitUniform (n + 3) P) {Q : Set (Space (n + 3))}
    (hPQ : Congruent P Q) {v : E} (hv : v ∈ P.extremePoints ℝ)
    {w : Space (n + 3)} (hw : w ∈ Q.extremePoints ℝ) :
    let hQ := (unitUniform_cross_congruent_iff hPQ (n + 3)).mp hP
    Congruent (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (vertexFigure Q w (vertexCentroid (vertices Q (uniform_finitePolytope hQ.1)))) := by
  dsimp only
  let hQ := (unitUniform_cross_congruent_iff hPQ (n + 3)).mp hP
  obtain ⟨f, hf, hfv⟩ := exists_vertex_matched_embedding hP hPQ hv hw
  have hc := embedding_vertexCentroid f (uniform_finitePolytope hQ.1)
  have hfig := embedding_vertexFigure f Q w
    (vertexCentroid (vertices Q (uniform_finitePolytope hQ.1)))
  have heV : vertices (f '' Q)
      ((finitePolytope_affineIsometry_image_iff f Q).mpr (uniform_finitePolytope hQ.1)) =
      vertices P (uniform_finitePolytope hP.1) := by
    apply Finset.coe_injective
    simp only [coe_vertices, hf]
  have hc' := hc.trans (congrArg vertexCentroid heV)
  rw [hc', hf, hfv] at hfig
  have hh := congruent_affineIsometry_image f
    (vertexFigure Q w (vertexCentroid (vertices Q (uniform_finitePolytope hQ.1))))
  rw [hfig] at hh
  exact congruent_symm hh

namespace LibraryNumericalData
noncomputable def baseVertex (N : LibraryNumericalData) (f : CanonicalFacetName) : Space 4 :=
  if h : (N.vertexSet f).Nonempty then Classical.choose h else 0

noncomputable def figureModel (N : LibraryNumericalData) (f : CanonicalFacetName) : Set (Space 4) :=
  vertexFigure (N.model f) (N.baseVertex f) (vertexCentroid (N.vertexSet f))
end LibraryNumericalData

namespace LIB
variable {N : LibraryNumericalData} (hLIB : LIB N)
include hLIB

theorem vertexSet_eq (f : CanonicalFacetName) (hF : FinitePolytope (N.model f)) :
    N.vertexSet f = vertices (N.model f) hF := by
  apply Finset.coe_injective
  rw [hLIB.vertices_exact, coe_vertices]

theorem baseVertex_extreme (f : CanonicalFacetName) :
    N.baseVertex f ∈ (N.model f).extremePoints ℝ := by
  obtain ⟨r, hR, _⟩ := hLIB.radius_enclosed f
  have hF := hR.1
  have hne : (N.vertexSet f).Nonempty := by
    rw [hLIB.vertexSet_eq f hF]
    exact vertices_nonempty hF
  rw [LibraryNumericalData.baseVertex, dif_pos hne, ← hLIB.vertices_exact]
  exact Classical.choose_spec hne

theorem actual_figure_matches {P : Set E} (hP : UnitUniform 4 P)
    {f : CanonicalFacetName} (hPf : Congruent P (N.model f))
    {v : E} (hv : v ∈ P.extremePoints ℝ) :
    Congruent (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (N.figureModel f) := by
  have hm := (unitUniform_cross_congruent_iff hPf 4).mp hP
  have hh := unitUniform_vertexFigure_model_congruent hP hPf hv (hLIB.baseVertex_extreme f)
  change Congruent _ (vertexFigure (N.model f) (N.baseVertex f) _)
  rwa [hLIB.vertexSet_eq f (uniform_finitePolytope hm.1)]

end LIB
end Uniform5.Composition
