import Uniform5.CompositionCenteredModel
import Uniform5.CompositionFigurePlacement
import Uniform5.CompositionLongEdges
import Uniform5.CompositionEmbedding

/-! Four-dimensional centered coordinates for actual vertex figures.
The affine embedding records the original center and all actual vertices,
so the normalization can be used by geometric placement arguments. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Every actual vertex figure has a full-dimensional centered realization
in four-dimensional Euclidean space. The sphere radius and separation are
derived from the parent unit-uniform polytope, not supplied as model data. -/
theorem unitUniform5_vertexFigure_centered_model {P : Set (Space 5)}
    (hP : UnitUniform 5 P) {v : Space 5} (hv : v ∈ P.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    let V := vertexFigure P v c
    let o := c + figureCenter (v - c) (intrinsicRadius P)
    ∃ (f : Space 4 →ᵃⁱ[ℝ] Space 5) (Q : Set (Space 4)),
      f '' Q = V ∧ f 0 = o ∧ Congruent Q V ∧
      FinitePolytope Q ∧ affineDimension Q = 4 ∧
      (0 : Space 4) ∈ intrinsicInterior ℝ Q ∧ affineSpan ℝ Q = ⊤ ∧
      f '' Q.extremePoints ℝ = V.extremePoints ℝ ∧
      (∀ x ∈ Q.extremePoints ℝ,
        ‖x‖ = Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2))) ∧
      (∀ x ∈ Q.extremePoints ℝ, ∀ y ∈ Q.extremePoints ℝ,
        x ≠ y → 1 ≤ dist x y) := by
  dsimp only
  let hPP := uniform_finitePolytope hP.1
  let c := vertexCentroid (vertices P hPP)
  let V := vertexFigure P v c
  let o := c + figureCenter (v - c) (intrinsicRadius P)
  obtain ⟨R, hR, hs, hm⟩ := unitUniform5_vertexFigure_metric hP
  have hReq : R = intrinsicRadius P := HasIntrinsicRadius.eq_intrinsicRadius
    ⟨hPP, hR.le, fun x hx => by rw [← dist_eq_norm, hs x hx]⟩
  subst R
  obtain ⟨_, _, ho, hrad⟩ := hm v hv
  have hs2 : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = intrinsicRadius P ^ 2 := by
    intro x hx
    rw [← dist_eq_norm, hs x hx]
  have hV : FinitePolytope V := finitePolytope_vertexFigure_of_positiveDimension
    hPP hv c (intrinsicRadius P) hs2 hP.2 (by rw [uniform_dimension hP.1]; omega)
  have hdV : affineDimension V = 4 := by
    have hh := finitePolytope_unit_vertexFigure_dimension hPP hv c
      (intrinsicRadius P) hs2 hP.2 (by simpa using uniform_dimension hP.1) (by simp)
    simpa [V, Space] using hh
  obtain ⟨f, Q, him, hf0, hQ, hdQ, h0, htop⟩ :=
    exists_finitePolytope_centered_intrinsic_model V hV 4 hdV o ho
  have hc : Congruent Q V := by
    rw [← him]
    exact congruent_affineIsometry_image f Q
  have hext : f '' Q.extremePoints ℝ = V.extremePoints ℝ := by
    rw [embedding_extremePoints, him]
  refine ⟨f, Q, him, hf0, hc, hQ, hdQ, h0, htop, hext, ?_, ?_⟩
  · intro x hx
    have hfx : f x ∈ V.extremePoints ℝ := hext ▸ mem_image_of_mem f hx
    have hd := hrad (f x) hfx
    change dist (f x) o = _ at hd
    rw [← hf0, f.isometry.dist_eq, dist_zero_right] at hd
    exact hd
  · intro x hx y hy hxy
    have hfx : f x ∈ V.extremePoints ℝ := hext ▸ mem_image_of_mem f hx
    have hfy : f y ∈ V.extremePoints ℝ := hext ▸ mem_image_of_mem f hy
    have hh := (unitUniform5_vertexFigure_vertex_metric hP hv).2
      (f x) hfx (f y) hfy (fun he => hxy (f.injective he))
    rwa [f.isometry.dist_eq] at hh

end Uniform5.Composition
