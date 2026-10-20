import Uniform5.CompositionFigureFacetCorrespondence
import Uniform5.CompositionFacetSystemGeneral
import Uniform5.CompositionCycleWords

/-! The actual metric placement in stage 2(a): incident facet figures
have their intrinsic spheres, the prescribed hyperplane offset, and a
strictly interior-side parent center. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An interior point lies strictly on the inner side of a facet's
actual supporting hyperplane, including in a proper affine ambient span. -/
theorem facet_strict_support_of_intrinsicInterior {Q G : Set E}
    (hQ : FinitePolytope Q) (hG : Facet Q G) {o : E}
    (ho : o ∈ intrinsicInterior ℝ Q) :
    ∃ L : E →L[ℝ] ℝ, ∃ t : ℝ,
      (∀ x ∈ Q, L x ≤ t) ∧ G = {x ∈ Q | L x = t} ∧ L o < t := by
  obtain ⟨a, ha⟩ := hG.2.1
  obtain ⟨L, hL⟩ := finitePolytope_face_isExposed hQ hG.1 hG.2.1
  have hmax := (Set.ext_iff.mp hL a).mp ha
  have hs : ∀ x ∈ Q, L x ≤ L a := hmax.2
  have heq : G = {x ∈ Q | L x = L a} := by
    ext x
    rw [hL]
    constructor
    · rintro ⟨hx, hm⟩
      exact ⟨hx, le_antisymm (hs x hx) (hm a (hG.1.2.1 ha))⟩
    · rintro ⟨hx, he⟩
      exact ⟨hx, fun y hy => (hs y hy).trans_eq he.symm⟩
  have hproper : G ≠ Q := by
    intro he
    have hd := hG.2.2
    rw [he] at hd
    omega
  refine ⟨L, L a, hs, heq, lt_of_le_of_ne (hs o (intrinsicInterior_subset ho)) ?_⟩
  intro he
  exact intrinsicInterior_not_mem_proper_face hG.1 hproper ho
    (heq.symm ▸ ⟨intrinsicInterior_subset ho, he⟩)

/-- The nearest-point distance to a sphere section's affine span is the
square root of the difference of the two squared radii. -/
theorem sphere_projection_offset {G : Set E} (hne : G.Nonempty)
    {o b x : E} {r s : ℝ} (hx : x ∈ G)
    (hp : spanProjection G hne o = b) (hr : dist x o = r) (hs : dist x b = s) :
    dist o b = Real.sqrt (r ^ 2 - s ^ 2) ∧
      Metric.infDist o (affineSpan ℝ G : Set E) = Real.sqrt (r ^ 2 - s ^ 2) := by
  letI : Nonempty (affineSpan ℝ G) :=
    ⟨⟨hne.choose, subset_affineSpan ℝ G hne.choose_spec⟩⟩
  have hp' : (EuclideanGeometry.orthogonalProjection (affineSpan ℝ G) o : E) = b := hp
  have hpy := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    o (subset_affineSpan ℝ G hx)
  rw [hp', hr, hs] at hpy
  have hd : r ^ 2 - s ^ 2 = dist o b ^ 2 := by nlinarith [hpy]
  have he : dist o b = Real.sqrt (r ^ 2 - s ^ 2) := by
    rw [hd, Real.sqrt_sq (dist_nonneg : 0 ≤ dist o b)]
  refine ⟨he, ?_⟩
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist, hp', he]

/-- All metric assertions of stage 2(a), before finite library labels are
attached. The hyperplane is the actual affine span of the facet figure:
it has dimension three inside the four-dimensional parent figure. -/
theorem unitUniform5_facet_figure_placement {P K : Set (Space 5)}
    (hP : UnitUniform 5 P) (hK : Facet P K) {v : Space 5}
    (hv : v ∈ K.extremePoints ℝ) :
    let hPP := uniform_finitePolytope hP.1
    let hKP := finitePolytope_face hPP hK.1 hK.2.1
    let c := vertexCentroid (vertices P hPP)
    let a := vertexCentroid (vertices K hKP)
    let Q := vertexFigure P v c
    let G := K ∩ Q
    let o := c + figureCenter (v - c) (intrinsicRadius P)
    let b := a + figureCenter (v - a) (intrinsicRadius K)
    let r := Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2))
    let s := Real.sqrt (1 - 1 / (4 * intrinsicRadius K ^ 2))
    FinitePolytope Q ∧ affineDimension Q = 4 ∧ Facet Q G ∧ affineDimension G = 3 ∧
      o ∈ intrinsicInterior ℝ Q ∧ b ∈ intrinsicInterior ℝ G ∧
      (∀ x ∈ Q.extremePoints ℝ, dist x o = r) ∧
      (∀ x ∈ G.extremePoints ℝ, dist x b = s) ∧
      (∃ hne : G.Nonempty, spanProjection G hne o = b) ∧
      dist o b = Real.sqrt (r ^ 2 - s ^ 2) ∧
      Metric.infDist o (affineSpan ℝ G : Set (Space 5)) = Real.sqrt (r ^ 2 - s ^ 2) ∧
      ∃ L : Space 5 →L[ℝ] ℝ, ∃ t : ℝ,
        (∀ x ∈ Q, L x ≤ t) ∧ G = {x ∈ Q | L x = t} ∧ L o < t := by
  dsimp only
  let hPP := uniform_finitePolytope hP.1
  let hKP := finitePolytope_face hPP hK.1 hK.2.1
  let c := vertexCentroid (vertices P hPP)
  let a := vertexCentroid (vertices K hKP)
  let Q := vertexFigure P v c
  let G := K ∩ Q
  let o := c + figureCenter (v - c) (intrinsicRadius P)
  let b := a + figureCenter (v - a) (intrinsicRadius K)
  have hvP : v ∈ P.extremePoints ℝ := hK.1.2.extremePoints_subset_extremePoints hv
  have hR := uniform_intrinsicRadius_pos hP.1
  obtain ⟨_, _, hs⟩ := uniform_hasIntrinsicRadius hP.1
  have hsD : ∀ x ∈ P.extremePoints ℝ, dist x c = intrinsicRadius P := by
    intro x hx
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp (hs x hx)
  have hQ : FinitePolytope Q := finitePolytope_vertexFigure_of_positiveDimension
    hPP hvP c (intrinsicRadius P) hs hP.2 (by rw [uniform_dimension hP.1]; omega)
  have hdQ : affineDimension Q = 4 := by
    have hh := finitePolytope_unit_vertexFigure_dimension hPP hvP c
      (intrinsicRadius P) hs hP.2 (by simpa using uniform_dimension hP.1) (by simp)
    simpa [Q, Space] using hh
  have hG : Facet Q G :=
    (unitUniform_vertexFigure_facet_correspondence (n := 2) hP hvP).1 K hK hv.1
  have hdG : affineDimension G = 3 := by have hh := hG.2.2; omega
  have ho : o ∈ intrinsicInterior ℝ Q :=
    unitUniform5_centroid_figureCenter_mem_intrinsicInterior hP _ hR hs hvP
  have hrad : ∀ x ∈ Q.extremePoints ℝ,
      dist x o = Real.sqrt (1 - 1 / (4 * intrinsicRadius P ^ 2)) := by
    intro x hx
    have he : Edge P v x := by
      rw [finitePolytope_unit_vertexFigure_extremePoints hPP hvP c _ hs hP.2] at hx
      exact hx
    exact translated_figure_radius (hsD x he.2.1) (hsD v hvP) hR.ne'
      (by rw [dist_comm]; exact hP.2 v x he)
  obtain ⟨Rk, hRk, hsK, heq, hb, hext, hsph⟩ := unitUniform_facet_vertexFigure (n := 1) hP hK hv
  have hRkeq : Rk = intrinsicRadius K := HasIntrinsicRadius.eq_intrinsicRadius
    ⟨hKP, hRk.le, fun x hx => by rw [← dist_eq_norm, hsK x hx]⟩
  subst Rk
  obtain ⟨Rk, hRk', hsK', hne, hproj, _⟩ :=
    unitUniform_facet_figureCenter_projection (n := 1) hP hK hv _ hR hsD
  have hRkeq : Rk = intrinsicRadius K := HasIntrinsicRadius.eq_intrinsicRadius
    ⟨hKP, hRk'.le, fun x hx => by rw [← dist_eq_norm, hsK' x hx]⟩
  subst Rk
  obtain ⟨x, hx⟩ := finitePolytope_extremePoints_nonempty (finitePolytope_facet hQ hG)
  have hxp := hG.1.2.extremePoints_subset_extremePoints hx
  have hoff := sphere_projection_offset hne hx.1 hproj (hrad x hxp) (hsph x hx)
  exact ⟨hQ, hdQ, hG, hdG, ho, hb, hrad, hsph, ⟨hne, hproj⟩,
    hoff.1, hoff.2, facet_strict_support_of_intrinsicInterior hQ hG ho⟩

end Uniform5.Composition
