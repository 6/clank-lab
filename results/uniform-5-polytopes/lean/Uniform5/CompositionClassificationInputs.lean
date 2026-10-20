import Uniform5.CompositionPolyhedronModels
import Uniform5.CompositionExceptionalModels
import Uniform5.CompositionFigureRidgeCorrespondence
import Uniform5.CompositionPolygonClosure
import Uniform5.CompositionTransverseTangent
import Uniform5.CaseBInputs

/-!
# The two cited classification inputs, with concrete interpretations

These are precisely Facts 3-D and 4-D in the manuscript, under the paper's
unit-edge convention. The five Platonic and thirteen Archimedean entries
use the node orders and ring sets defined by the concrete library models. No uniformity,
existence of a snub seed, or classification is proved by a model definition.

A vertex configuration is read from a complete, injective cyclic edge walk
on the actual two-dimensional vertex figure. Its labels count the actual
vertices of the unique incident polygon faces. Existence of this geometric
configuration is proved independently of the cited classifications.
-/

noncomputable section
namespace Uniform5.Composition
open Set Classical

noncomputable def A3RingModel (J : Finset (Fin 3)) (P : Set (Space 3)) : Prop :=
  ∃ x : ModelSpace 4, (∑ i, x i) = 0 ∧ WythoffSeed rootsA3 J x ∧
    Congruent P (WythoffHull rootsA3 x)

noncomputable def B3RingModel (J : Finset (Fin 3)) (P : Set (Space 3)) : Prop :=
  ∃ x : ModelSpace 3, WythoffSeed rootsB3 J x ∧ Congruent P (WythoffHull rootsB3 x)

noncomputable def H3RingModel (J : Finset (Fin 3)) (P : Set (Space 3)) : Prop :=
  ∃ x : ModelSpace 3, WythoffSeed rootsH3 J x ∧ Congruent P (WythoffHull rootsH3 x)

/-- Tetrahedron, octahedron, cube, icosahedron, dodecahedron, in that order. -/
noncomputable def PlatonicModel : Fin 5 → Set (Space 3) → Prop :=
  ![A3RingModel {0}, B3RingModel {0}, B3RingModel {2}, H3RingModel {2}, H3RingModel {0}]

/-- The thirteen entries in the source's order: tut, co, tic, toe, sirco,
girco, id, tid, ti, srid, grid, snic, snid. -/
noncomputable def ArchimedeanModel : Fin 13 → Set (Space 3) → Prop :=
  ![A3RingModel {0, 1}, B3RingModel {1}, B3RingModel {1, 2}, B3RingModel {0, 1},
    B3RingModel {0, 2}, B3RingModel {0, 1, 2}, H3RingModel {1}, H3RingModel {1, 2},
    H3RingModel {0, 1}, H3RingModel {0, 2}, H3RingModel {0, 1, 2},
    IsSnubCube, IsSnubDodeca]

/-- A4, B4, D4, F4, H4, in the order of Fact 4-D. -/
noncomputable def Wythoff4Model : Fin 5 → Set (Space 4) → Prop :=
  ![IsA4Wythoff, IsB4Wythoff, IsD4Wythoff, IsF4Wythoff, IsH4Wythoff]

/-- The cyclic polygon-size sequence around an actual vertex. Both choices
of orientation and of starting vertex are allowed by the existential walk. -/
noncomputable def ActualVertexConfiguration (P : Set (Space 3)) {n : ℕ}
    (sizes : Fin n → ℕ) : Prop :=
  ∃ hP : FinitePolytope P, ∃ v : Space 3, ∃ u : ℕ → Space 3,
    ∃ F : Fin n → Set (Space 3),
    let Q := vertexFigure P v (vertexCentroid (vertices P hP))
    v ∈ P.extremePoints ℝ ∧ affineDimension Q = 2 ∧ 3 ≤ n ∧
      u '' Iio n = Q.extremePoints ℝ ∧ Set.InjOn u (Iio n) ∧ u n = u 0 ∧
      (∀ i < n, Edge Q (u i) (u (i + 1))) ∧
      ∀ i : Fin n, PolygonFace P (F i) (sizes i) ∧ v ∈ F i ∧
        F i ∩ Q = segment ℝ (u i) (u (i.val + 1))

noncomputable def SameVertexConfiguration (P Q : Set (Space 3)) : Prop :=
  ∃ n : ℕ, ∃ sizes : Fin n → ℕ,
    ActualVertexConfiguration P sizes ∧ ActualVertexConfiguration Q sizes

/-- Every actual finite convex polygon admits a complete simple boundary
cycle; translation removes the auxiliary origin-interior condition. -/
theorem finitePolytope_two_dimensional_cycle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : FinitePolytope S) (hdS : affineDimension S = 2) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ u : ℕ → E,
      u '' Iio n = S.extremePoints ℝ ∧ Set.InjOn u (Iio n) ∧ u n = u 0 ∧
      ∀ i < n, Edge S (u i) (u (i + 1)) := by
  let a := vertexCentroid (vertices S hS)
  let g := AffineIsometryEquiv.constVAdd ℝ E (-a)
  have hga : g a = 0 := by simp [g]
  have h0 : (0 : E) ∈ intrinsicInterior ℝ (g '' S) := by
    change (0 : E) ∈ intrinsicInterior ℝ (g.toAffineIsometry '' S)
    rw [g.toAffineIsometry.image_intrinsicInterior]
    rw [← hga]
    exact mem_image_of_mem g (vertexCentroid_mem_intrinsicInterior hS)
  obtain ⟨n, u, hrange, hinj, hcycle, _, hedge, ⟨hfan⟩⟩ :=
    exists_intrinsic_edge_ray_fan (finitePolytope_image g hS)
      (by rwa [affineDimension_image]) h0
  refine ⟨n, sphericalFanData_three_le hfan, fun i => g.symm (u i), ?_, ?_,
    congrArg g.symm hcycle, ?_⟩
  · rw [← image_image, hrange, affineIsometry_image_extremePoints,
      affineIsometry_symm_image_image]
  · intro i hi j hj hij
    exact hinj hi hj (g.symm.injective hij)
  · intro i hi
    simpa only [affineIsometry_symm_image_image] using edge_image g.symm (hedge i hi)

/-- Nonvacuity of the geometric cyclic configuration: no classification
input is used to obtain the sequence or its actual incident polygon faces. -/
theorem unitUniform3_exists_vertexConfiguration {P : Set (Space 3)}
    (hP : UnitUniform 3 P) : ∃ n : ℕ, ∃ sizes : Fin n → ℕ,
      ActualVertexConfiguration P sizes := by
  let hPP := uniform_finitePolytope hP.1
  obtain ⟨v, hv⟩ := vertices_nonempty hPP
  have hvP := (mem_vertices hPP v).mp hv
  let c := vertexCentroid (vertices P hPP)
  obtain ⟨R, _, hs⟩ := finitePolytope_transitive_cospherical hPP
    (uniform_vertexTransitive hP.1)
  have hQ := finitePolytope_vertexFigure_of_positiveDimension hPP hvP c R hs hP.2
    (by rw [uniform_dimension hP.1]; norm_num)
  have hd := finitePolytope_unit_vertexFigure_dimension hPP hvP c R hs hP.2
    (by rw [uniform_dimension hP.1]; simp [Space]) (by simp [Space])
  have hdQ : affineDimension (vertexFigure P v c) = 2 := by
    simpa [Space] using hd
  obtain ⟨n, hn, u, hrange, hinj, hcycle, hedge⟩ :=
    finitePolytope_two_dimensional_cycle hQ hdQ
  have hparents : ∀ i : Fin n, ∃ F, IsConvexFace P F ∧ v ∈ F ∧
      affineDimension F = 2 ∧ F ∩ vertexFigure P v c = segment ℝ (u i) (u (i.val + 1)) := by
    intro i
    exact ((unitUniform_vertexFigure_face_correspondence (n := 0) hP hvP 1).2
      _ (edge_isConvexFace (hedge i i.isLt)) ⟨u i, left_mem_segment ℝ _ _⟩
      (edge_dimension (hedge i i.isLt))).exists
  choose F hF using hparents
  let hfaces (i : Fin n) := finitePolytope_face hPP (hF i).1 ⟨v, (hF i).2.1⟩
  refine ⟨n, fun i => (vertices (F i) (hfaces i)).card, hPP, v, u, F,
    hvP, hdQ, hn, hrange, hinj, hcycle, hedge, ?_⟩
  intro i
  exact ⟨⟨(hF i).1, (hF i).2.2.1, vertices (F i) (hfaces i),
    coe_vertices _ _, rfl⟩, (hF i).2.1, (hF i).2.2.2⟩

theorem sameVertexConfiguration_refl {P : Set (Space 3)} (hP : UnitUniform 3 P) :
    SameVertexConfiguration P P := by
  obtain ⟨n, sizes, hs⟩ := unitUniform3_exists_vertexConfiguration hP
  exact ⟨n, sizes, hs, hs⟩

/-- The figure edge forces both its actual parent face and its polygon-size
label; the cyclic sequence does not permit an arbitrary relabeling. -/
theorem vertexConfiguration_edge_label_unique {P : Set (Space 3)}
    (hP : UnitUniform 3 P) {v x y : Space 3} (hv : v ∈ P.extremePoints ℝ)
    (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    {F G : Set (Space 3)} {k l : ℕ} (hF : PolygonFace P F k)
    (hG : PolygonFace P G l) (hvF : v ∈ F) (hvG : v ∈ G)
    (hsectionF : F ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) = segment ℝ x y)
    (hsectionG : G ∩ vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) = segment ℝ x y) :
    F = G ∧ k = l := by
  obtain ⟨H, _, hunique⟩ :=
    (unitUniform_vertexFigure_face_correspondence (n := 0) hP hv 1).2 _
      (edge_isConvexFace he) ⟨x, left_mem_segment ℝ x y⟩ (edge_dimension he)
  have hFG : F = G := (hunique F ⟨hF.1, hvF, hF.2.1, hsectionF⟩).trans
    (hunique G ⟨hG.1, hvG, hG.2.1, hsectionG⟩).symm
  refine ⟨hFG, ?_⟩
  rw [← hFG] at hG
  exact (polygonFace_extremePoints_ncard hF).symm.trans (polygonFace_extremePoints_ncard hG)

/-- Every slot of the existing semantic interface is now an actual geometric
predicate or congruence to a specified coordinate hull. -/
noncomputable def concreteClassificationModels :
    CaseB.ClassificationModels (Set (Space 3)) (Set (Space 4)) where
  uniform3 := UnitUniform 3
  uniform4 := UnitUniform 4
  congruent3 := Congruent
  sameVertexConfiguration := SameVertexConfiguration
  hasPolygon3 := fun P q => ∃ F, PolygonFace P F q
  hasPolygon4 := fun P q => ∃ F, PolygonFace P F q
  platonic := fun P => ∃ i, PlatonicModel i P
  archimedean := ArchimedeanModel
  prism := fun q P => Congruent P (polygonPrismModel q)
  antiprism := fun q P => Congruent P (antiprismModel q)
  wythoff4 := Wythoff4Model
  snub24 := IsSnub24
  grandAntiprism := IsGrandAntiprism
  polyhedronPrism := fun Q P => Congruent P (polyhedralPrismModel Q)
  duoprism := fun p q P => Congruent P (duoprismModel p q)
  antiprismPrism := fun q P => Congruent P (antiprismPrismModel q)

/-- Named hypothesis for precisely Fact 3-D, including cyclic-configuration
uniqueness and the large-polygon consequence. -/
noncomputable def CitedClassification3D : Prop :=
  CaseB.Classification3D concreteClassificationModels

/-- Named hypothesis for precisely Fact 4-D, including its large-polygon
consequence. All models in this statement are concrete finite hulls or
explicit reflection orbits, and the prism base is actually unit-uniform. -/
noncomputable def CitedClassification4D : Prop :=
  CaseB.Classification4D concreteClassificationModels

end Uniform5.Composition
