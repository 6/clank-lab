import Uniform5.CompositionActualStarPlacements
import Uniform5.CompositionActualStageTwo

/-! Construction of the entire geometric stage-three star from an actual
polytope and its already proved stage-two figure. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

theorem exists_actual_u3_star
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N)
    (f : Space 4 →ᵃⁱ[ℝ] Space 5) {Q : Set (Space 4)}
    (him : f '' Q = vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
    (hf0 : f 0 = vertexCentroid (vertices P (uniform_finitePolytope hP.1)) +
      figureCenter (v - vertexCentroid (vertices P (uniform_finitePolytope hP.1))) (intrinsicRadius P))
    {c : RootRegionClass S}
    (hD : StageTwoFigureConditions N S c (intrinsicRadius P)
      (actualNormalizedStageTwoFigure N hP v f Q)) :
    ∃ X : U3StarData, X.root = v ∧
      X.center = vertexCentroid (vertices P (uniform_finitePolytope hP.1)) ∧
      X.radius = intrinsicRadius P ∧
      X.figure = actualNormalizedStageTwoFigure N hP v f Q ∧
      X.star N = facetStar P v ∧ U3GeometricStar N S c X := by
  let V := vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))
  letI : Fintype {F : Set (Space 4) // Facet Q F} :=
    actualFigureFacetFintype (show FinitePolytope Q from hD.polytope)
  have hex (F : {F : Set (Space 4) // Facet Q F}) :
      ∃ p : U3PlacedFacet, ActualStarPlacement N P v V f F.val p :=
    actual_normalized_facet_placement classification3D classification4D hP hs hv N hLIB f him F.property
  choose p hp using hex
  let e := (Fintype.equivFin {F : Set (Space 4) // Facet Q F}).symm
  let L := List.ofFn (fun i => p (e i))
  let idx (i : Fin L.length) : {F : Set (Space 4) // Facet Q F} :=
    e ⟨i.val, by simpa only [L, List.length_ofFn] using i.isLt⟩
  have hget (i : Fin L.length) : L.get i = p (idx i) := by simp [L, idx]
  have hidx : Function.Bijective idx := by
    constructor
    · intro i j hij
      have he := congrArg Fin.val (e.injective hij)
      exact Fin.ext he
    · intro F
      obtain ⟨i, hi⟩ := e.surjective F
      exact ⟨⟨i.val, by simpa only [L, List.length_ofFn] using i.isLt⟩, hi⟩
  let X : U3StarData := ⟨v, vertexCentroid (vertices P (uniform_finitePolytope hP.1)),
    intrinsicRadius P, actualNormalizedStageTwoFigure N hP v f Q, f, L⟩
  have hprops (i : Fin L.length) : ActualStarPlacement N P v V f (idx i).val (L.get i) :=
    (hget i).symm ▸ hp (idx i)
  have hstar : X.star N = facetStar P v := by
    rw [← actual_placed_facets_complete hP hv N f him p hp]
    change Set.range (fun i : Fin L.length =>
      (L.get i).placement '' N.model (L.get i).name) = _
    ext F
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨idx i, by dsimp only; rw [hget]⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := hidx.2 i
      exact ⟨j, by dsimp only; rw [hget]⟩
  have hfacet (i : Fin L.length) : X.facet N i ∈ facetStar P v :=
    hstar ▸ Set.mem_range_self i
  have hhull : X.hull N = facetStarHull P v := by
    unfold U3StarData.hull facetStarHull
    rw [hstar]
  refine ⟨X, rfl, rfl, rfl, rfl, hstar, ?_⟩
  refine {
    figure := hD
    root_radius := ?_
    figure_center := hf0
    facet_faces := ?_
    facet_labels := ?_
    facet_injective := ?_
    facet_complete := ?_
    base_vertex := ?_
    figure_sections := ?_
    section_exact := ?_
    hull_figure := ?_
    convex_placement := ?_
    sphere := ?_
    separation := ?_ }
  · obtain ⟨_, hR, hsph⟩ := uniform_hasIntrinsicRadius hP.1
    change dist v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) = intrinsicRadius P
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hR).mp (hsph v hv)
  · intro i
    change Facet Q (L.get i).figureFace
    rw [(hprops i).1]
    exact (idx i).property
  · intro i
    exact (hprops i).2.1.trans (congrArg
      (normalizedFigureFacetLabel N P v V f) (hprops i).1.symm)
  · intro i j hij
    apply hidx.1
    apply Subtype.ext
    change (L.get i).figureFace = (L.get j).figureFace at hij
    rwa [(hprops i).1, (hprops j).1] at hij
  · intro H hH
    obtain ⟨i, hi⟩ := hidx.2 ⟨H, hH⟩
    exact ⟨i, (hprops i).1.trans (congrArg Subtype.val hi)⟩
  · intro i
    exact (hprops i).2.2.2.2.1
  · intro i
    change (L.get i).placement '' N.figureModel (L.get i).name = f '' (L.get i).figureFace
    rw [(hprops i).1]
    exact (hprops i).2.2.2.2.2.1
  · intro i
    change ((L.get i).placement '' N.model (L.get i).name) ∩ (f '' Q) = f '' (L.get i).figureFace
    rw [him, (hprops i).1]
    exact (hprops i).2.2.2.2.2.2
  · change f '' Q = vertexFigure (X.hull N) v _
    rw [hhull, unitUniform5_facetStarHull_figure hP hv]
    exact him
  · intro i
    rw [hhull]
    exact unitUniform5_facetStarHull_facet hP hv (hfacet i)
  · intro x hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨_, hR, hsph⟩ := uniform_hasIntrinsicRadius hP.1
    have hxP := (hfacet i).1.1.2.extremePoints_subset_extremePoints hi
    change dist x (vertexCentroid (vertices P (uniform_finitePolytope hP.1))) = intrinsicRadius P
    rw [dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) hR).mp (hsph x hxP)
  · rintro x ⟨i, hi⟩ y ⟨j, hj⟩ hxy
    exact unitUniform_separated hP
      ((hfacet i).1.1.2.extremePoints_subset_extremePoints hi)
      ((hfacet j).1.1.2.extremePoints_subset_extremePoints hj) hxy


/-- The full actual star satisfies the geometric realization search input;
its signature and radius closure are derived before the U3 input is used. -/
theorem unitUniform5_smallFaces_u3_star
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {P : Set (Space 5)} (hP : UnitUniform 5 P) (hs : SmallFaces P)
    {v : Space 5} (hv : v ∈ P.extremePoints ℝ)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (T : StageTwoNumericalData S)
    (hLIB : LIB N) (hS : S1 N S) (hS2 : S2 N S T) :
    ∃ c : ActiveRootClass S, c.val ∈ survivingRootClasses N S ∧
      ∃ X : U3StarData, X.root = v ∧
        X.center = vertexCentroid (vertices P (uniform_finitePolytope hP.1)) ∧
        X.radius = intrinsicRadius P ∧ X.star N = facetStar P v ∧
        ∃ hX : U3GeometricStar N S c.val X,
          X.radius ∈ radiusClassRegion S c ∧
          X.figure.signature hX.figure ∈ T.signatures c ∧
          (X.figure.signature hX.figure).RadiusCompatible N X.radius := by
  obtain ⟨_, j, hj, hc, _⟩ := unitUniform5_smallFaces_first_stage
    classification3D classification4D hP hs N S hLIB hS hv
  let c : ActiveRootClass S := ⟨_, (Finset.mem_filter.mp hc).1⟩
  have hR : intrinsicRadius P ∈ radiusClassRegion S c := radius_mem_classRegion S c rfl hj
  obtain ⟨f, Q, him, hf0, _, hQ, hdQ, h0, _, _, hsphere, hsep⟩ :=
    unitUniform5_vertexFigure_centered_model hP hv
  let hD := actualNormalizedStageTwo_conditions classification3D classification4D
    hP hs hv N S hLIB hS f hQ hdQ h0 him hf0 hsphere hsep hj
  obtain ⟨X, hxroot, hxcenter, hxradius, hxfigure, hxstar, hX⟩ :=
    exists_actual_u3_star classification3D classification4D hP hs hv N S hLIB f him hf0 hD
  refine ⟨c, hc, X, hxroot, hxcenter, hxradius, hxstar, hX, ?_, ?_, ?_⟩
  · rwa [hxradius]
  · have hsig := hS2.complete c hc _ hR _ hD
    simpa only [hxfigure] using hsig
  · have hclosure := actualNormalizedStageTwo_radiusCompatible
      classification3D classification4D hP hs hv N hLIB f hQ him
    simpa only [hxfigure, hxradius] using hclosure

end Uniform5.Composition
