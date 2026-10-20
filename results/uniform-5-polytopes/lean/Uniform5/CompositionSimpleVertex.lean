import Uniform5.CompositionFigureRanks
import Uniform5.CompositionFigure

/-!
# Actual simplex face lattices and simple vertices
-/

noncomputable section
namespace Uniform5.Composition
open Set Classical
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every subset of the vertices of an affinely independent finite hull
spans an actual convex face. Coefficient uniqueness proves extremality. -/
theorem affineIndependent_subset_isFace (V T : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) (hTV : T ⊆ V) :
    IsConvexFace (convexHull ℝ (V : Set E)) (convexHull ℝ (T : Set E)) := by
  refine ⟨convex_convexHull ℝ (T : Set E), convexHull_mono hTV, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨u, hu, hsumu, hxu⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨v, hv, hsumv, hyv⟩ := Finset.mem_convexHull'.mp hy
  obtain ⟨w, hw, hsumw, hzw⟩ := Finset.mem_convexHull'.mp hz
  obtain ⟨a, b, ha, hb, hab, hxyz⟩ := hseg
  let d : E → ℝ := fun i => a * u i + b * v i - if i ∈ T then w i else 0
  have hsumd : ∑ i ∈ V, d i = 0 := by
    simp only [d, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hTV, hsumu, hsumv, hsumw]
    linarith
  have hvecd : ∑ i ∈ V, d i • i = 0 := by
    simp only [d, sub_smul, add_smul, mul_smul, ite_smul, zero_smul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum,
      ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hTV, hxu, hyv, hzw]
    rw [hxyz, sub_self]
  have hdz := hV.eq_zero_of_sum_eq_zero_subtype hsumd hvecd
  have huz : ∀ i ∈ V, i ∉ T → u i = 0 := by
    intro i hi hiT
    have heq : a * u i + b * v i = 0 := by simpa [d, hiT] using hdz i hi
    have hmul : a * u i = 0 := by nlinarith [mul_nonneg ha.le (hu i hi), mul_nonneg hb.le (hv i hi)]
    exact (mul_eq_zero.mp hmul).resolve_left ha.ne'
  have hvz : ∀ i ∈ V, i ∉ T → v i = 0 := by
    intro i hi hiT
    have heq : a * u i + b * v i = 0 := by simpa [d, hiT] using hdz i hi
    have hmul : b * v i = 0 := by nlinarith [mul_nonneg ha.le (hu i hi), mul_nonneg hb.le (hv i hi)]
    exact (mul_eq_zero.mp hmul).resolve_left hb.ne'
  constructor
  · apply Finset.mem_convexHull'.mpr
    refine ⟨u, fun i hi => hu i (hTV hi), ?_, ?_⟩
    · rwa [Finset.sum_subset hTV huz]
    · rw [Finset.sum_subset hTV (fun i hi hiT => by simp [huz i hi hiT])]
      exact hxu
  · apply Finset.mem_convexHull'.mpr
    refine ⟨v, fun i hi => hv i (hTV hi), ?_, ?_⟩
    · rwa [Finset.sum_subset hTV hvz]
    · rw [Finset.sum_subset hTV (fun i hi hiT => by simp [hvz i hi hiT])]
      exact hyv

/-- Every generator of an affinely independent finite hull is an actual
extreme point. -/
theorem affineIndependent_mem_extremePoints (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) {x : E} (hx : x ∈ V) :
    x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ := by
  have hf := affineIndependent_subset_isFace V {x} hV (by simpa)
  simpa only [Finset.coe_singleton, convexHull_singleton, singleton_face_iff_extremePoint]
    using hf

/-- An original simplex vertex belongs to a sub-simplex exactly when it
is one of that sub-simplex's generators. -/
theorem affineIndependent_mem_subhull_iff (V T : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) (hTV : T ⊆ V)
    {x : E} (hx : x ∈ V) : x ∈ convexHull ℝ (T : Set E) ↔ x ∈ T := by
  refine ⟨fun hxT => ?_, fun hxT => subset_convexHull ℝ (T : Set E) hxT⟩
  apply extremePoints_convexHull_subset (𝕜 := ℝ)
  exact inter_extremePoints_subset_extremePoints_of_subset (convexHull_mono hTV)
    ⟨hxT, affineIndependent_mem_extremePoints V hV hx⟩

/-- The incident simplex vertices of an actual geometric face. -/
noncomputable def simplexVerticesIn (V : Finset E)
    (F : GeometricFace (convexHull ℝ (V : Set E))) : Finset V :=
  Finset.univ.filter (fun x : V => (x : E) ∈ F.val)

@[simp] theorem mem_simplexVerticesIn (V : Finset E)
    (F : GeometricFace (convexHull ℝ (V : Set E))) (x : V) :
    x ∈ simplexVerticesIn V F ↔ (x : E) ∈ F.val := by simp [simplexVerticesIn]

/-- A simplex's actual geometric face poset is the full subset lattice of
its vertices. No combinatorial face correspondence is assumed. -/
noncomputable def simplexFaceEquiv (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) :
    GeometricFace (convexHull ℝ (V : Set E)) ≃o Finset V where
  toFun := simplexVerticesIn V
  invFun T := ⟨convexHull ℝ ((T.image (fun x : V => (x : E))) : Set E),
    affineIndependent_subset_isFace V (T.image (fun x : V => (x : E))) hV (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact y.property)⟩
  left_inv F := by
    apply Subtype.ext
    change convexHull ℝ
      ((simplexVerticesIn V F).image (fun x : V => (x : E)) : Set E) = F.val
    rw [face_convexHull_eq F.property]
    congr 1
    ext x
    simp only [Finset.mem_coe, Finset.mem_image, mem_simplexVerticesIn, Set.mem_inter_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxV, hxF⟩
      exact ⟨⟨x, hxV⟩, hxF, rfl⟩
  right_inv T := by
    ext x
    rw [mem_simplexVerticesIn]
    change (x : E) ∈ convexHull ℝ (T.image (fun x : V => (x : E)) : Set E) ↔ x ∈ T
    rw [affineIndependent_mem_subhull_iff V _ hV (by
      intro y hy
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
      exact z.property) x.property]
    simp only [Finset.mem_image, Subtype.coe_inj]
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
  map_rel_iff' := by
    intro F G
    constructor
    · intro hFG
      change F.val ⊆ G.val
      rw [face_convexHull_eq F.property, face_convexHull_eq G.property]
      apply convexHull_mono
      intro x hx
      exact ⟨hx.1, (mem_simplexVerticesIn V G ⟨x, hx.1⟩).mp
        (hFG ((mem_simplexVerticesIn V F ⟨x, hx.1⟩).mpr hx.2))⟩
    · intro hFG x hx
      exact (mem_simplexVerticesIn V G x).mpr (hFG ((mem_simplexVerticesIn V F x).mp hx))

/-- The existing simplex-lattice interface is realized by actual geometric
faces, rather than supplied as an independent hypothesis. -/
noncomputable def simplexFaceLattice (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) :
    VertexFigureSimplexFaceLattice (simplexVerticesIn V) :=
  ⟨simplexFaceEquiv V hV, fun _ => rfl⟩

/-- A finite hull with exactly dimension plus one generators is a simplex. -/
theorem affineIndependent_of_card_dimension (V : Finset E) (n : ℕ)
    (hcard : V.card = n + 1) (hdim : affineDimension (convexHull ℝ (V : Set E)) = n) :
    AffineIndependent ℝ ((↑) : V → E) := by
  apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ ((↑) : V → E)
    (by simpa only [Fintype.card_coe] using hcard)).mpr
  have hrange : Set.range ((↑) : V → E) = (V : Set E) := by ext x; simp
  rw [hrange]
  unfold affineDimension Uniform5.affineDimension at hdim
  rw [affineSpan_convexHull (𝕜 := ℝ), direction_affineSpan] at hdim
  exact hdim

/-- Actual neighbors of the zero vertex, as a finite set. -/
noncomputable def zeroNeighbors (V : Finset E) : Finset E :=
  V.filter (fun x => IsEdge V 0 x)

@[simp] theorem mem_zeroNeighbors (V : Finset E) (x : E) :
    x ∈ zeroNeighbors V ↔ IsEdge V 0 x := by
  simp only [zeroNeighbors, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩

@[simp] theorem coe_zeroNeighbors (V : Finset E) :
    (zeroNeighbors V : Set E) = {x | IsEdge V 0 x} := by ext x; simp

/-- The actual incident edge endpoints belonging to an apex face. -/
noncomputable def apexNeighborsIn (V : Finset E)
    (F : {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val}) :
    Finset (zeroNeighbors V) :=
  Finset.univ.filter (fun x : zeroNeighbors V => (x : E) ∈ F.val.val)

@[simp] theorem mem_apexNeighborsIn (V : Finset E)
    (F : {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val})
    (x : zeroNeighbors V) : x ∈ apexNeighborsIn V F ↔ (x : E) ∈ F.val.val := by
  simp [apexNeighborsIn]

/-- Set equality transports actual geometric faces without changing their sets. -/
noncomputable def geometricFace_congr {P Q : Set E} (h : P = Q) :
    GeometricFace P ≃o GeometricFace Q where
  toFun F := ⟨F.val, h ▸ F.property⟩
  invFun F := ⟨F.val, h.symm ▸ F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

/-- The actual neighbor hull at a degree-four vertex of a four-dimensional
polytope is a three-dimensional simplex. -/
theorem zeroSimpleVertex_neighbors_affineIndependent [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hedge : ∀ x, IsEdge V 0 x → L x = 1)
    (hdim : affineDimension (convexHull ℝ (V : Set E)) = 4)
    (hfour : (zeroNeighbors V).card = 4) :
    AffineIndependent ℝ ((↑) : zeroNeighbors V → E) := by
  have hsection : heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ (zeroNeighbors V : Set E) := by
    rw [coe_zeroNeighbors]
    exact finiteHull_section_eq_convexHull_edges V hzero hvertices L hheight hedge
  have hne : (V.erase 0).Nonempty := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (zeroNeighbors V).card by omega)
    have he := (mem_zeroNeighbors V x).mp hx
    exact ⟨x, Finset.mem_erase.mpr ⟨he.2.2.1.symm, he.2.1⟩⟩
  have hdimSection : affineDimension (heightSection (convexHull ℝ (V : Set E)) L) = 3 := by
    have hs : heightSection (convexHull ℝ (V : Set E)) L =
        convexHull ℝ ((fun x => (L x)⁻¹ • x) '' (V.erase 0 : Set E)) :=
      finiteHull_radial_section V hzero L hheight
    have hd := finiteHull_radialHull_dimension_intrinsic V hzero L.toLinearMap
      (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one (hheight x hx))) hne
    change affineDimension (convexHull ℝ ((fun x => (L x)⁻¹ • x) '' (V.erase 0 : Set E))) + 1 =
      affineDimension (convexHull ℝ (V : Set E)) at hd
    rw [← hs, hdim] at hd
    omega
  have hWi : AffineIndependent ℝ ((↑) : zeroNeighbors V → E) :=
    affineIndependent_of_card_dimension (zeroNeighbors V) 3 hfour (hsection ▸ hdimSection)
  exact hWi

/-- A four-dimensional geometric polytope with exactly four neighbors at
its zero vertex has the actual simplex face lattice required in `lem:simple`.
The section and its face correspondence are proved geometric constructions. -/
noncomputable def zeroSimpleVertexFaceLattice [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hedge : ∀ x, IsEdge V 0 x → L x = 1)
    (hdim : affineDimension (convexHull ℝ (V : Set E)) = 4)
    (hfour : (zeroNeighbors V).card = 4) :
    VertexFigureSimplexFaceLattice (apexNeighborsIn V) := by
  have hsection : heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ (zeroNeighbors V : Set E) := by
    rw [coe_zeroNeighbors]
    exact finiteHull_section_eq_convexHull_edges V hzero hvertices L hheight hedge
  have hWi := zeroSimpleVertex_neighbors_affineIndependent V hzero hvertices L hheight
    hedge hdim hfour
  let e : GeometricFace (heightSection (convexHull ℝ (V : Set E)) L) ≃o
      Finset (zeroNeighbors V) := (geometricFace_congr hsection).trans
        (simplexFaceEquiv (zeroNeighbors V) hWi)
  refine ⟨(apexFaceSectionEquiv V hzero L hheight).trans e, ?_⟩
  intro F
  have he (G : GeometricFace (heightSection (convexHull ℝ (V : Set E)) L))
      (x : zeroNeighbors V) : x ∈ e G ↔ (x : E) ∈ G.val := by
    exact mem_simplexVerticesIn _ _ _
  ext x
  rw [OrderIso.trans_apply, he, apexFaceSectionEquiv_apply, mem_apexNeighborsIn]
  change ((x : E) ∈ F.val.val ∧ (x : E) ∈ heightSection (convexHull ℝ (V : Set E)) L) ↔ _
  have hxedge := (mem_zeroNeighbors V (x : E)).mp x.property
  exact ⟨fun h => h.1, fun h => ⟨h, subset_convexHull ℝ _ hxedge.2.1, hedge _ hxedge⟩⟩

/-- The dimension of a nonempty actual simplex face is one less than its
number of incident vertices. -/
theorem simplexFace_dimension [FiniteDimensional ℝ E] (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E))
    (F : GeometricFace (convexHull ℝ (V : Set E))) (hne : F.val.Nonempty) :
    affineDimension F.val + 1 = (simplexVerticesIn V F).card := by
  let T := simplexVerticesIn V F
  have hFhull : F.val = convexHull ℝ (T.image (fun x : V => (x : E)) : Set E) :=
    (congrArg Subtype.val ((simplexFaceEquiv V hV).left_inv F)).symm
  have hTne : T.Nonempty := by
    have hh : (T.image (fun x : V => (x : E)) : Set E).Nonempty :=
      (convexHull_nonempty_iff (𝕜 := ℝ)).mp (hFhull ▸ hne)
    exact Finset.image_nonempty.mp hh
  have hcard : T.card = (T.card - 1) + 1 := by have := hTne.card_pos; omega
  have hd := hV.finrank_vectorSpan_image_finset hcard
  change Module.finrank ℝ (vectorSpan ℝ (T.image (fun x : V => (x : E)) : Set E)) = T.card - 1 at hd
  rw [hFhull, affineDimension, Uniform5.affineDimension, affineSpan_convexHull (𝕜 := ℝ), direction_affineSpan]
  change Module.finrank ℝ (vectorSpan ℝ (T.image (fun x : V => (x : E)) : Set E)) + 1 = T.card
  omega

/-- At a simple four-dimensional vertex, each apex face's dimension is
exactly the number of incident edges in that face. -/
theorem zeroSimpleVertex_face_dimension [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hedge : ∀ x, IsEdge V 0 x → L x = 1)
    (hdim : affineDimension (convexHull ℝ (V : Set E)) = 4)
    (hfour : (zeroNeighbors V).card = 4)
    (F : {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val}) :
    affineDimension F.val.val = (apexNeighborsIn V F).card := by
  by_cases hF0 : F.val.val = {0}
  · have hinc : apexNeighborsIn V F = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      have hx0 : (x : E) = 0 := by
        simpa [hF0] using (mem_apexNeighborsIn V F x).mp hx
      have he := (mem_zeroNeighbors V (x : E)).mp x.property
      exact he.2.2.1 hx0.symm
    rw [hF0, affineDimension_singleton, hinc, Finset.card_empty]
  have hsection : heightSection (convexHull ℝ (V : Set E)) L =
      convexHull ℝ (zeroNeighbors V : Set E) := by
    rw [coe_zeroNeighbors]
    exact finiteHull_section_eq_convexHull_edges V hzero hvertices L hheight hedge
  have hWi := zeroSimpleVertex_neighbors_affineIndependent V hzero hvertices L hheight
    hedge hdim hfour
  let G := geometricFace_congr hsection (apexFaceSectionEquiv V hzero L hheight F)
  have hGne : G.val.Nonempty :=
    (apexFace_section_nonempty_iff V L hheight F.val.property F.property).mpr hF0
  have hinc : simplexVerticesIn (zeroNeighbors V) G = apexNeighborsIn V F := by
    ext x
    rw [mem_simplexVerticesIn, mem_apexNeighborsIn]
    change ((x : E) ∈ F.val.val ∧ (x : E) ∈ heightSection (convexHull ℝ (V : Set E)) L) ↔ _
    have he := (mem_zeroNeighbors V (x : E)).mp x.property
    exact ⟨fun h => h.1, fun h => ⟨h, subset_convexHull ℝ _ he.2.1, hedge _ he⟩⟩
  have hdG := simplexFace_dimension (zeroNeighbors V) hWi G hGne
  have hdF := apexFace_section_dimension V hzero L hheight F.val.property F.property hF0
  exact hdF.symm.trans (hdG.trans (congrArg Finset.card hinc))

/-- Paper `lem:simple`: an actual facet through a degree-four vertex has
exactly three of its four incident edges, with all geometry discharged. -/
theorem zeroSimpleVertex_facet_iff_three [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hedge : ∀ x, IsEdge V 0 x → L x = 1)
    (hdim : affineDimension (convexHull ℝ (V : Set E)) = 4)
    (hfour : (zeroNeighbors V).card = 4)
    (F : {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val}) :
    Facet (convexHull ℝ (V : Set E)) F.val.val ↔ (apexNeighborsIn V F).card = 3 := by
  have hdF := zeroSimpleVertex_face_dimension V hzero hvertices L hheight hedge hdim hfour F
  constructor
  · intro hf
    have hr := hf.2.2
    omega
  · intro hc
    refine ⟨F.val.property, ⟨0, F.property⟩, ?_⟩
    omega

/-- Paper `lem:simple`: every three incident edges determine exactly one
actual facet through the simple vertex. -/
theorem zeroSimpleVertex_unique_facet [FiniteDimensional ℝ E]
    (V : Finset E) (hzero : 0 ∈ V)
    (hvertices : ∀ x ∈ V, x ∈ (convexHull ℝ (V : Set E)).extremePoints ℝ)
    (L : E →L[ℝ] ℝ) (hheight : ∀ x ∈ V.erase 0, 1 ≤ L x)
    (hedge : ∀ x, IsEdge V 0 x → L x = 1)
    (hdim : affineDimension (convexHull ℝ (V : Set E)) = 4)
    (hfour : (zeroNeighbors V).card = 4) (s : Finset (zeroNeighbors V)) (hthree : s.card = 3) :
    ∃! F : {F : GeometricFace (convexHull ℝ (V : Set E)) // (0 : E) ∈ F.val},
      Facet (convexHull ℝ (V : Set E)) F.val.val ∧ apexNeighborsIn V F = s := by
  let hl := zeroSimpleVertexFaceLattice V hzero hvertices L hheight hedge hdim hfour
  have hi : apexNeighborsIn V (hl.faceEquiv.symm s) = s := by
    rw [← hl.incidence, hl.faceEquiv.apply_symm_apply]
  refine ⟨hl.faceEquiv.symm s, ⟨?_, hi⟩, ?_⟩
  · apply (zeroSimpleVertex_facet_iff_three V hzero hvertices L hheight hedge hdim hfour _).mpr
    rw [hi, hthree]
  · intro F hF
    apply hl.faceEquiv.injective
    rw [hl.incidence, hF.2, hl.faceEquiv.apply_symm_apply]

/-- Sphere geometry and unit edges discharge the section-height conditions
used by the actual simple-vertex construction. -/
theorem cosphericalUnit_simpleVertex_heights (V : Finset E) (hzero : 0 ∈ V)
    (c : E) (R : ℝ) (hsphere : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : ∀ x y, IsEdge V x y → dist x y = 1) :
    (∀ x ∈ V.erase 0, 1 ≤ sphereHeight c x) ∧
      (∀ x, IsEdge V 0 x → sphereHeight c x = 1) := by
  have hc : ‖c‖ ^ 2 = R ^ 2 := by simpa using hsphere 0 hzero
  have hheight (x : E) (hx : x ∈ V) : sphereHeight c x = ‖x‖ ^ 2 :=
    sphereHeight_eq_norm_sq ((hsphere x hx).trans hc.symm)
  constructor
  · intro x hx
    rw [hheight x (Finset.mem_erase.mp hx).2]
    have hsep := unit_edges_separated V hsphere hunit hzero (Finset.mem_erase.mp hx).2
      (Finset.mem_erase.mp hx).1.symm
    simp only [dist_zero_left] at hsep
    nlinarith
  · intro x hx
    rw [hheight x hx.2.1]
    have hlen := hunit 0 x hx
    simp only [dist_zero_left] at hlen
    rw [hlen]
    norm_num

/-- Actual unit-uniform four-polytopes supply the previously assumed
simplex face lattice at a degree-four zero vertex. There is no additional
sphere, section, exposed-face, or combinatorial premise. -/
noncomputable def unitUniform4_zeroSimpleVertexFaceLattice [FiniteDimensional ℝ E]
    {P : Set E} (hP : UnitUniform 4 P) (hzero : (0 : E) ∈ P.extremePoints ℝ)
    (hfour : (zeroNeighbors (vertices P (uniform_finitePolytope hP.1))).card = 4) :
    VertexFigureSimplexFaceLattice
      (apexNeighborsIn (vertices P (uniform_finitePolytope hP.1))) := by
  apply Classical.choice
  obtain ⟨c, R, _, hs⟩ := uniform_cospherical_pos hP.1
  let V := vertices P (uniform_finitePolytope hP.1)
  have hVzero : (0 : E) ∈ V := (mem_vertices _ 0).mpr hzero
  have hVs : ∀ x ∈ V, ‖x - c‖ ^ 2 = R ^ 2 :=
    fun x hx => hs x ((mem_vertices _ x).mp hx)
  have hVu : ∀ x y, IsEdge V x y → dist x y = 1 :=
    fun x y hxy => hP.2 x y ((edge_iff_vertices_isEdge _ x y).mpr hxy)
  have hh := cosphericalUnit_simpleVertex_heights V hVzero c R hVs hVu
  exact ⟨zeroSimpleVertexFaceLattice V hVzero
    (fun x hx => by simpa only [V, convexHull_vertices] using (mem_vertices _ x).mp hx)
    (sphereHeight c) hh.1 hh.2
    (by simpa only [V, convexHull_vertices] using uniform_dimension hP.1) hfour⟩

/-- Paper `lem:simple` as an actual facet statement for unit-uniform
four-polytopes with a degree-four zero vertex. -/
theorem unitUniform4_zeroSimpleVertex_facet_iff_three [FiniteDimensional ℝ E]
    {P : Set E} (hP : UnitUniform 4 P) (hzero : (0 : E) ∈ P.extremePoints ℝ)
    (hfour : (zeroNeighbors (vertices P (uniform_finitePolytope hP.1))).card = 4)
    (F : {F : GeometricFace (convexHull ℝ
      (vertices P (uniform_finitePolytope hP.1) : Set E)) // (0 : E) ∈ F.val}) :
    Facet P F.val.val ↔
      (apexNeighborsIn (vertices P (uniform_finitePolytope hP.1)) F).card = 3 := by
  obtain ⟨c, R, _, hs⟩ := uniform_cospherical_pos hP.1
  let V := vertices P (uniform_finitePolytope hP.1)
  have hVzero : (0 : E) ∈ V := (mem_vertices _ 0).mpr hzero
  have hh := cosphericalUnit_simpleVertex_heights V hVzero c R
    (fun x hx => hs x ((mem_vertices _ x).mp hx))
    (fun x y hxy => hP.2 x y ((edge_iff_vertices_isEdge _ x y).mpr hxy))
  have hf := zeroSimpleVertex_facet_iff_three V hVzero
    (fun x hx => by simpa only [V, convexHull_vertices] using (mem_vertices _ x).mp hx)
    (sphereHeight c) hh.1 hh.2
    (by simpa only [V, convexHull_vertices] using uniform_dimension hP.1) hfour F
  simpa only [V, convexHull_vertices] using hf

end Uniform5.Composition
