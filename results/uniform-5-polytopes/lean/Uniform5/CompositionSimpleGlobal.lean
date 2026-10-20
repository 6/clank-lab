import Uniform5.CompositionSimpleVertex
import Uniform5.CompositionEdgeFaces
import Uniform5.CaseBCases

/-!
# Actual simple-vertex incidence at arbitrary vertices
-/

noncomputable section
namespace Uniform5.Composition
open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual finite neighbors of a vertex, with points as labels. -/
noncomputable def geometricNeighbours (P : Set E) (hP : FinitePolytope P) (v : E) : Finset E :=
  (vertices P hP).filter (fun w => Edge P v w)

@[simp] theorem mem_geometricNeighbours (P : Set E) (hP : FinitePolytope P) (v w : E) :
    w ∈ geometricNeighbours P hP v ↔ Edge P v w := by
  simp only [geometricNeighbours, Finset.mem_filter, mem_vertices]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩

/-- Finite sets of geometric neighbors transport under ambient isometries. -/
theorem geometricNeighbours_image (g : E ≃ᵃⁱ[ℝ] E) {P : Set E}
    (hP : FinitePolytope P) (v : E) :
    geometricNeighbours (g '' P) (finitePolytope_image g hP) (g v) =
      (geometricNeighbours P hP v).image g := by
  ext x
  simp only [mem_geometricNeighbours, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
    apply (edge_image_iff g P v (g.symm x)).mp
    simpa using hx
  · rintro ⟨y, hy, rfl⟩
    exact edge_image g hy

/-- The actual neighbor set at zero agrees with the finite-hull construction. -/
theorem geometricNeighbours_zero {P : Set E} (hP : FinitePolytope P) :
    geometricNeighbours P hP 0 = zeroNeighbors (vertices P hP) := by
  ext x
  rw [mem_geometricNeighbours, mem_zeroNeighbors, edge_iff_vertices_isEdge]

/-- Actual faces containing a distinguished geometric vertex. -/
noncomputable def FacesAt (P : Set E) (v : E) := {F : GeometricFace P // v ∈ F.val}

noncomputable instance (P : Set E) (v : E) : PartialOrder (FacesAt P v) :=
  inferInstanceAs (PartialOrder {F : GeometricFace P // v ∈ F.val})

/-- The neighbor incidence of an actual face through a vertex. -/
noncomputable def neighboursIn (P : Set E) (hP : FinitePolytope P) (v : E)
    (F : FacesAt P v) : Finset (geometricNeighbours P hP v) :=
  Finset.univ.filter (fun w : geometricNeighbours P hP v => (w : E) ∈ F.val.val)

@[simp] theorem mem_neighboursIn (P : Set E) (hP : FinitePolytope P) (v : E)
    (F : FacesAt P v) (w : geometricNeighbours P hP v) :
    w ∈ neighboursIn P hP v F ↔ (w : E) ∈ F.val.val := by simp [neighboursIn]

/-- Actual apex-face posets transport under ambient isometries. -/
noncomputable def facesAtImageEquiv (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) (v : E) :
    FacesAt P v ≃o FacesAt (g '' P) (g v) where
  toFun F := ⟨⟨g '' F.val.val, isConvexFace_image g F.val.property⟩,
    mem_image_of_mem g F.property⟩
  invFun G := ⟨⟨g.symm '' G.val.val, by
    simpa using isConvexFace_image g.symm G.val.property⟩, by
    simpa using mem_image_of_mem g.symm G.property⟩
  left_inv F := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv G := by apply Subtype.ext; apply Subtype.ext; simp
  map_rel_iff' := by
    intro F G
    change g '' F.val.val ⊆ g '' G.val.val ↔ F.val.val ⊆ G.val.val
    constructor
    · intro h x hx
      obtain ⟨y, hy, hxy⟩ := h (mem_image_of_mem g hx)
      exact g.injective hxy ▸ hy
    · exact Set.image_mono

/-- Equality of the ambient hull and apex transports their face posets. -/
noncomputable def facesAtCongr {P Q : Set E} {v w : E} (hP : P = Q) (hv : v = w) :
    FacesAt P v ≃o FacesAt Q w where
  toFun F := ⟨⟨F.val.val, hP ▸ F.val.property⟩, hv ▸ F.property⟩
  invFun F := ⟨⟨F.val.val, hP.symm ▸ F.val.property⟩, hv.symm ▸ F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

/-- Neighbor labels after sending the distinguished vertex to zero. -/
noncomputable def zeroNeighbourImageEquiv (g : E ≃ᵃⁱ[ℝ] E) (P : Set E)
    (hP : FinitePolytope P) (v : E) (hgv : g v = 0) :
    zeroNeighbors (vertices (g '' P) (finitePolytope_image g hP)) ≃ geometricNeighbours P hP v where
  toFun x := ⟨g.symm x, by
    rw [mem_geometricNeighbours]
    apply (edge_image_iff g P v (g.symm x)).mp
    have he := (edge_iff_vertices_isEdge (finitePolytope_image g hP) 0 (x : E)).mpr
      ((mem_zeroNeighbors _ _).mp x.property)
    simpa only [hgv, g.apply_symm_apply] using he⟩
  invFun y := ⟨g y, by
    rw [mem_zeroNeighbors]
    apply (edge_iff_vertices_isEdge (finitePolytope_image g hP) 0 (g y)).mp
    have he := edge_image g ((mem_geometricNeighbours P hP v (y : E)).mp y.property)
    simpa only [hgv] using he⟩
  left_inv x := by apply Subtype.ext; exact g.apply_symm_apply x
  right_inv y := by apply Subtype.ext; exact g.symm_apply_apply y

/-- Relabeling finite vertex subsets gives an inclusion order isomorphism. -/
noncomputable def finsetLabelEquiv {A B : Type*} (e : A ≃ B) : Finset A ≃o Finset B where
  toEquiv := e.finsetCongr
  map_rel_iff' := Finset.map_subset_map

/-- Transport actual faces to the canonical finite hull at the zero apex. -/
noncomputable def zeroFacesImageEquiv (g : E ≃ᵃⁱ[ℝ] E) (P : Set E)
    (hP : FinitePolytope P) (v : E) (hgv : g v = 0) :
    FacesAt P v ≃o FacesAt (convexHull ℝ
      (vertices (g '' P) (finitePolytope_image g hP) : Set E)) 0 :=
  (facesAtImageEquiv g P v).trans
    (facesAtCongr (convexHull_vertices (finitePolytope_image g hP)).symm hgv)

/-- Transport preserves the literal incident-neighbor finite sets. -/
theorem zeroNeighbourImage_incidence (g : E ≃ᵃⁱ[ℝ] E) (P : Set E)
    (hP : FinitePolytope P) (v : E) (hgv : g v = 0) (F : FacesAt P v) :
    (apexNeighborsIn (vertices (g '' P) (finitePolytope_image g hP))
      (zeroFacesImageEquiv g P hP v hgv F)).map
        (zeroNeighbourImageEquiv g P hP v hgv).toEmbedding = neighboursIn P hP v F := by
  ext x
  rw [Finset.mem_map, mem_neighboursIn]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [mem_apexNeighborsIn] at hy
    change (y : E) ∈ g '' F.val.val at hy
    obtain ⟨z, hzF, hzy⟩ := hy
    have hcoe : g.symm (y : E) = (x : E) := congrArg Subtype.val hyx
    have hxz : (x : E) = z := by rw [← hcoe, ← hzy, g.symm_apply_apply]
    exact hxz.symm ▸ hzF
  · intro hxF
    refine ⟨(zeroNeighbourImageEquiv g P hP v hgv).symm x, ?_,
      (zeroNeighbourImageEquiv g P hP v hgv).apply_symm_apply x⟩
    rw [mem_apexNeighborsIn]
    exact mem_image_of_mem g hxF

/-- The genuine simplex face lattice at any degree-four vertex of a
unit-uniform four-polytope. Translation removes the origin restriction. -/
noncomputable def unitUniform4_simpleVertexFaceLattice [FiniteDimensional ℝ E]
    {P : Set E} (hP : UnitUniform 4 P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (hfour : (geometricNeighbours P (uniform_finitePolytope hP.1) v).card = 4) :
    VertexFigureSimplexFaceLattice
      (neighboursIn P (uniform_finitePolytope hP.1) v) := by
  let g := AffineIsometryEquiv.constVAdd ℝ E (-v)
  have hgv : g v = 0 := by simp [g]
  let hQ := unitUniform_image g hP
  have hz : (0 : E) ∈ (g '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints, ← hgv]
    exact mem_image_of_mem g hv
  let V := vertices (g '' P) (uniform_finitePolytope hQ.1)
  let eN := zeroNeighbourImageEquiv g P (uniform_finitePolytope hP.1) v hgv
  have hfourQ : (zeroNeighbors V).card = 4 := by
    have hc := Fintype.card_congr eN
    simp only [Fintype.card_coe] at hc
    exact hc.trans hfour
  let hl := unitUniform4_zeroSimpleVertexFaceLattice hQ hz hfourQ
  let eF : FacesAt P v ≃o FacesAt (convexHull ℝ (V : Set E)) 0 :=
    (facesAtImageEquiv g P v).trans (facesAtCongr (convexHull_vertices (uniform_finitePolytope hQ.1)).symm hgv)
  refine ⟨(eF.trans hl.faceEquiv).trans (finsetLabelEquiv eN), ?_⟩
  intro F
  ext x
  change x ∈ (hl.faceEquiv (eF F)).map eN.toEmbedding ↔
    x ∈ neighboursIn P (uniform_finitePolytope hP.1) v F
  rw [Finset.mem_map, mem_neighboursIn]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [hl.incidence, mem_apexNeighborsIn] at hy
    change (y : E) ∈ g '' F.val.val at hy
    obtain ⟨z, hzF, hzy⟩ := hy
    have hcoe : g.symm (y : E) = (x : E) := congrArg Subtype.val hyx
    have hxz : (x : E) = z := by rw [← hcoe, ← hzy, g.symm_apply_apply]
    exact hxz.symm ▸ hzF
  · intro hxF
    refine ⟨eN.symm x, ?_, eN.apply_symm_apply x⟩
    rw [hl.incidence, mem_apexNeighborsIn]
    exact mem_image_of_mem g hxF

/-- An actual facet at any degree-four vertex has exactly three incident
edges, without an origin or assumed face-lattice premise. -/
theorem unitUniform4_simpleVertex_facet_iff_three [FiniteDimensional ℝ E]
    {P : Set E} (hP : UnitUniform 4 P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (hfour : (geometricNeighbours P (uniform_finitePolytope hP.1) v).card = 4)
    (F : FacesAt P v) :
    Facet P F.val.val ↔ (neighboursIn P (uniform_finitePolytope hP.1) v F).card = 3 := by
  let g := AffineIsometryEquiv.constVAdd ℝ E (-v)
  have hgv : g v = 0 := by simp [g]
  let hQ := unitUniform_image g hP
  have hz : (0 : E) ∈ (g '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints, ← hgv]
    exact mem_image_of_mem g hv
  let V := vertices (g '' P) (uniform_finitePolytope hQ.1)
  let eN := zeroNeighbourImageEquiv g P (uniform_finitePolytope hP.1) v hgv
  have hfourQ : (zeroNeighbors V).card = 4 := by
    have hc := Fintype.card_congr eN
    simp only [Fintype.card_coe] at hc
    exact hc.trans hfour
  let G := zeroFacesImageEquiv g P (uniform_finitePolytope hP.1) v hgv F
  have hf := unitUniform4_zeroSimpleVertex_facet_iff_three hQ hz hfourQ G
  have hi := congrArg Finset.card
    (zeroNeighbourImage_incidence g P (uniform_finitePolytope hP.1) v hgv F)
  rw [Finset.card_map] at hi
  rw [hi] at hf
  exact (facet_image_iff g P F.val.val).symm.trans hf

/-- Every three incident edges at an arbitrary simple vertex determine
exactly one actual facet through that vertex. -/
theorem unitUniform4_simpleVertex_unique_facet [FiniteDimensional ℝ E]
    {P : Set E} (hP : UnitUniform 4 P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (hfour : (geometricNeighbours P (uniform_finitePolytope hP.1) v).card = 4)
    (s : Finset (geometricNeighbours P (uniform_finitePolytope hP.1) v)) (hthree : s.card = 3) :
    ∃! F : FacesAt P v, Facet P F.val.val ∧ neighboursIn P (uniform_finitePolytope hP.1) v F = s := by
  let hl := unitUniform4_simpleVertexFaceLattice hP hv hfour
  have hi : neighboursIn P (uniform_finitePolytope hP.1) v (hl.faceEquiv.symm s) = s := by
    rw [← hl.incidence, hl.faceEquiv.apply_symm_apply]
  refine ⟨hl.faceEquiv.symm s, ⟨?_, hi⟩, ?_⟩
  · apply (unitUniform4_simpleVertex_facet_iff_three hP hv hfour _).mpr
    rw [hi, hthree]
  · intro F hF
    apply hl.faceEquiv.injective
    rw [hl.incidence, hF.2, hl.faceEquiv.apply_symm_apply]

end Uniform5.Composition
