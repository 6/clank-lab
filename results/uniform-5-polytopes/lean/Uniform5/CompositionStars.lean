import Uniform5.CompositionEdgeFaces
import Uniform5.CompositionGraph
import Uniform5.Propagation

/-!
# The actual geometric instance of local-to-global propagation

A star is exactly the set of incident facets, each an actual subset of
Euclidean space. Facet containment and edge inheritance prove that this
star determines the neighbors. The local-forcing premise below is still
to be derived from the exact interpretation of LU in the classification.
-/
noncomputable section
namespace Uniform5.Composition
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The paper's full geometric star, consisting of actual incident facets. -/
noncomputable def facetStar (P : Set E) (v : E) : Set (Set E) :=
  {F | Facet P F ∧ v ∈ F}

/-- Equality of actual facet stars forces exactly the same edge neighbors. -/
theorem facetStar_determines_edges [FiniteDimensional ℝ E] {P Q : Set E}
    (hP : FinitePolytope P) (hQ : FinitePolytope Q)
    (hdP : 1 < affineDimension P) (hdQ : 1 < affineDimension Q)
    {v : E} (hs : facetStar P v = facetStar Q v) (w : E) :
    Edge P v w ↔ Edge Q v w := by
  have forward {A B : Set E} (hA : FinitePolytope A) (hB : FinitePolytope B)
      (hdA : 1 < affineDimension A) (heq : facetStar A v = facetStar B v)
      (he : Edge A v w) : Edge B v w := by
    obtain ⟨F, hF, hvF, hwF⟩ := edge_mem_facet hA he hdA
    have hFB : Facet B F := (show F ∈ facetStar B v by rw [← heq]; exact ⟨hF, hvF⟩).1
    exact (edge_face_iff hB hFB.1 hvF hwF).mpr
      ((edge_face_iff hA hF.1 hvF hwF).mp he)
  exact ⟨forward hP hQ hdP hs, forward hQ hP hdQ hs.symm⟩

/-- Coordinate change on sets of actual facets. -/
noncomputable def facetSetImage (g : E ≃ᵃⁱ[ℝ] E) (S : Set (Set E)) : Set (Set E) :=
  (fun F => g '' F) '' S

@[simp] theorem facetSetImage_symm_image (g : E ≃ᵃⁱ[ℝ] E) (S : Set (Set E)) :
    facetSetImage g.symm (facetSetImage g S) = S := by
  ext F
  simp [facetSetImage]

noncomputable def facetSetImageEquiv (g : E ≃ᵃⁱ[ℝ] E) : Set (Set E) ≃ Set (Set E) where
  toFun := facetSetImage g
  invFun := facetSetImage g.symm
  left_inv := facetSetImage_symm_image g
  right_inv S := by simpa using facetSetImage_symm_image g.symm S

theorem facetStar_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) (v : E) :
    facetStar (g '' P) (g v) = facetSetImage g (facetStar P v) := by
  ext F
  constructor
  · rintro ⟨hF, hvF⟩
    refine ⟨g.symm '' F, ⟨?_, ?_⟩, affineIsometry_image_symm_image g F⟩
    · have hh := facet_image g.symm hF
      simpa only [affineIsometry_symm_image_image] using hh
    · exact ⟨g v, hvF, g.symm_apply_apply v⟩
  · rintro ⟨G, ⟨hG, hvG⟩, rfl⟩
    exact ⟨facet_image g hG, mem_image_of_mem g hvG⟩

/-- Actual unit-uniform five-polytopes instantiate the previously abstract
propagation system, including its connectedness and extensionality laws. -/
noncomputable def geometricStarSystem :
    StarSystem (Space 5) (Set (Set (Space 5))) UnitUniform5 where
  vertices P := P.val.extremePoints ℝ
  finite_vertices P := finitePolytope_extremePoints_finite (uniform_finitePolytope P.property.1)
  star P := facetStar P.val
  adjacent P := Edge P.val
  adjacent_mem h := ⟨h.1, h.2.1⟩
  neighbours {P Q x} _ _ hs w := facetStar_determines_edges
    (uniform_finitePolytope P.property.1) (uniform_finitePolytope Q.property.1)
    (by rw [uniform_dimension P.property.1]; norm_num)
    (by rw [uniform_dimension Q.property.1]; norm_num) hs w
  connected {P x y} hv hw := P.edge_connected hv hw
  ext := UnitUniform5.ext_vertices

/-- Every ambient affine isometry supplies the exact coordinate transport
required by the propagation theorem. -/
noncomputable def geometricStarTransport (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) :
    StarTransport geometricStarSystem where
  point := g.toEquiv
  stars := facetSetImageEquiv g
  model := UnitUniform5.imageEquiv g
  vertices P x := UnitUniform5.image_mem_vertices g P x
  star P x := facetStar_image g P.val x
  adjacent P x y := edge_image_iff g P.val x y

theorem geometricStarSystem_transitive (r : Space 5) (P : UnitUniform5)
    (hr : r ∈ geometricStarSystem.vertices P) (x : Space 5)
    (hx : x ∈ geometricStarSystem.vertices P) :
    ∃ t : StarTransport geometricStarSystem, t.model P = P ∧ t.point r = x := by
  obtain ⟨g, hg, hgr⟩ := uniform_vertexTransitive P.property.1 r hr x hx
  exact ⟨geometricStarTransport g, UnitUniform5.ext hg, hgr⟩

/-- Paper `lem:induction` for actual geometric polytopes. The only remaining
premise is the lemma's local forcing at the fixed root and fixed facet star;
graph, transport, finiteness and vertex-hull extensionality are proved. -/
theorem geometric_local_uniqueness_global
    (r : Space 5) (S : Set (Set (Space 5)))
    (forcing : ∀ A B : UnitUniform5, r ∈ A.val.extremePoints ℝ →
      r ∈ B.val.extremePoints ℝ → facetStar A.val r = S → facetStar B.val r = S →
      ∀ y, Edge A.val r y → facetStar A.val y = facetStar B.val y)
    {A B : UnitUniform5} (hrA : r ∈ A.val.extremePoints ℝ)
    (hrB : r ∈ B.val.extremePoints ℝ)
    (hsA : facetStar A.val r = S) (hsB : facetStar B.val r = S) : A = B :=
  geometricStarSystem.local_uniqueness_global r S
    (geometricStarSystem_transitive r) forcing hrA hrB hsA hsB

end Uniform5.Composition
