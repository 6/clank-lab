import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Uniform5.Faces
import Uniform5.Sphere
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Local uniqueness propagates through a connected vertex graph

The first part is the abstract combinatorial and transport core of paper
Lemma `lem:induction`. The second part constructs a finite Euclidean model in
dimension five, with genuine maximal proper convex faces and their full
vertex-set stars. Ambient affine isometries preserve the model and its stars;
edge containment in facets and neighbour determination are proved.

The concrete local forcing step, inclusion and global results have no
connectivity premise: actual exposed-edge connectivity follows from finite
vertex transitivity via the centroid sphere and a closest-pair cut argument.
The model records uniformity by vertex transitivity on every convex face.
For finite-hull faces this is proved equivalent to facet-recursive vertex
transitivity, and `ofRecursive` constructs the model from that recursion.
The exact regular-polygon base and the restricted paper-class propagation
are constructed in `EuclideanPropagation`. No classification-specific local
forcing is established.
-/

namespace Uniform5

/-- Finite vertex models, with stars determining the neighbours of a vertex.
`ext` expresses that a model is determined by its vertex set, as for convex
hulls. No equality of stars away from a shared vertex is required. -/
structure StarSystem (V S M : Type*) where
  vertices : M → Set V
  finite_vertices : ∀ P, (vertices P).Finite
  star : M → V → S
  adjacent : M → V → V → Prop
  adjacent_mem : ∀ {P x y}, adjacent P x y → x ∈ vertices P ∧ y ∈ vertices P
  neighbours : ∀ {P Q x}, x ∈ vertices P → x ∈ vertices Q →
    star P x = star Q x → ∀ y, adjacent P x y ↔ adjacent Q x y
  connected : ∀ {P x y}, x ∈ vertices P → y ∈ vertices P →
    Relation.ReflTransGen (adjacent P) x y
  ext : ∀ {P Q}, vertices P = vertices Q → P = Q

/-- An invertible change of coordinates, including its action on models and
stars. Its action on models is not assumed to fix both models. -/
structure StarTransport {V S M : Type*} (D : StarSystem V S M) where
  point : V ≃ V
  stars : S ≃ S
  model : M ≃ M
  vertices : ∀ P x, point x ∈ D.vertices (model P) ↔ x ∈ D.vertices P
  star : ∀ P x, D.star (model P) (point x) = stars (D.star P x)
  adjacent : ∀ P x y, D.adjacent (model P) (point x) (point y) ↔ D.adjacent P x y

namespace StarSystem

variable {V S M : Type*} (D : StarSystem V S M)

/-- Local forcing at one root transfers to a shared star at any vertex, using
an automorphism of the first model and transporting the second model back.
This is the step where the paper must not presume a common symmetry. -/
theorem local_forcing_step
    (r : V) (s : S)
    (transitive : ∀ P, r ∈ D.vertices P → ∀ x ∈ D.vertices P,
      ∃ t : StarTransport D, t.model P = P ∧ t.point r = x)
    (forcing : ∀ A B, r ∈ D.vertices A → r ∈ D.vertices B →
      D.star A r = s → D.star B r = s →
      ∀ y, D.adjacent A r y → D.star A y = D.star B y)
    {A B : M} (hrA : r ∈ D.vertices A) (hsA : D.star A r = s)
    {x y : V} (hxA : x ∈ D.vertices A) (hxB : x ∈ D.vertices B)
    (hx : D.star A x = D.star B x) (hxy : D.adjacent A x y) :
    y ∈ D.vertices B ∧ D.star A y = D.star B y := by
  obtain ⟨t, htA, htr⟩ := transitive A hrA x hxA
  let B' := t.model.symm B
  have htB : t.model B' = B := t.model.apply_symm_apply B
  have hrB' : r ∈ D.vertices B' := by
    apply (t.vertices B' r).mp
    simpa only [htB, htr] using hxB
  have hsB' : D.star B' r = s := by
    rw [← hsA]
    apply t.stars.injective
    rw [← t.star B' r, ← t.star A r, htB, htA, htr]
    exact hx.symm
  let y' := t.point.symm y
  have hty : t.point y' = y := t.point.apply_symm_apply y
  have hary : D.adjacent A r y' := by
    apply (t.adjacent A r y').mp
    simpa only [htA, htr, hty] using hxy
  have hyStar := forcing A B' hrA hrB' hsA hsB' y' hary
  have hy : D.star A y = D.star B y := by
    have h := congrArg t.stars hyStar
    rw [← t.star A y', ← t.star B' y', htA, htB, hty] at h
    exact h
  exact ⟨(D.adjacent_mem ((D.neighbours hxA hxB hx y).mp hxy)).2, hy⟩

/-- Connectedness propagates the root equality to every vertex of the first
model. -/
theorem local_forcing_inclusion
    (r : V) (s : S)
    (transitive : ∀ P, r ∈ D.vertices P → ∀ x ∈ D.vertices P,
      ∃ t : StarTransport D, t.model P = P ∧ t.point r = x)
    (forcing : ∀ A B, r ∈ D.vertices A → r ∈ D.vertices B →
      D.star A r = s → D.star B r = s →
      ∀ y, D.adjacent A r y → D.star A y = D.star B y)
    {A B : M} (hrA : r ∈ D.vertices A) (hrB : r ∈ D.vertices B)
    (hsA : D.star A r = s) (hsB : D.star B r = s) :
    ∀ x ∈ D.vertices A, x ∈ D.vertices B ∧ D.star A x = D.star B x := by
  intro x hx
  have path := D.connected hrA hx
  induction path with
  | refl => exact ⟨hrB, hsA.trans hsB.symm⟩
  | @tail y z _ hyz ih =>
    have ih := ih (D.adjacent_mem hyz).1
    exact D.local_forcing_step r s transitive forcing hrA hsA
      (D.adjacent_mem hyz).1 ih.1 ih.2 hyz

/-- Paper Lemma `lem:induction`, conditional on a finite star model with
connected vertex graphs and the stated transport/vertex-transitivity data.
The forcing premise is only at the fixed root and fixed star `s`. -/
theorem local_uniqueness_global
    (r : V) (s : S)
    (transitive : ∀ P, r ∈ D.vertices P → ∀ x ∈ D.vertices P,
      ∃ t : StarTransport D, t.model P = P ∧ t.point r = x)
    (forcing : ∀ A B, r ∈ D.vertices A → r ∈ D.vertices B →
      D.star A r = s → D.star B r = s →
      ∀ y, D.adjacent A r y → D.star A y = D.star B y)
    {A B : M} (hrA : r ∈ D.vertices A) (hrB : r ∈ D.vertices B)
    (hsA : D.star A r = s) (hsB : D.star B r = s) : A = B := by
  apply D.ext
  apply Set.Subset.antisymm
  · intro x hx
    exact (D.local_forcing_inclusion r s transitive forcing hrA hrB hsA hsB x hx).1
  · intro x hx
    exact (D.local_forcing_inclusion r s transitive forcing hrB hrA hsB hsA x hx).1

end StarSystem
end Uniform5

namespace Uniform5
open Set

section EuclideanFaces
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A face of a finitely generated convex hull is the hull of the original
vertices it contains. This uses convex extremality, not transitivity of exposure. -/
theorem face_eq_convexHull_inter (V : Set E) {F : Set E}
    (hF : IsConvexFace (convexHull ℝ V) F) :
    convexHull ℝ (V ∩ F) = F := by
  apply Set.Subset.antisymm
  · exact convexHull_min inter_subset_right hF.1
  · have hconv : Convex ℝ {x | x ∈ convexHull ℝ V ∧
        (x ∈ F → x ∈ convexHull ℝ (V ∩ F))} := by
      intro x hx y hy a b ha hb hab
      refine ⟨(convex_convexHull ℝ V) hx.1 hy.1 ha hb hab, ?_⟩
      intro hxy
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy.2 (by simpa [ha0, hb1] using hxy)
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simpa [hb0, ha1] using hx.2 (by simpa [hb0, ha1] using hxy)
      have hends := hF.2.2 hx.1 hy.1 hxy
        ⟨a, b, lt_of_le_of_ne ha (Ne.symm ha0),
          lt_of_le_of_ne hb (Ne.symm hb0), hab, rfl⟩
      exact (convex_convexHull ℝ (V ∩ F)) (hx.2 hends.1) (hy.2 hends.2) ha hb hab
    have hmin := convexHull_min (t := {x | x ∈ convexHull ℝ V ∧
        (x ∈ F → x ∈ convexHull ℝ (V ∩ F))})
      (fun x hx => ⟨subset_convexHull ℝ V hx,
        fun hxF => subset_convexHull ℝ (V ∩ F) ⟨hx, hxF⟩⟩) hconv
    exact fun x hx => (hmin (hF.2.1 hx)).2 hx

/-- Genuine geometric facets: maximal nonempty proper convex faces. -/
def IsGeometricFacet (P F : Set E) : Prop :=
  IsConvexFace P F ∧ F.Nonempty ∧ F ≠ P ∧
    ∀ G, IsConvexFace P G → F ⊆ G → G ≠ P → G = F

/-- Stars record full facet vertex sets, rather than facet labels. -/
def facetStar (V : Set E) (x : E) : Set (Set E) :=
  {W | ∃ F, IsGeometricFacet (convexHull ℝ V) F ∧ W = V ∩ F ∧ x ∈ W}

/-- Adjacency is a nondegenerate convex one-face of the actual hull. -/
def GeometricEdge (V : Set E) (x y : E) : Prop :=
  x ∈ V ∧ y ∈ V ∧ x ≠ y ∧ IsConvexFace (convexHull ℝ V) (segment ℝ x y)

/-- The project's exposed edges are geometric convex one-faces. The concrete
model uses convex one-faces so restriction and face transitivity need no
finite-hull exposure bridge. -/
theorem isEdge_geometricEdge {V : Finset E} {x y : E} (h : IsEdge V x y) :
    GeometricEdge (V : Set E) x y :=
  ⟨h.1, h.2.1, h.2.2.1, convex_segment x y, h.2.2.2.isExtreme⟩

/-- Finite hulls have finitely many convex faces, proved by their vertex sets. -/
theorem finite_convexFaces {V : Set E} (hV : V.Finite) :
    {F | IsConvexFace (convexHull ℝ V) F}.Finite := by
  have himage : ((fun F : Set E => V ∩ F) ''
      {F | IsConvexFace (convexHull ℝ V) F}).Finite :=
    hV.powerset.subset (by rintro _ ⟨F, hF, rfl⟩; exact inter_subset_left)
  apply himage.of_finite_image
  intro F hF G hG heq
  change V ∩ F = V ∩ G at heq
  rw [← face_eq_convexHull_inter V hF, ← face_eq_convexHull_inter V hG, heq]

/-- A nonempty proper face of a finite hull lies in an actual facet. -/
theorem face_contained_in_facet {V F : Set E} (hV : V.Finite)
    (hF : IsConvexFace (convexHull ℝ V) F) (hne : F.Nonempty)
    (hproper : F ≠ convexHull ℝ V) :
    ∃ G, IsGeometricFacet (convexHull ℝ V) G ∧ F ⊆ G := by
  let candidates := {G | IsConvexFace (convexHull ℝ V) G ∧
    F ⊆ G ∧ G ≠ convexHull ℝ V}
  have hfin : candidates.Finite := (finite_convexFaces hV).subset (fun _ h => h.1)
  obtain ⟨G, hG, hmax⟩ := hfin.exists_maximal_wrt id candidates
    ⟨F, hF, Set.Subset.rfl, hproper⟩
  refine ⟨G, ⟨hG.1, hne.mono hG.2.1, hG.2.2, ?_⟩, hG.2.1⟩
  intro H hH hGH hHP
  exact (hmax H ⟨hH, hG.2.1.trans hGH, hHP⟩ hGH).symm

/-- Affine isometries preserve convex faces, with the actual image sets. -/
theorem convexFace_isometry_image (g : E ≃ᵃⁱ[ℝ] E) {P F : Set E}
    (hF : IsConvexFace P F) : IsConvexFace (g '' P) (g '' F) := by
  refine ⟨hF.1.affine_image g.toAffineEquiv.toAffineMap, ?_, ?_⟩
  · exact Set.image_mono hF.2.1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
    have hseg' : z ∈ openSegment ℝ a b := by
      have himg := (image_openSegment ℝ g.toAffineEquiv.toAffineMap a b).symm ▸ hseg
      obtain ⟨w, hw, heq⟩ := himg
      exact g.injective heq ▸ hw
    obtain ⟨haF, hbF⟩ := hF.2.2 ha hb hz hseg'
    exact ⟨Set.mem_image_of_mem g haF, Set.mem_image_of_mem g hbF⟩

/-- Pulling an image back by the inverse ambient isometry recovers the set. -/
@[simp] theorem isometry_symm_image_image (g : E ≃ᵃⁱ[ℝ] E) (S : Set E) :
    g.symm '' (g '' S) = S := by
  ext x
  simp

@[simp] theorem isometry_image_symm_image (g : E ≃ᵃⁱ[ℝ] E) (S : Set E) :
    g '' (g.symm '' S) = S := by
  ext x
  simp

/-- Facets, including their maximality among proper faces, are preserved. -/
theorem facet_isometry_image (g : E ≃ᵃⁱ[ℝ] E) {P F : Set E}
    (hF : IsGeometricFacet P F) : IsGeometricFacet (g '' P) (g '' F) := by
  refine ⟨convexFace_isometry_image g hF.1, hF.2.1.image g,
    fun heq => hF.2.2.1 (g.injective.image_injective heq), ?_⟩
  intro H hH hFH hHP
  have hback : IsConvexFace P (g.symm '' H) := by
    simpa using convexFace_isometry_image g.symm hH
  have hsub : F ⊆ g.symm '' H := by
    intro x hx
    exact ⟨g x, hFH (Set.mem_image_of_mem g hx), g.symm_apply_apply x⟩
  have hproper : g.symm '' H ≠ P := by
    intro heq
    apply hHP
    have := congrArg (fun S : Set E => g '' S) heq
    simpa using this
  have heq := hF.2.2.2 _ hback hsub hproper
  have := congrArg (fun S : Set E => g '' S) heq
  simpa using this

/-- An ambient affine isometry commutes with the actual convex hull. -/
theorem isometry_image_convexHull (g : E ≃ᵃⁱ[ℝ] E) (V : Set E) :
    g '' convexHull ℝ V = convexHull ℝ (g '' V) :=
  g.toAffineEquiv.toAffineMap.image_convexHull V

/-- Actual facet vertex sets and their incidence transform by ambient isometry. -/
theorem facetStar_isometry_image (g : E ≃ᵃⁱ[ℝ] E) (V : Set E) (x : E) :
    facetStar (g '' V) (g x) = (fun W : Set E => g '' W) '' facetStar V x := by
  apply Set.Subset.antisymm
  · rintro W ⟨F, hF, rfl, hx⟩
    have hback : IsGeometricFacet (convexHull ℝ V) (g.symm '' F) := by
      have h := facet_isometry_image g.symm hF
      rw [← isometry_image_convexHull g V] at h
      simpa using h
    refine ⟨V ∩ (g.symm '' F), ⟨g.symm '' F, hback, rfl, ?_⟩, ?_⟩
    · exact ⟨g.injective.mem_set_image.mp hx.1,
        ⟨g x, hx.2, g.symm_apply_apply x⟩⟩
    · change g '' (V ∩ (g.symm '' F)) = _
      rw [Set.image_inter g.injective, isometry_image_symm_image]
  · rintro _ ⟨W, ⟨F, hF, rfl, hx⟩, rfl⟩
    refine ⟨g '' F, ?_, Set.image_inter g.injective, ?_⟩
    · rw [← isometry_image_convexHull g V]
      exact facet_isometry_image g hF
    · exact Set.mem_image_of_mem g hx

/-- Ambient isometries preserve the geometric edge relation. -/
theorem geometricEdge_isometry_image (g : E ≃ᵃⁱ[ℝ] E) {V : Set E} {x y : E}
    (h : GeometricEdge V x y) : GeometricEdge (g '' V) (g x) (g y) := by
  refine ⟨Set.mem_image_of_mem g h.1, Set.mem_image_of_mem g h.2.1,
    g.injective.ne h.2.2.1, ?_⟩
  rw [← isometry_image_convexHull g V]
  have hseg : g '' segment ℝ x y = segment ℝ (g x) (g y) :=
    image_segment ℝ g.toAffineEquiv.toAffineMap x y
  rw [← hseg]
  exact convexFace_isometry_image g h.2.2.2

/-- Vertex transitivity uses ambient affine isometries preserving the entire set. -/
def IsVertexTransitive (V : Set E) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, ∃ g : E ≃ᵃⁱ[ℝ] E, g '' V = V ∧ g x = y

/-- Recursive vertex uniformity follows the actual facet relation. The
constructor requires transitivity at the current face and recursive uniformity
only at its facets, rather than assuming transitivity of every subface. It
also applies to points and the empty face, whose facet families are empty.
The paper's regular-polygon base must supply these transitivity data; this
predicate does not define regularity of polygons. -/
inductive RecursiveUniform (V : Set E) : Set E → Prop
  | intro {P : Set E} (transitive : IsVertexTransitive (V ∩ P))
      (facets : ∀ G, IsGeometricFacet P G → RecursiveUniform V G) :
      RecursiveUniform V P

/-- On a face of a finite hull, recursive facet uniformity implies vertex
transitivity of every subface. The proper nonempty case extends the subface
to a genuine facet, and the empty/whole cases are handled directly. -/
theorem RecursiveUniform.face_transitive {V : Set E} (hV : V.Finite) {P : Set E}
    (h : RecursiveUniform V P) :
    IsConvexFace (convexHull ℝ V) P →
      ∀ F, IsConvexFace P F → IsVertexTransitive (V ∩ F) := by
  induction h with
  | @intro P htrans hfacets ih =>
    intro hP F hF
    by_cases hne : F.Nonempty
    · by_cases heq : F = P
      · simpa only [heq] using htrans
      · have hPgen := face_eq_convexHull_inter V hP
        have hFgen : IsConvexFace (convexHull ℝ (V ∩ P)) F := by
          simpa only [hPgen] using hF
        have hproper : F ≠ convexHull ℝ (V ∩ P) := by
          simpa only [hPgen] using heq
        obtain ⟨G, hG, hFG⟩ := face_contained_in_facet
          (hV.subset inter_subset_left) hFgen hne hproper
        have hfacet : IsGeometricFacet P G := by simpa only [hPgen] using hG
        exact ih G hfacet (face_of_face hP hfacet.1) F
          (face_restrict hF hfacet.1.2.1 hFG)
    · intro x hx
      exact (hne ⟨x, hx.2⟩).elim

/-- Conversely, facewise transitivity builds the recursive facet predicate.
The recursion terminates because a proper facet has strictly fewer original
vertices, as proved using face reconstruction. This equivalence concerns
vertex transitivity, not the paper's regular-polygon base definition. -/
theorem recursiveUniform_of_face_transitive {V : Set E} (hV : V.Finite) {P : Set E}
    (hP : IsConvexFace (convexHull ℝ V) P)
    (hfaces : ∀ F, IsConvexFace P F → IsVertexTransitive (V ∩ F)) :
    RecursiveUniform V P := by
  have aux : ∀ n : ℕ, ∀ Q : Set E, (V ∩ Q).ncard = n →
      IsConvexFace (convexHull ℝ V) Q →
      (∀ F, IsConvexFace Q F → IsVertexTransitive (V ∩ F)) →
      RecursiveUniform V Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hn hQ hfacesQ
      refine RecursiveUniform.intro (hfacesQ Q ⟨hQ.1, IsExtreme.refl ℝ Q⟩) ?_
      intro G hG
      have hGglobal := face_of_face hQ hG.1
      have hsub : V ∩ G ⊆ V ∩ Q := inter_subset_inter_right V hG.1.2.1
      have hne : V ∩ G ≠ V ∩ Q := by
        intro heq
        apply hG.2.2.1
        rw [← face_eq_convexHull_inter V hGglobal,
          ← face_eq_convexHull_inter V hQ, heq]
      have hlt : (V ∩ G).ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
          (hV.subset inter_subset_left)
      exact ih (V ∩ G).ncard hlt G rfl hGglobal
        (fun F hF => hfacesQ F (face_of_face hG.1 hF))
  exact aux (V ∩ P).ncard P rfl hP hfaces

/-- For faces of finite hulls, facet-recursive and all-face vertex
transitivity are equivalent. No equivalence with polygon regularity is asserted. -/
theorem recursiveUniform_iff_face_transitive {V : Set E} (hV : V.Finite) {P : Set E}
    (hP : IsConvexFace (convexHull ℝ V) P) :
    RecursiveUniform V P ↔ ∀ F, IsConvexFace P F → IsVertexTransitive (V ∩ F) :=
  ⟨fun h => h.face_transitive hV hP, recursiveUniform_of_face_transitive hV hP⟩

/-- Uniformity data remain valid after changing ambient coordinates:
symmetries are conjugated, rather than presumed to fix both models. -/
theorem vertexTransitive_isometry_image (g : E ≃ᵃⁱ[ℝ] E) {V : Set E}
    (hV : IsVertexTransitive V) : IsVertexTransitive (g '' V) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨t, htV, htxy⟩ := hV x hx y hy
  refine ⟨g.symm.trans (t.trans g), ?_, ?_⟩
  · change (fun z => g (t (g.symm z))) '' (g '' V) = g '' V
    rw [Set.image_image]
    simp only [Function.comp_def, g.symm_apply_apply]
    change (fun z => g (t z)) '' V = g '' V
    rw [← Set.image_image g t V, htV]
  · change g (t (g.symm (g x))) = g y
    rw [g.symm_apply_apply, htxy]

end EuclideanFaces

/-- The actual ambient Euclidean space has dimension five. -/
abbrev Euclidean5 := EuclideanSpace ℝ (Fin 5)

/-- A geometric unit-edge uniform model. Vertices are actual extreme points,
not a labelled presentation. Uniformity is recorded facewise: every convex
face has a vertex-transitive ambient symmetry group. This includes the whole
polytope and all its facets. No connectivity or local-forcing field is included.

The facewise symmetry field can be constructed from facet-recursive vertex
transitivity by `ofRecursive`; the converse is also proved. The paper's
regular-polygon base case is not formalized here. The propagation proof only
uses vertex transitivity of the whole polytope and therefore also applies to
the broader class obtained by dropping uniformity of proper faces. -/
structure EuclideanUniform5 where
  vertices : Set Euclidean5
  finite_vertices : vertices.Finite
  spanning : affineSpan ℝ vertices = ⊤
  extreme_vertices : ∀ x ∈ vertices,
    IsConvexFace (convexHull ℝ vertices) {x}
  unit_edges : ∀ x y, GeometricEdge vertices x y → dist x y = 1
  uniform_faces : ∀ F, IsConvexFace (convexHull ℝ vertices) F →
    IsVertexTransitive (vertices ∩ F)

namespace EuclideanUniform5

/-- Construct the concrete model from recursive facet uniformity. The
all-face symmetry field is derived by finite-face geometry, not supplied as
an additional assumption. Polygon regularity is not encoded by this input. -/
noncomputable def ofRecursive (V : Set Euclidean5) (hfinite : V.Finite)
    (hspan : affineSpan ℝ V = ⊤)
    (hextreme : ∀ x ∈ V, IsConvexFace (convexHull ℝ V) {x})
    (hunit : ∀ x y, GeometricEdge V x y → dist x y = 1)
    (hrecursive : RecursiveUniform V (convexHull ℝ V)) : EuclideanUniform5 where
  vertices := V
  finite_vertices := hfinite
  spanning := hspan
  extreme_vertices := hextreme
  unit_edges := hunit
  uniform_faces := hrecursive.face_transitive hfinite
    ⟨convex_convexHull ℝ V, IsExtreme.refl ℝ _⟩

/-- Every concrete model also supplies recursive uniformity along its actual
facets; this checks both directions of the transitivity-only equivalence. -/
theorem recursive_uniform (P : EuclideanUniform5) :
    RecursiveUniform P.vertices (convexHull ℝ P.vertices) :=
  recursiveUniform_of_face_transitive P.finite_vertices
    ⟨convex_convexHull ℝ P.vertices, IsExtreme.refl ℝ _⟩ P.uniform_faces

@[ext] theorem ext {P Q : EuclideanUniform5} (h : P.vertices = Q.vertices) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Full dimension rules out the entire polytope being just an edge. -/
theorem segment_ne_hull (P : EuclideanUniform5) (x y : Euclidean5) :
    segment ℝ x y ≠ convexHull ℝ P.vertices := by
  intro heq
  have hspan : affineSpan ℝ ({x, y} : Set Euclidean5) = ⊤ := by
    rw [← affineSpan_convexHull (𝕜 := ℝ), convexHull_pair, heq,
      affineSpan_convexHull, P.spanning]
  have hdim := (collinear_pair ℝ x y).finrank_le_one
  have hdir := congrArg (fun S : AffineSubspace ℝ Euclidean5 => S.direction) hspan
  dsimp only at hdir
  rw [direction_affineSpan, AffineSubspace.direction_top] at hdir
  rw [hdir, finrank_top, finrank_euclideanSpace_fin] at hdim
  omega

/-- Every geometric edge is contained in a genuine facet, with both full
vertex-set incidences. This is proved, rather than assumed as a star field. -/
theorem edge_in_facet (P : EuclideanUniform5) {x y : Euclidean5}
    (h : GeometricEdge P.vertices x y) :
    ∃ F, IsGeometricFacet (convexHull ℝ P.vertices) F ∧
      x ∈ P.vertices ∩ F ∧ y ∈ P.vertices ∩ F := by
  obtain ⟨F, hF, hsub⟩ := face_contained_in_facet P.finite_vertices h.2.2.2
    ⟨x, left_mem_segment ℝ x y⟩ (P.segment_ne_hull x y)
  exact ⟨F, hF, ⟨h.1, hsub (left_mem_segment ℝ x y)⟩,
    ⟨h.2.1, hsub (right_mem_segment ℝ x y)⟩⟩

/-- Equal full facet vertex-set stars determine all geometric neighbours.
The proof reconstructs the common facet hull and restricts/lifts convex faces. -/
theorem neighbours_of_star_eq {P Q : EuclideanUniform5} {x y : Euclidean5}
    (hstar : facetStar P.vertices x = facetStar Q.vertices x)
    (hxy : GeometricEdge P.vertices x y) : GeometricEdge Q.vertices x y := by
  obtain ⟨F, hF, hxF, hyF⟩ := P.edge_in_facet hxy
  have hmem : P.vertices ∩ F ∈ facetStar P.vertices x :=
    ⟨F, hF, rfl, hxF⟩
  rw [hstar] at hmem
  obtain ⟨G, hG, hverts, hxG⟩ := hmem
  have hyG : y ∈ Q.vertices ∩ G := hverts ▸ hyF
  have hFG : F = G := by
    rw [← face_eq_convexHull_inter P.vertices hF.1,
      ← face_eq_convexHull_inter Q.vertices hG.1, hverts]
  have hxG' : x ∈ Q.vertices ∩ G := hverts ▸ hxG
  refine ⟨hxG'.1, hyG.1, hxy.2.2.1, ?_⟩
  apply face_of_face hG.1
  rw [← hFG]
  exact face_restrict hxy.2.2.2 hF.1.2.1
    (hF.1.1.segment_subset hxF.2 hyF.2)

/-- The whole-face instance of uniformity supplies vertex transitivity. -/
theorem vertex_transitive (P : EuclideanUniform5) : IsVertexTransitive P.vertices := by
  have hinter : P.vertices ∩ convexHull ℝ P.vertices = P.vertices :=
    inter_eq_left.mpr (subset_convexHull ℝ P.vertices)
  have h := P.uniform_faces (convexHull ℝ P.vertices)
    ⟨convex_convexHull ℝ P.vertices, IsExtreme.refl ℝ _⟩
  simpa only [hinter] using h

/-- A change of ambient Euclidean coordinates preserves every defining field. -/
noncomputable def image (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) (P : EuclideanUniform5) : EuclideanUniform5 where
  vertices := g '' P.vertices
  finite_vertices := P.finite_vertices.image g
  spanning := g.toAffineEquiv.toAffineMap.span_eq_top_of_surjective g.surjective P.spanning
  extreme_vertices := by
    rintro _ ⟨x, hx, rfl⟩
    have h := convexFace_isometry_image g (P.extreme_vertices x hx)
    simpa only [isometry_image_convexHull, Set.image_singleton] using h
  unit_edges := by
    intro x y hxy
    have hback := geometricEdge_isometry_image g.symm hxy
    rw [isometry_symm_image_image] at hback
    have h := P.unit_edges _ _ hback
    simpa only [g.symm.dist_map] using h
  uniform_faces := by
    intro F hF
    have hback := convexFace_isometry_image g.symm hF
    rw [← isometry_image_convexHull g P.vertices, isometry_symm_image_image] at hback
    have h := vertexTransitive_isometry_image g (P.uniform_faces _ hback)
    rwa [Set.image_inter g.injective, isometry_image_symm_image] at h

@[simp] theorem image_vertices (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) (P : EuclideanUniform5) :
    (image g P).vertices = g '' P.vertices := rfl

/-- Ambient isometries act bijectively on the concrete model class. -/
noncomputable def imageEquiv (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) : EuclideanUniform5 ≃ EuclideanUniform5 where
  toFun := image g
  invFun := image g.symm
  left_inv P := ext (isometry_symm_image_image g P.vertices)
  right_inv P := ext (isometry_image_symm_image g P.vertices)

/-- The supplied generators are exactly the geometric extreme points. -/
theorem vertices_eq_extremePoints (P : EuclideanUniform5) :
    P.vertices = (convexHull ℝ P.vertices).extremePoints ℝ := by
  apply Set.Subset.antisymm
  · intro x hx
    exact isExtreme_singleton.mp (P.extreme_vertices x hx).2
  · exact extremePoints_convexHull_subset

/-- Equality of the actual convex polytopes also determines the model. -/
theorem eq_of_hull_eq {P Q : EuclideanUniform5}
    (h : convexHull ℝ P.vertices = convexHull ℝ Q.vertices) : P = Q := by
  apply ext
  rw [P.vertices_eq_extremePoints, Q.vertices_eq_extremePoints, h]

@[simp] theorem image_symm_image (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) (P : EuclideanUniform5) :
    image g.symm (image g P) = P := ext (isometry_symm_image_image g P.vertices)

@[simp] theorem image_image_symm (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) (P : EuclideanUniform5) :
    image g (image g.symm P) = P := ext (isometry_image_symm_image g P.vertices)

/-- The ambient point isometry induces a bijection on sets of full facet vertex sets. -/
noncomputable def starEquiv (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) :
    Set (Set Euclidean5) ≃ Set (Set Euclidean5) :=
  Equiv.Set.congr (Equiv.Set.congr g.toAffineEquiv.toEquiv)

theorem image_star (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) (P : EuclideanUniform5)
    (x : Euclidean5) :
    facetStar (image g P).vertices (g x) = starEquiv g (facetStar P.vertices x) :=
  facetStar_isometry_image g P.vertices x

/-- A finite implementation of the actual geometric vertex set. -/
noncomputable def vertexFinset (P : EuclideanUniform5) : Finset Euclidean5 :=
  P.finite_vertices.toFinset

@[simp] theorem coe_vertexFinset (P : EuclideanUniform5) :
    (P.vertexFinset : Set Euclidean5) = P.vertices := P.finite_vertices.coe_toFinset

@[simp] theorem mem_vertexFinset (P : EuclideanUniform5) (x : Euclidean5) :
    x ∈ P.vertexFinset ↔ x ∈ P.vertices := P.finite_vertices.mem_toFinset

theorem finset_transitive (P : EuclideanUniform5) :
    ∀ x ∈ P.vertexFinset, ∀ y ∈ P.vertexFinset,
      ∃ g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5,
        g '' (P.vertexFinset : Set Euclidean5) = (P.vertexFinset : Set Euclidean5) ∧ g x = y := by
  intro x hx y hy
  obtain ⟨g, hg, hxy⟩ := P.vertex_transitive x ((P.mem_vertexFinset x).mp hx)
    y ((P.mem_vertexFinset y).mp hy)
  exact ⟨g, by simpa only [coe_vertexFinset] using hg, hxy⟩

/-- The actual edge graph, with no auxiliary connectivity field in the model. -/
def GraphConnected (P : EuclideanUniform5) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices,
    Relation.ReflTransGen (GeometricEdge P.vertices) x y

/-- Connectivity is derived from ambient vertex transitivity. The sphere is
obtained from the centroid; the exposed-edge path comes from the closest-pair
cut proof in Separation, then each exposed edge is a convex one-face. -/
theorem graph_connected (P : EuclideanUniform5) : P.GraphConnected := by
  intro x hx y hy
  have hpath := vertex_transitive_edge_graph_connected P.vertexFinset P.finset_transitive
    ((P.mem_vertexFinset x).mpr hx) ((P.mem_vertexFinset y).mpr hy)
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hab ih =>
    have ih := ih ((P.mem_vertexFinset a).mp hab.1)
    exact ih.tail (by simpa only [coe_vertexFinset] using isEdge_geometricEdge hab)

/-- For these models the convex one-face definition agrees with the project's
exposed-edge definition. Cosphericity is derived from actual vertex symmetries;
unit edges then identify both relations with unit distance. -/
theorem geometricEdge_iff_isEdge (P : EuclideanUniform5) {x y : Euclidean5} :
    GeometricEdge P.vertices x y ↔ IsEdge P.vertexFinset x y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hx : x ∈ P.vertexFinset := (P.mem_vertexFinset x).mpr h.1
    have hy : y ∈ P.vertexFinset := (P.mem_vertexFinset y).mpr h.2.1
    obtain ⟨R, hR⟩ := vertex_transitive_cospherical P.vertexFinset ⟨x, hx⟩ P.finset_transitive
    have hsphere : ∀ z ∈ P.vertexFinset,
        ‖z - P.vertexFinset.centroid ℝ id‖ ^ 2 = R ^ 2 := by
      intro z hz
      rw [← dist_eq_norm, hR z hz]
    have hunit : ∀ v w, IsEdge P.vertexFinset v w → dist v w = 1 := by
      intro v w hvw
      apply P.unit_edges v w
      simpa only [coe_vertexFinset] using isEdge_geometricEdge hvw
    exact (isEdge_iff_dist_eq_one P.vertexFinset hsphere hunit hx hy).mpr (P.unit_edges x y h)
  · simpa only [coe_vertexFinset] using isEdge_geometricEdge h

/-- A concrete Euclidean star system, with every geometric field proved. -/
noncomputable def starSystem :
    StarSystem Euclidean5 (Set (Set Euclidean5)) EuclideanUniform5 where
  vertices := EuclideanUniform5.vertices
  finite_vertices := EuclideanUniform5.finite_vertices
  star := fun P => facetStar P.vertices
  adjacent := fun P => GeometricEdge P.vertices
  adjacent_mem := fun h => ⟨h.1, h.2.1⟩
  neighbours := by
    intro P Q x _ _ h y
    exact ⟨neighbours_of_star_eq h, neighbours_of_star_eq h.symm⟩
  connected := by
    intro P x y hx hy
    exact P.graph_connected x hx y hy
  ext := ext

/-- An ambient affine isometry supplies every `StarTransport` field. In
particular it acts on the whole class of models, including inverse images. -/
noncomputable def transport (g : Euclidean5 ≃ᵃⁱ[ℝ] Euclidean5) : StarTransport starSystem where
  point := g.toAffineEquiv.toEquiv
  stars := starEquiv g
  model := imageEquiv g
  vertices := fun P x => g.injective.mem_set_image
  star := image_star g
  adjacent := by
    intro P x y
    change GeometricEdge (g '' P.vertices) (g x) (g y) ↔ GeometricEdge P.vertices x y
    refine ⟨fun h => ?_, geometricEdge_isometry_image g⟩
    have hback := geometricEdge_isometry_image g.symm h
    simpa only [isometry_symm_image_image, g.symm_apply_apply] using hback

/-- Vertex transitivity of the concrete uniform model gives the abstract
transitivity data, using a symmetry of the first model alone. -/
theorem transport_transitive (r : Euclidean5) :
    ∀ P, r ∈ starSystem.vertices P →
      ∀ x ∈ starSystem.vertices P,
        ∃ t : StarTransport starSystem, t.model P = P ∧ t.point r = x := by
  intro P hr x hx
  obtain ⟨g, hg, hgr⟩ := P.vertex_transitive r hr x hx
  exact ⟨transport g, ext hg, hgr⟩

/-- Concrete geometric forcing at a shared star. No graph-connectivity premise
is needed for this single step. All transports are ambient affine isometries. -/
theorem local_forcing_step (r : Euclidean5) (s : Set (Set Euclidean5))
    (forcing : ∀ A B : EuclideanUniform5, r ∈ A.vertices → r ∈ B.vertices →
      facetStar A.vertices r = s → facetStar B.vertices r = s →
      ∀ y, GeometricEdge A.vertices r y →
        facetStar A.vertices y = facetStar B.vertices y)
    {A B : EuclideanUniform5} (hrA : r ∈ A.vertices) (hsA : facetStar A.vertices r = s)
    {x y : Euclidean5} (hxA : x ∈ A.vertices) (hxB : x ∈ B.vertices)
    (hx : facetStar A.vertices x = facetStar B.vertices x)
    (hxy : GeometricEdge A.vertices x y) :
    y ∈ B.vertices ∧ facetStar A.vertices y = facetStar B.vertices y := by
  obtain ⟨g, hgA, hgr⟩ := A.vertex_transitive r hrA x hxA
  have hgA' : image g A = A := ext hgA
  have hgAinv : image g.symm A = A := by
    have h := congrArg (image g.symm) hgA'
    simpa only [image_symm_image] using h.symm
  have hgrinv : g.symm x = r := by rw [← hgr, g.symm_apply_apply]
  let B' := image g.symm B
  have hrB' : r ∈ B'.vertices := ⟨x, hxB, hgrinv⟩
  have hsB' : facetStar B'.vertices r = s := by
    have h := congrArg (starEquiv g.symm) hx
    rw [← image_star g.symm A x, ← image_star g.symm B x, hgAinv, hgrinv] at h
    exact h.symm.trans hsA
  have hedge : GeometricEdge A.vertices r (g.symm y) := by
    have h := geometricEdge_isometry_image g.symm hxy
    change GeometricEdge (image g.symm A).vertices (g.symm x) (g.symm y) at h
    simpa only [hgAinv, hgrinv] using h
  have hforced := forcing A B' hrA hrB' hsA hsB' (g.symm y) hedge
  have hstars := congrArg (starEquiv g) hforced
  rw [← image_star g A (g.symm y), ← image_star g B' (g.symm y),
    hgA', g.apply_symm_apply] at hstars
  have hgB' : image g B' = B := image_image_symm g B
  rw [hgB'] at hstars
  exact ⟨(neighbours_of_star_eq hx hxy).2.1, hstars⟩

/-- Propagation in the concrete Euclidean model, deriving actual edge-graph
connectivity rather than accepting it as an additional premise. -/
theorem local_forcing_inclusion (r : Euclidean5) (s : Set (Set Euclidean5))
    (forcing : ∀ A B : EuclideanUniform5, r ∈ A.vertices → r ∈ B.vertices →
      facetStar A.vertices r = s → facetStar B.vertices r = s →
      ∀ y, GeometricEdge A.vertices r y →
        facetStar A.vertices y = facetStar B.vertices y)
    {A B : EuclideanUniform5}
    (hrA : r ∈ A.vertices) (hrB : r ∈ B.vertices)
    (hsA : facetStar A.vertices r = s) (hsB : facetStar B.vertices r = s) :
    ∀ x ∈ A.vertices, x ∈ B.vertices ∧
      facetStar A.vertices x = facetStar B.vertices x := by
  intro x hx
  have path := A.graph_connected r hrA x hx
  induction path with
  | refl => exact ⟨hrB, hsA.trans hsB.symm⟩
  | @tail y z _ hyz ih =>
    have ih := ih hyz.1
    exact local_forcing_step r s forcing hrA hsA hyz.1 ih.1 ih.2 hyz

/-- Concrete local uniqueness. Facet geometry, model extensionality, ambient
isometric transport, vertex transitivity and actual graph connectivity are
proved above. The fixed-root forcing premise is exactly the paper's premise. -/
theorem local_uniqueness_global (r : Euclidean5) (s : Set (Set Euclidean5))
    (forcing : ∀ A B : EuclideanUniform5, r ∈ A.vertices → r ∈ B.vertices →
      facetStar A.vertices r = s → facetStar B.vertices r = s →
      ∀ y, GeometricEdge A.vertices r y →
        facetStar A.vertices y = facetStar B.vertices y)
    {A B : EuclideanUniform5}
    (hrA : r ∈ A.vertices) (hrB : r ∈ B.vertices)
    (hsA : facetStar A.vertices r = s) (hsB : facetStar B.vertices r = s) : A = B := by
  apply ext
  apply Set.Subset.antisymm
  · exact fun x hx => (local_forcing_inclusion r s forcing hrA hrB hsA hsB x hx).1
  · exact fun x hx => (local_forcing_inclusion r s forcing hrB hrA hsB hsA x hx).1

end EuclideanUniform5

end Uniform5
