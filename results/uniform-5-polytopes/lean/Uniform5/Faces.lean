import Uniform5.Separation
import Mathlib.Data.Finset.Grade
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open Set

namespace Uniform5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex face, expressed using Mathlib's extreme-subset notion.
Unlike exposed subsets of general convex sets, these faces are transitive. -/
def IsConvexFace (P F : Set E) : Prop := Convex ℝ F ∧ IsExtreme ℝ P F

/-- Paper `lem:face`: a face of a face is a face. -/
theorem face_of_face {P F G : Set E} (hF : IsConvexFace P F)
    (hG : IsConvexFace F G) : IsConvexFace P G :=
  ⟨hG.1, hF.2.trans hG.2⟩

/-- A face contained in another face restricts to a face of it. -/
theorem face_restrict {P F G : Set E} (hG : IsConvexFace P G)
    (hFP : F ⊆ P) (hGF : G ⊆ F) : IsConvexFace F G :=
  ⟨hG.1, hG.2.mono hFP hGF⟩

/-- Paper `lem:face`, both directions for a segment with endpoints in a face.
The dimension-one/nondegeneracy condition can be added without altering it. -/
theorem segment_face_iff {P F : Set E} {p q : E}
    (hF : IsConvexFace P F) (hp : p ∈ F) (hq : q ∈ F) :
    IsConvexFace P (segment ℝ p q) ↔ IsConvexFace F (segment ℝ p q) :=
  ⟨fun h => face_restrict h hF.2.1 (hF.1.segment_subset hp hq),
    fun h => face_of_face hF h⟩

/-- Exposed edges restrict to any smaller convex hull containing the endpoints.
In particular this applies to the vertex set of a face. -/
theorem edge_restrict {V W : Finset E} {p q : E}
    (hWV : (W : Set E) ⊆ (V : Set E)) (hp : p ∈ W) (hq : q ∈ W)
    (hedge : IsEdge V p q) : IsEdge W p q := by
  refine ⟨hp, hq, hedge.2.2.1, hedge.2.2.2.mono ?_ ?_⟩
  · exact convexHull_mono hWV
  · exact segment_subset_convexHull hp hq

/-- A finite-hull extreme segment is exposed. Its affine line is disjoint
from the hull of generators outside the segment; strong separation gives a
functional constant on that line and strictly smaller on the other generators.
Generators inside the segment are redundant and are replaced by its endpoints.
This uses no transitivity assertion for exposed subsets of general convex sets. -/
private theorem finite_extreme_segment_isExposed {V : Finset E} {p q : E}
    (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (hf : IsExtreme ℝ (convexHull ℝ (V : Set E)) (segment ℝ p q)) :
    IsExposed ℝ (convexHull ℝ (V : Set E)) (segment ℝ p q) := by
  classical
  let B : Set E := {x ∈ (V : Set E) | x ∉ segment ℝ p q}
  let A := affineSpan ℝ ({p, q} : Set E)
  have hBP : convexHull ℝ B ⊆ convexHull ℝ (V : Set E) \ segment ℝ p q :=
    convexHull_min (fun x hx => ⟨subset_convexHull ℝ _ hx.1, hx.2⟩)
      (hf.convex_diff (convex_convexHull ℝ _))
  have hdisj : Disjoint (convexHull ℝ B) (A : Set E) := by
    rw [Set.disjoint_left]
    intro x hx hxA
    have hxP := (hBP hx).1
    have hxn := (hBP hx).2
    have hxp : x ≠ p := by intro h; exact hxn (h ▸ left_mem_segment ℝ p q)
    have hxq : x ≠ q := by intro h; exact hxn (h ▸ right_mem_segment ℝ p q)
    rcases (collinear_insert_of_mem_affineSpan_pair hxA).wbtw_or_wbtw_or_wbtw with h | h | h
    · have hi : p ∈ openSegment ℝ x q :=
        mem_openSegment_of_ne_left_right hxp hpq.symm h.mem_segment
      exact hxn (hf.2 hxP (subset_convexHull ℝ _ hq) (left_mem_segment ℝ p q) hi).1
    · have hi : q ∈ openSegment ℝ p x :=
        mem_openSegment_of_ne_left_right hpq hxq h.mem_segment
      exact hxn (hf.2 (subset_convexHull ℝ _ hp) hxP (right_mem_segment ℝ p q) hi).2
    · exact hxn (by simpa only [segment_symm] using h.mem_segment)
  letI : FiniteDimensional ℝ A.direction :=
    finiteDimensional_direction_affineSpan_of_finite ℝ (Set.toFinite _)
  obtain ⟨L, a, b, hB, hab, hA⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ B) ((V.finite_toSet.subset (fun _ hx => hx.1)).isCompact_convexHull)
    A.convex A.closed_of_finiteDimensional hdisj
  have hpA : p ∈ A := left_mem_affineSpan_pair ℝ p q
  have hLp : b < L p := hA p hpA
  have hpqL : L q = L p := by
    by_contra hn
    have hd : L q - L p ≠ 0 := sub_ne_zero.mpr hn
    have h := hA (AffineMap.lineMap p q ((b - L p) / (L q - L p)))
      (AffineMap.lineMap_mem_affineSpan_pair _ _ _)
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul] at h
    simp only [smul_eq_mul] at h
    have he : (1 - (b - L p) / (L q - L p)) * L p +
        ((b - L p) / (L q - L p)) * L q = b := by field_simp [hd]; ring
    exact (ne_of_gt h) he
  let S : Set E := B ∪ {p, q}
  have hpS : p ∈ S := Or.inr (by simp)
  have hqS : q ∈ S := Or.inr (by simp)
  have hSV : S ⊆ (V : Set E) := by
    rintro x (hx | hx)
    · exact hx.1
    · rcases hx with rfl | hx
      · exact hp
      · simpa only [Set.mem_singleton_iff] using hx ▸ hq
  have hHull : convexHull ℝ S = convexHull ℝ (V : Set E) := by
    apply Set.Subset.antisymm (convexHull_mono hSV)
    apply convexHull_min _ (convex_convexHull ℝ S)
    intro x hx
    by_cases hs : x ∈ segment ℝ p q
    · exact segment_subset_convexHull hpS hqS hs
    · exact subset_convexHull ℝ S (Or.inl ⟨hx, hs⟩)
  rw [← hHull]
  apply exposes_segment hpS hqS L (L p) rfl hpqL
  · intro x hx
    rcases hx with hx | hx
    · exact le_of_lt (lt_trans (hB x (subset_convexHull ℝ B hx)) (lt_trans hab hLp))
    · rcases hx with rfl | hx
      · rfl
      · have hxq : x = q := hx
        simp [hxq, hpqL]
  · intro x hx heq
    rcases hx with hx | hx
    · exact False.elim ((ne_of_lt (lt_trans (hB x (subset_convexHull ℝ B hx))
        (lt_trans hab hLp))) heq)
    · exact hx

/-- The general finite-polytope extreme/exposed bridge, retained as a named
property. The edge converse below proves the segment case directly and does
not require this property as an input. -/
def PolytopeFacesExposed (V : Finset E) : Prop :=
  ∀ F : Set E, IsConvexFace (convexHull ℝ (V : Set E)) F →
    IsExposed ℝ (convexHull ℝ (V : Set E)) F

/-- Paper `lem:face`, converse in the project's exposed-edge definition.
Transitivity is used for extreme faces, and exposure of the resulting segment
is proved directly for the finite hull. -/
theorem edge_of_face {V W : Finset E} {p q : E}
    (hface : IsConvexFace (convexHull ℝ (V : Set E)) (convexHull ℝ (W : Set E)))
    (hWV : (W : Set E) ⊆ (V : Set E)) (hedge : IsEdge W p q) : IsEdge V p q := by
  refine ⟨hWV hedge.1, hWV hedge.2.1, hedge.2.2.1, ?_⟩
  exact finite_extreme_segment_isExposed (hWV hedge.1) (hWV hedge.2.1)
    hedge.2.2.1 (hface.2.trans hedge.2.2.2.isExtreme)

section SimpleVertex

variable {Face Edge : Type*} [PartialOrder Face] [OrderTop Face]
  [Fintype Edge] [DecidableEq Edge]

/-- Named geometric input for paper `lem:simple`: the face lattice through a
vertex of a four-dimensional polytope with four incident edges is identified
with the face lattice of its tetrahedral vertex figure. `Face` includes the
vertex itself and the whole polytope; coatoms are facets through the vertex.
`Edge` is the type of incident edges; `edgesIn` records their incidence.

Constructing this order isomorphism from geometric degree four (including the
vertex-figure face-lattice theorem and tetrahedrality) is not formalized here.
The structure assumes the full lattice correspondence, not the desired
three-edge facet counts or uniqueness statements. -/
structure VertexFigureSimplexFaceLattice (edgesIn : Face → Finset Edge) where
  faceEquiv : Face ≃o Finset Edge
  incidence : ∀ F, faceEquiv F = edgesIn F

/-- The facets of a simplex on four vertices are exactly its three-subsets. -/
theorem four_element_coatom_iff {s : Finset Edge} (hfour : Fintype.card Edge = 4) :
    IsCoatom s ↔ s.card = 3 := by
  constructor
  · intro hs
    obtain ⟨e, rfl⟩ := Finset.isCoatom_iff.mp hs
    simp [Finset.card_compl, hfour]
  · intro hs
    have hcomp : sᶜ.card = 1 := by simp [Finset.card_compl, hfour, hs]
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcomp
    apply Finset.isCoatom_iff.mpr
    exact ⟨e, by simpa using congrArg (fun t : Finset Edge => tᶜ) he⟩

/-- Paper `lem:simple`: each facet through a degree-four vertex has three of
its four incident edges, given the named vertex-figure geometric input. -/
theorem simple_vertex_facet_iff_three_edges (edgesIn : Face → Finset Edge)
    (hfigure : VertexFigureSimplexFaceLattice edgesIn) (hfour : Fintype.card Edge = 4)
    (F : Face) : IsCoatom F ↔ (edgesIn F).card = 3 := by
  rw [← hfigure.faceEquiv.isCoatom_iff F, hfigure.incidence F]
  exact four_element_coatom_iff hfour

/-- Paper `lem:simple`: each three-subset is incident to exactly one facet.
Existence and uniqueness follow from the lattice isomorphism; the fact that
the preimage is a facet is derived from the finite coatom calculation. -/
theorem simple_vertex_unique_facet (edgesIn : Face → Finset Edge)
    (hfigure : VertexFigureSimplexFaceLattice edgesIn) (hfour : Fintype.card Edge = 4)
    (s : Finset Edge) (hthree : s.card = 3) :
    ∃! F : Face, IsCoatom F ∧ edgesIn F = s := by
  refine ⟨hfigure.faceEquiv.symm s, ⟨?_, ?_⟩, ?_⟩
  · apply (hfigure.faceEquiv.isCoatom_iff _).mp
    simpa using (four_element_coatom_iff hfour).mpr hthree
  · rw [← hfigure.incidence, hfigure.faceEquiv.apply_symm_apply]
  · intro F hF
    apply hfigure.faceEquiv.injective
    rw [hfigure.incidence, hF.2, hfigure.faceEquiv.apply_symm_apply]

end SimpleVertex

end Uniform5
