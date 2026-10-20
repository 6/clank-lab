import Uniform5.PolytopeFaces
import Uniform5.ExposedSection

/-!
# The convex-face correspondence for a vertex figure

The finite-hull extreme/exposed theorem converts the proved exposed-face
correspondence to the ordinary convex-face formulation. The section is a
finite hull by the unit-edge neighbour-hull identity, so the same conversion
also applies on the section side. No face correspondence is assumed.
-/

namespace Uniform5
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The ordinary convex-face version of the vertex-figure correspondence:
restriction, inclusion reflection, unique lifting, and dimension shift.
Faces through the vertex include the singleton, which restricts to the empty
face. Dimensions use natural-number truncation for that singleton/empty pair. -/
def ConvexVertexFigureCorrespondence (V : Finset E) (v : E) (R : ℝ) : Prop :=
  let P := convexHull ℝ (V : Set E)
  let H := figureHyperplane v R
  (∀ F, IsConvexFace P F → v ∈ F → IsConvexFace (P ∩ H) (F ∩ H)) ∧
  (∀ F G, IsConvexFace P F → v ∈ F → IsConvexFace P G → v ∈ G →
    (F ∩ H ⊆ G ∩ H ↔ F ⊆ G)) ∧
  (∀ G, IsConvexFace (P ∩ H) G →
    ∃! F, IsConvexFace P F ∧ v ∈ F ∧ F ∩ H = G) ∧
  (∀ F, IsConvexFace P F → v ∈ F →
    Module.finrank ℝ (affineSpan ℝ (F ∩ H)).direction =
      Module.finrank ℝ (affineSpan ℝ F).direction - 1)

/-- The complete convex-face vertex-figure correspondence for a finite
cospherical unit-edge hull. Finite generators for the section are constructed
as the neighbours of the chosen vertex, rather than assumed separately. -/
theorem unit_edge_convexVertexFigureCorrespondence (V : Finset E) {v : E} {R : ℝ}
    (hv : v ∈ V) (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hunit : ∀ x y, IsEdge V x y → dist x y = 1) :
    ConvexVertexFigureCorrespondence V v R := by
  classical
  let P := convexHull ℝ (V : Set E)
  let H := figureHyperplane v R
  let N := V.filter (fun x => IsEdge V v x)
  have hN : (N : Set E) = {x : E | IsEdge V v x} := by
    ext x
    simp only [N, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
    exact ⟨And.right, fun h => ⟨h.2.1, h⟩⟩
  have hsectionHull : P ∩ H = convexHull ℝ (N : Set E) := by
    change convexHull ℝ (V : Set E) ∩ figureHyperplane v R = _
    rw [unit_edge_section_eq_neighborHull V hv hsphere hunit, ← hN]
  have hsectionConvex : Convex ℝ (P ∩ H) := by
    rw [hsectionHull]
    exact convex_convexHull ℝ _
  have section_exposed (G : Set E) (hG : IsConvexFace (P ∩ H) G) :
      IsExposed ℝ (P ∩ H) G := by
    rw [hsectionHull] at hG ⊢
    exact polytope_faces_exposed N G hG
  have section_face (G : Set E) (hG : IsExposed ℝ (P ∩ H) G) :
      IsConvexFace (P ∩ H) G :=
    ⟨hG.convex hsectionConvex, hG.isExtreme⟩
  obtain ⟨restrict, inclusion, lift, dimension⟩ :=
    unit_edge_exposedVertexFigureCorrespondence V hv hsphere hunit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F hF hvF
    exact section_face _ (restrict F (polytope_faces_exposed V F hF) hvF)
  · intro F G hF hvF hG hvG
    exact inclusion F G (polytope_faces_exposed V F hF) hvF
      (polytope_faces_exposed V G hG) hvG
  · intro G hG
    obtain ⟨F, ⟨hF, hvF, hFG⟩, hunique⟩ := lift G (section_exposed G hG)
    refine ⟨F, ⟨⟨hF.convex (convex_convexHull ℝ _), hF.isExtreme⟩, hvF, hFG⟩, ?_⟩
    rintro K ⟨hK, hvK, hKG⟩
    exact hunique K ⟨polytope_faces_exposed V K hK, hvK, hKG⟩
  · intro F hF hvF
    exact dimension F (polytope_faces_exposed V F hF) hvF

end Uniform5
