import Uniform5.PolygonChord
import Uniform5.Geometry
import Uniform5.ConvexSection

/-! Translating the polygon section into the containing polytope's coordinates. -/
noncomputable section
namespace Uniform5
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The global vertex-section equation is exactly the intrinsic section
 equation on any plane whose sphere centre is the projection of the origin. -/
theorem translated_figureHyperplane_iff {y v c : E} {R S : ℝ}
    (hv : ‖v‖ = R) (hvS : dist v c = S)
    (hyc : ⟪y - c, c⟫ = 0) (hvc : ⟪v - c, c⟫ = 0) :
    y ∈ figureHyperplane v R ↔ y - c ∈ figureHyperplane (v - c) S := by
  have hvSsq : ‖v - c‖ ^ 2 = S ^ 2 := by rw [← dist_eq_norm, hvS]
  have hsq := norm_sub_sq_real v c
  rw [hv, hvSsq] at hsq
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at hyc hvc
  change ⟪y, v⟫ = R ^ 2 - 1 / 2 ↔ ⟪y - c, v - c⟫ = S ^ 2 - 1 / 2
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]
  have hcv : ⟪c, v⟫ = ⟪v, c⟫ := real_inner_comm _ _
  constructor <;> intro h <;> nlinarith [hcv]

/-- Translating the circle model translates each of its vertices. -/
theorem regularPolygonPoint_translate (c e f : E) (ρ : ℝ) (p : ℕ) (k : ℤ) :
    regularPolygonPoint c e f ρ p k = c + regularPolygonPoint 0 e f ρ p k := by
  simp [regularPolygonPoint, add_assoc]

/-- The polygon hull commutes with translation of its circle centre. -/
theorem regularPolygonHull_translate (c e f : E) (ρ : ℝ) (p : ℕ) :
    convexHull ℝ (regularPolygonVertices c e f ρ p : Set E) =
      (fun z => c + z) '' convexHull ℝ (regularPolygonVertices 0 e f ρ p : Set E) := by
  classical
  have hsets : (regularPolygonVertices c e f ρ p : Set E) =
      (fun z => c + z) '' (regularPolygonVertices 0 e f ρ p : Set E) := by
    ext x
    simp only [regularPolygonVertices, Finset.mem_coe, Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_image]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, (regularPolygonPoint_translate c e f ρ p (k.val : ℤ)).symm⟩
    · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, regularPolygonPoint_translate c e f ρ p (k.val : ℤ)⟩
  rw [hsets]
  exact ((AffineEquiv.constVAdd ℝ E c).toAffineMap.image_convexHull _).symm

/-- The actual unit polygon's section in a containing centred sphere is its
neighbour chord, even when its own centre is not the global origin. -/
theorem regularPolygon_global_section {p : ℕ} (hp : 3 ≤ p) (c e f : E) {ρ R : ℝ}
    (hρ : 0 ≤ ρ) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (horth : ⟪e, f⟫ = 0)
    (hc : c ∈ affineSpan ℝ (regularPolygonVertices c e f ρ p : Set E))
    (hsphere : ∀ x ∈ regularPolygonVertices c e f ρ p, ‖x‖ = R)
    (hunit : dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p 0) = 1) :
    (convexHull ℝ (regularPolygonVertices c e f ρ p : Set E) ∩
      figureHyperplane (regularPolygonPoint c e f ρ p 0) R =
      segment ℝ (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p (-1))) ∧
    regularPolygonPoint c e f ρ p 1 ≠ regularPolygonPoint c e f ρ p (-1) ∧
    dist (regularPolygonPoint c e f ρ p 1) (regularPolygonPoint c e f ρ p (-1)) =
      2 * Real.cos (Real.pi / (p : ℝ)) := by
  classical
  let W := regularPolygonVertices c e f ρ p
  let W₀ := regularPolygonVertices (0 : E) e f ρ p
  let v := regularPolygonPoint c e f ρ p 0
  have hunit₀ : dist (regularPolygonPoint 0 e f ρ p 1)
      (regularPolygonPoint 0 e f ρ p 0) = 1 := by
    simpa only [regularPolygonPoint_translate c, dist_add_left] using hunit
  obtain ⟨hlocal, hne, hdist⟩ := regularPolygon_vertexFigure hp e f hρ he hf horth hunit₀
  have hs : ∀ x ∈ W, dist x c = ρ := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact regularPolygonPoint_on_sphere c e f hρ p he hf horth _
  have hv : v ∈ W := (regularPolygon_neighbor_mem c e f ρ hp).1
  have hnormal := circumsphere_centres_orthogonal (c := (0 : E)) hc
    (fun y hy => by simpa using hsphere y hy) hs
  have hn (y : E) (hy : y ∈ convexHull ℝ (W : Set E)) : ⟪y - c, c⟫ = 0 := by
    simpa using hnormal y (convexHull_subset_affineSpan (W : Set E) hy)
  have hvtr : v - c = regularPolygonPoint 0 e f ρ p 0 := by
    simp [v, regularPolygonPoint_translate c]
  have hiff (y : E) (hy : y ∈ convexHull ℝ (W : Set E)) :
      y ∈ figureHyperplane v R ↔ y - c ∈ figureHyperplane (regularPolygonPoint 0 e f ρ p 0) ρ := by
    simpa only [hvtr] using translated_figureHyperplane_iff (hsphere v hv) (hs v hv)
      (hn y hy) (hn v (subset_convexHull ℝ (W : Set E) hv))
  have hglobal : convexHull ℝ (W : Set E) ∩ figureHyperplane v R =
      (fun z => c + z) '' (convexHull ℝ (W₀ : Set E) ∩
        figureHyperplane (regularPolygonPoint 0 e f ρ p 0) ρ) := by
    ext y
    constructor
    · rintro ⟨hy, hyH⟩
      have hyH' := (hiff y hy).mp hyH
      obtain ⟨z, hz, rfl⟩ := (regularPolygonHull_translate c e f ρ p) ▸ hy
      exact ⟨z, ⟨hz, by simpa only [add_sub_cancel_left] using hyH'⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzH⟩, rfl⟩
      have hy : c + z ∈ convexHull ℝ (W : Set E) := by
        rw [regularPolygonHull_translate]
        exact ⟨z, hz, rfl⟩
      exact ⟨hy, (hiff _ hy).mpr (by simpa only [add_sub_cancel_left] using hzH)⟩
  refine ⟨?_, ?_, regularPolygon_neighbor_chord hp c e f hρ he hf horth hunit⟩
  · change convexHull ℝ (W : Set E) ∩ figureHyperplane v R = _
    rw [hglobal, hlocal]
    rw [regularPolygonPoint_translate c e f ρ p 1, regularPolygonPoint_translate c e f ρ p (-1)]
    exact image_segment ℝ (AffineEquiv.constVAdd ℝ E c).toAffineMap _ _
  · intro h
    apply hne
    rw [regularPolygonPoint_translate c e f ρ p 1,
      regularPolygonPoint_translate c e f ρ p (-1)] at h
    exact add_left_cancel h

/-- Polygonal-face clause of the vertex-figure lemma, for an actual regular
unit polygon with its chosen vertex indexed by zero. The resulting segment
is a genuine nondegenerate convex face of the whole vertex figure. -/
def PolygonSectionGeometry (V : Finset E) (v : E) (R : ℝ) : Prop :=
  ∀ (p : ℕ) (c e f : E) (ρ : ℝ) (K : Set E), 3 ≤ p → 0 ≤ ρ →
    ‖e‖ = 1 → ‖f‖ = 1 → ⟪e, f⟫ = 0 →
    IsConvexFace (convexHull ℝ (V : Set E)) K →
    (V : Set E) ∩ K = (regularPolygonVertices c e f ρ p : Set E) →
    v = regularPolygonPoint c e f ρ p 0 → c ∈ affineSpan ℝ K →
    dist (regularPolygonPoint c e f ρ p 1) v = 1 →
    let x := regularPolygonPoint c e f ρ p 1
    let y := regularPolygonPoint c e f ρ p (-1)
    K ∩ figureHyperplane v R = segment ℝ x y ∧
    IsConvexFace (convexHull ℝ (V : Set E) ∩ figureHyperplane v R) (segment ℝ x y) ∧
    x ≠ y ∧ dist x y = 2 * Real.cos (Real.pi / (p : ℝ))

/-- Derives the polygonal section and its edge length from the actual face
and circle coordinates, with no assumed section/edge identification. -/
theorem unit_edge_polygonSectionGeometry [FiniteDimensional ℝ E]
    (V : Finset E) {v : E} {R : ℝ} (hv : v ∈ V)
    (hsphere : ∀ y ∈ V, ‖y‖ = R)
    (hunit : ∀ y z, IsEdge V y z → dist y z = 1) :
    PolygonSectionGeometry V v R := by
  intro p c e f ρ K hp hρ he hf ho hK hverts hv0 hc hside
  subst v
  have hKeq : K = convexHull ℝ (regularPolygonVertices c e f ρ p : Set E) := by
    rw [exposedFace_eq_convexHull_inter (V : Set E) (finite_convexFace_isExposed V hK), hverts]
  have hc' : c ∈ affineSpan ℝ (regularPolygonVertices c e f ρ p : Set E) := by
    simpa only [hKeq, affineSpan_convexHull] using hc
  have hsp : ∀ x ∈ regularPolygonVertices c e f ρ p, ‖x‖ = R := by
    intro x hx
    have hx' : x ∈ (V : Set E) ∩ K := hverts.symm ▸ hx
    exact hsphere x hx'.1
  have hvK : regularPolygonPoint c e f ρ p 0 ∈ K := by
    have hh := (regularPolygon_neighbor_mem c e f ρ hp).1
    exact (show regularPolygonPoint c e f ρ p 0 ∈ (V : Set E) ∩ K from hverts.symm ▸ hh).2
  obtain ⟨hsec, hne, hdist⟩ := regularPolygon_global_section hp c e f hρ he hf ho hc' hsp hside
  rw [← hKeq] at hsec
  have hface := (unit_edge_convexVertexFigureCorrespondence V hv hsphere hunit).1 K hK hvK
  rw [hsec] at hface
  exact ⟨hsec, hface, hne, hdist⟩

end Uniform5
