import Uniform5.CompositionModelIncidence
import Uniform5.CompositionClassificationInputs
import Uniform5.CompositionActualCycleData

/-! Fact F2 for actual faces and complete polygon cycles in arbitrary
finite-dimensional Euclidean ambient spaces. Polygon parameters are the
actual numbers of extreme points, retained by intrinsic coordinate maps. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An intrinsic model carries the same actual polygon, including its side count. -/
theorem unitUniform_intrinsic_polygon_model {d q : ℕ} {P G : Set E}
    (hP : UnitUniform (d + 3) P) (hG : PolygonFace P G q) :
    ∃ (Q H : Set (Space (d + 3))), UnitUniform (d + 3) Q ∧
      PolygonFace Q H q ∧ Congruent P Q ∧ Congruent G H := by
  obtain ⟨f, Q, hf, hQP, hQ⟩ := exists_unitUniform_intrinsic_model hP
  have hG' : PolygonFace (f '' Q) G q := hf ▸ hG
  have hi := embedding_face_image_preimage f hG'.1
  refine ⟨Q, f ⁻¹' G, hQ,
    embedding_polygonFace_preimage f (uniform_finitePolytope hQ.1) hG',
    congruent_symm hQP, ?_⟩
  have hh := congruent_affineIsometry_image f (f ⁻¹' G)
  rw [hi] at hh
  exact congruent_symm hh

/-- Fact F2 in dimension three, with the original polygon parameter. -/
theorem unitUniform3_nonexceptional_polygon_family
    (classification3D : CitedClassification3D) {P G : Set E} {q : ℕ}
    (hP : UnitUniform 3 P) (hG : PolygonFace P G q)
    (hq : ¬ CaseB.ExceptionalPolygon q) :
    Congruent P (polygonPrismModel q) ∨ Congruent P (antiprismModel q) := by
  obtain ⟨Q, H, hQ, hH, hPQ, _⟩ := unitUniform_intrinsic_polygon_model (d := 0) hP hG
  rcases classification3D.family_polygon Q q hQ ⟨H, hH⟩ hq with h | h
  · exact Or.inl (congruent_trans hPQ h)
  · exact Or.inr (congruent_trans hPQ h)

/-- Fact F2 in dimension four, retaining the actual polygon as the first factor. -/
theorem unitUniform4_nonexceptional_polygon_family
    (classification4D : CitedClassification4D) {P G : Set E} {q : ℕ}
    (hP : UnitUniform 4 P) (hG : PolygonFace P G q)
    (hq : ¬ CaseB.ExceptionalPolygon q) :
    (∃ p : ℕ, 3 ≤ p ∧ Congruent P (duoprismModel q p)) ∨
      Congruent P (antiprismPrismModel q) := by
  obtain ⟨Q, H, hQ, hH, hPQ, _⟩ := unitUniform_intrinsic_polygon_model (d := 1) hP hG
  rcases classification4D.family_polygon Q q hQ ⟨H, hH⟩ hq with ⟨p, hp, h⟩ | h
  · exact Or.inl ⟨p, hp, congruent_trans hPQ h⟩
  · exact Or.inr (congruent_trans hPQ h)

theorem large_polygon_nonexceptional {q : ℕ} (hq : 17 ≤ q) :
    ¬ CaseB.ExceptionalPolygon q := by
  simp only [CaseB.ExceptionalPolygon, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem family_polygon_nonexceptional {q : ℕ} (hq : CaseB.FamilyPolygon q) :
    ¬ CaseB.ExceptionalPolygon q := by
  simp only [CaseB.FamilyPolygon, List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [CaseB.ExceptionalPolygon, List.mem_cons, List.not_mem_nil, or_false]
  omega

omit [FiniteDimensional ℝ E] in
/-- Restriction changes the parent face, not the polygon or its side count. -/
theorem polygonFace_restrict_parent {P G C : Set E} {q : ℕ}
    (hG : PolygonFace P G q) (hC : C ⊆ P) (hGC : G ⊆ C) :
    PolygonFace C G q := ⟨face_restrict hG.1 hC hGC, hG.2⟩

/-- Every actual three-cell at a nonexceptional polygon has the stated model. -/
theorem unitUniform_three_face_polygon_family
    (classification3D : CitedClassification3D) {d q : ℕ} {P G C : Set E}
    (hP : UnitUniform (d + 3) P) (hG : PolygonFace P G q)
    (hC : IsConvexFace P C) (hGC : G ⊆ C) (hdC : affineDimension C = 3)
    (hq : ¬ CaseB.ExceptionalPolygon q) :
    Congruent C (polygonPrismModel q) ∨ Congruent C (antiprismModel q) := by
  have hUC := unitUniform_face hP hC ((polygonFace_nonempty hG).mono hGC) (by omega)
  rw [hdC] at hUC
  exact unitUniform3_nonexceptional_polygon_family classification3D hUC
    (polygonFace_restrict_parent hG hC.2.1 hGC) hq

/-- Every actual four-face at a nonexceptional polygon has the stated model. -/
theorem unitUniform_four_face_polygon_family
    (classification4D : CitedClassification4D) {d q : ℕ} {P G K : Set E}
    (hP : UnitUniform (d + 3) P) (hG : PolygonFace P G q)
    (hK : IsConvexFace P K) (hGK : G ⊆ K) (hdK : affineDimension K = 4)
    (hq : ¬ CaseB.ExceptionalPolygon q) :
    (∃ p : ℕ, 3 ≤ p ∧ Congruent K (duoprismModel q p)) ∨
      Congruent K (antiprismPrismModel q) := by
  have hUK := unitUniform_face hP hK ((polygonFace_nonempty hG).mono hGK) (by omega)
  rw [hdK] at hUK
  exact unitUniform4_nonexceptional_polygon_family classification4D hUK
    (polygonFace_restrict_parent hG hK.2.1 hGK) hq

/-- The special case needed at every large polygon of the five-polytope. -/
theorem unitUniform5_large_polygon_facet_family
    (classification4D : CitedClassification4D) {q : ℕ} {P G K : Set E}
    (hP : UnitUniform 5 P) (hG : PolygonFace P G q)
    (hK : Facet P K) (hGK : G ⊆ K) (hq : 17 ≤ q) :
    (∃ p : ℕ, 3 ≤ p ∧ Congruent K (duoprismModel q p)) ∨
      Congruent K (antiprismPrismModel q) := by
  exact unitUniform4_nonexceptional_polygon_family classification4D
    (unitUniform_facet hP hK) (polygonFace_restrict_parent hG hK.1.2.1 hGK)
    (large_polygon_nonexceptional hq)

/-- The entire actual cycle inherits F2, without a separately postulated model labeling. -/
theorem ActualPolygonCycle.nonexceptional_families
    {P G : Set (Space 5)} (D : ActualPolygonCycle P G)
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    {q : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G q)
    (hq : ¬ CaseB.ExceptionalPolygon q) :
    (∀ i, Congruent (D.cell i) (polygonPrismModel q) ∨
      Congruent (D.cell i) (antiprismModel q)) ∧
    (∀ i, (∃ p : ℕ, 3 ≤ p ∧ Congruent (D.facet i) (duoprismModel q p)) ∨
      Congruent (D.facet i) (antiprismPrismModel q)) := by
  constructor
  · intro i
    exact unitUniform_three_face_polygon_family classification3D hP hG
      (D.cell_face i) (D.cell_contains i) (D.cell_dimension i) hq
  · intro i
    exact unitUniform4_nonexceptional_polygon_family classification4D
      (D.facet_unitUniform hP i)
      (polygonFace_restrict_parent hG (D.facet_incidence i).1.1.2.1
        (D.facet_incidence i).2.1) hq

end Uniform5.Composition
