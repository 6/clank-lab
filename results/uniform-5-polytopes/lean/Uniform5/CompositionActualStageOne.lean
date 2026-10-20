import Uniform5.CompositionCyclicDomain

/-! Actual geometry supplies the precise root witness consumed by S1. -/
noncomputable section
namespace Uniform5.Composition
open Set

namespace CycleModelLabels
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G}
  (L : CycleModelLabels D CellType CanonicalFacetName)

theorem finite_angleSum_eq (hclosed : L.cellLabel D.length = L.cellLabel 0) (k : ℕ) :
    L.cyclicWord.angleSum k (intrinsicRadius ∘ L.facetModel)
      (intrinsicRadius ∘ L.cellModel) = ∑ i ∈ Finset.range D.length, L.angle k i := by
  calc
    _ = ∑ i : Fin D.length, L.angle k i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [cyclicWord, Function.comp_apply]
      rw [cycle_apply_finRotate (by have := D.length_ge; omega) L.cellLabel hclosed]
      simp only [angle, dif_pos i.isLt]
    _ = _ := Fin.sum_univ_eq_sum_range (L.angle k) D.length

theorem finite_domain (hclosed : L.cellLabel D.length = L.cellLabel 0)
    {k : ℕ} (hD : D.Stage1Geometry k) :
    L.cyclicWord.domain k (intrinsicRadius ∘ L.facetModel)
      (intrinsicRadius ∘ L.cellModel) (1 / intrinsicRadius P) := by
  have h := (L.geometric_properties hD).2.1
  refine ⟨h.1, ?_, ?_⟩
  · intro i
    exact h.2.1 i i.isLt.le
  · intro i
    have hi := h.2.2 i i.isLt
    dsimp only [cyclicWord, Function.comp_apply]
    rw [cycle_apply_finRotate (by have := D.length_ge; omega) L.cellLabel hclosed]
    simpa only [height, angle, dif_pos i.isLt] using hi

theorem finite_lowerAngleSum_eq (hclosed : L.cellLabel D.length = L.cellLabel 0)
    (N : LibraryNumericalData) (k : ℕ) :
    (∑ i : Fin D.length, (N.angleBall (L.cyclicWord.facet i) k (L.cyclicWord.cell i)
      (L.cyclicWord.cell (finRotate D.length i))).lower) =
      ∑ i ∈ Finset.range D.length, L.certifiedLowerAngle N k i := by
  calc
    _ = ∑ i : Fin D.length, L.certifiedLowerAngle N k i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [cyclicWord]
      rw [cycle_apply_finRotate (by have := D.length_ge; omega) L.cellLabel hclosed]
      simp only [certifiedLowerAngle, dif_pos i.isLt]
    _ = _ := Fin.sum_univ_eq_sum_range (L.certifiedLowerAngle N k) D.length

theorem finite_radius_domain (hP : UnitUniform 5 P) :
    0 < L.cyclicWord.maxRadius (intrinsicRadius ∘ L.facetModel) ∧
      L.cyclicWord.maxRadius (intrinsicRadius ∘ L.facetModel) < intrinsicRadius P ∧
      0 < 1 / intrinsicRadius P ∧
      1 / intrinsicRadius P < 1 / L.cyclicWord.maxRadius (intrinsicRadius ∘ L.facetModel) := by
  have hh := unitUniform5_facet_radius_domain hP D.facet
    (fun i => (D.facet_incidence i).1)
  have heq : L.cyclicWord.maxRadius (intrinsicRadius ∘ L.facetModel) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => intrinsicRadius (D.facet i)) := by
    unfold CyclicWord.maxRadius
    congr 1
    funext i
    exact (intrinsicRadius_cross_congruent (L.facet_matches i)).symm
  rwa [heq]

end CycleModelLabels

/-- Geometry at one actual polygon, before any stage-one enumeration. -/
structure LibraryCycleWord.ActualRootFacts (W : LibraryCycleWord)
    (N : LibraryNumericalData) (R : ℝ) : Prop where
  radius_pos : 0 < R
  max_pos : 0 < W.maxRadius N
  max_lt : W.maxRadius N < R
  reciprocal_strict : 1 / R < 1 / W.maxRadius N
  nonflat : W.angleSum N < 2 * Real.pi
  domain : W.Domain N (1 / R)
  root : W.closure N (1 / R) = 0

theorem unitUniform5_actual_library_word {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {k : ℕ} (hG : PolygonFace P G k) (hk : k ≤ 16)
    (N : LibraryNumericalData) (hLIB : LIB N)
    (hcoverage : ∀ K, Facet P K → ∃ n, Congruent K (N.model n)) :
    ∃ W : LibraryCycleWord, W.polygon.val = k ∧ W.Admissible N ∧
      W.ActualRootFacts N (intrinsicRadius P) := by
  obtain ⟨D, L, hD, hC, hF, hclosed, hvalid, hroot, hlower⟩ :=
    unitUniform5_library_cycle hP hG N hLIB hcoverage
  let W : LibraryCycleWord := ⟨⟨k, hD.polygon_three, hk⟩, ⟨D.length, D.length_ge⟩, L.cyclicWord⟩
  have hsum : W.angleSum N < 2 * Real.pi := by
    change L.cyclicWord.angleSum k (intrinsicRadius ∘ N.model)
      (intrinsicRadius ∘ cellTypeModel) < _
    rw [← hC, ← hF, L.finite_angleSum_eq hclosed, L.angle_eq]
    exact hD.perimeter
  have hdom : W.Domain N (1 / intrinsicRadius P) := by
    simpa only [W, LibraryCycleWord.Domain, CyclicWord.domain, finiteClosureDomain, hC, hF]
      using L.finite_domain hclosed hD
  have hr := L.finite_radius_domain hP
  rw [hF] at hr
  refine ⟨W, rfl, ⟨hvalid, ?_⟩,
    ⟨hD.parent_positive, hr.1, hr.2.1, hr.2.2.2, hsum, hdom, hroot⟩⟩
  change (∑ i : Fin D.length, (N.angleBall (L.cyclicWord.facet i) k (L.cyclicWord.cell i)
    (L.cyclicWord.cell (finRotate D.length i))).lower) ≤ _
  rw [L.finite_lowerAngleSum_eq hclosed]
  exact hlower.le

/-- S1 supplies a listed representative and an individual interval
containing the actual root. Flat and endpoint tags are excluded by geometry. -/
theorem S1.actual_root_witness {N : LibraryNumericalData} {S : StageOneNumericalData}
    (hS : S1 N S) {W : LibraryCycleWord} (hW : W.Admissible N)
    {R : ℝ} (hR : W.ActualRootFacts N R) :
    ∃ V ∈ S.listed, ∃ i : Fin (S.roots V).length,
      W.classCode = V.classCode ∧ S.flat V = false ∧ S.degenerate V i = false ∧
      1 / R ∈ (S.roots V)[i].carrier := by
  obtain ⟨V, hV, heq⟩ := hS.complete W hW
  have hmax := LibraryCycleWord.maxRadius_eq_of_class heq N
  have hangle := LibraryCycleWord.angleSum_eq_of_class heq N
  have hroot : V.closure N (1 / R) = 0 := by
    rw [← LibraryCycleWord.closure_eq_of_class heq N]
    exact hR.root
  have hdomain := (LibraryCycleWord.domain_iff_of_class heq N _).mp hR.domain
  have hstrict : 1 / R < 1 / V.maxRadius N := by
    rw [← hmax]
    exact hR.reciprocal_strict
  have hbound := (RationalBall.bounds (hS.reciprocal_enclosed V hV)).2
  obtain ⟨I, hI, hmem⟩ := hS.roots_cover V hV (1 / R)
    ⟨(one_div_pos.mpr hR.radius_pos).le, hstrict.le.trans hbound⟩ hdomain hroot
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hI
  have hi' : (S.roots V)[i] = I := by simpa only [List.get_eq_getElem] using hi
  refine ⟨V, hV, i, heq, ?_, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro ht
    have hf := (hS.flat_exact V hV).mp ht
    rw [← hangle] at hf
    exact (ne_of_lt hR.nonflat) hf
  · apply Bool.eq_false_iff.mpr
    intro ht
    have hd := (hS.degenerate_exact V hV i).mp ht
    have hm : 1 / R ∈ (S.roots V)[i].carrier := by simpa only [hi'] using hmem
    exact (ne_of_lt hstrict) (hd.2.2.2 (1 / R) hm hdomain hroot)
  · simpa only [hi'] using hmem

end Uniform5.Composition
