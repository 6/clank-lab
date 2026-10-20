import Uniform5.CompositionTypeIFiniteLabels

/-! The actual outside-partner neighbor lists used by the finite paired
case arguments, derived from complete tetrahedron coverage. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)

private theorem five_tetrahedra_neighbors (hlen : D.length = 3) (j : Fin D.length)
    (w : Space 5) :
    (∃ i : Fin D.length,
      T.pairedFiveLabels j 4 ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
      w ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
      T.pairedFiveLabels j 4 ≠ w) ↔
    w = T.pairedFiveLabels j 0 ∨ w = T.pairedFiveLabels j 1 ∨
      w = T.pairedFiveLabels j 2 ∨ w = T.pairedFiveLabels j 3 := by
  let p := T.pairedFiveLabels j
  have he (a b : Fin 5) : p a = p b ↔ a = b := p.injective.eq_iff
  have h0 : T.a = p 0 := rfl
  have h1 : T.b = p 1 := rfl
  have h2 : T.lateral j = p 2 := rfl
  have h3 : T.lateral (finRotate D.length j) = p 3 := rfl
  have h4 : T.lateral (finRotate D.length (finRotate D.length j)) = p 4 := rfl
  change (∃ i, p 4 ∈ _ ∧ w ∈ _ ∧ p 4 ≠ w) ↔ w = p 0 ∨ w = p 1 ∨ w = p 2 ∨ w = p 3
  constructor
  · rintro ⟨i, hz, hw, hne⟩
    rcases finRotate_three_enumeration hlen j i with rfl | rfl | rfl
    · simp only [h0, h1, h2, h3, Set.mem_insert_iff, Set.mem_singleton_iff, he, Fin.reduceEq, or_self] at hz
    · simp only [h0, h1, h3, h4, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inr hw))
      · exact (hne hw.symm).elim
    · rw [finRotate_three_closed hlen] at hw
      simp only [h0, h1, h2, h4, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact (hne hw.symm).elim
      · exact Or.inr (Or.inr (Or.inl hw))
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨finRotate D.length j, ?_⟩
      simp [h0, h1, h3, h4, he, Fin.reduceEq]
    · refine ⟨finRotate D.length j, ?_⟩
      simp [h0, h1, h3, h4, he, Fin.reduceEq]
    · refine ⟨finRotate D.length (finRotate D.length j), ?_⟩
      rw [finRotate_three_closed hlen]
      simp [h0, h1, h2, h4, he, Fin.reduceEq]
    · refine ⟨finRotate D.length j, ?_⟩
      simp [h0, h1, h3, h4, he, Fin.reduceEq]

private theorem six_tetrahedra_neighbors_4 (hlen : D.length = 4) (j : Fin D.length)
    (w : Space 5) :
    (∃ i : Fin D.length,
      T.pairedSixLabels hlen j 4 ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
      w ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
      T.pairedSixLabels hlen j 4 ≠ w) ↔
    w = T.pairedSixLabels hlen j 0 ∨ w = T.pairedSixLabels hlen j 1 ∨ w = T.pairedSixLabels hlen j 3 ∨ w = T.pairedSixLabels hlen j 5 := by
  let p := T.pairedSixLabels hlen j
  have he (a b : Fin 6) : p a = p b ↔ a = b := p.injective.eq_iff
  have h0 : T.a = p 0 := rfl
  have h1 : T.b = p 1 := rfl
  have h2 : T.lateral (j) = p 2 := rfl
  have h3 : T.lateral (finRotate D.length j) = p 3 := rfl
  have h4 : T.lateral (finRotate D.length (finRotate D.length j)) = p 4 := rfl
  have h5 : T.lateral (finRotate D.length (finRotate D.length (finRotate D.length j))) = p 5 := rfl
  change (∃ i, p 4 ∈ _ ∧ w ∈ _ ∧ p 4 ≠ w) ↔ w = p 0 ∨ w = p 1 ∨ w = p 3 ∨ w = p 5
  constructor
  · rintro ⟨i, hz, hw, hne⟩
    rcases finRotate_four_enumeration hlen j i with rfl | rfl | rfl | rfl
    · simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff, he, Fin.reduceEq, or_self] at hz
    · simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw | hw
      · exact Or.inl (hw)
      · exact Or.inr (Or.inl (hw))
      · exact Or.inr (Or.inr (Or.inl (hw)))
      · exact (hne hw.symm).elim
    · simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw | hw
      · exact Or.inl (hw)
      · exact Or.inr (Or.inl (hw))
      · exact (hne hw.symm).elim
      · exact Or.inr (Or.inr (Or.inr (hw)))
    · rw [finRotate_four_closed hlen] at hz hw
      simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff, he, Fin.reduceEq, or_self] at hz
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨finRotate D.length j, ?_⟩
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]
    · refine ⟨finRotate D.length j, ?_⟩
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]
    · refine ⟨finRotate D.length j, ?_⟩
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]
    · refine ⟨finRotate D.length (finRotate D.length j), ?_⟩
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]

private theorem six_tetrahedra_neighbors_5 (hlen : D.length = 4) (j : Fin D.length)
    (w : Space 5) :
    (∃ i : Fin D.length,
      T.pairedSixLabels hlen j 5 ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
      w ∈ ({T.a, T.b, T.lateral i, T.lateral (finRotate D.length i)} : Set (Space 5)) ∧
      T.pairedSixLabels hlen j 5 ≠ w) ↔
    w = T.pairedSixLabels hlen j 0 ∨ w = T.pairedSixLabels hlen j 1 ∨ w = T.pairedSixLabels hlen j 4 ∨ w = T.pairedSixLabels hlen j 2 := by
  let p := T.pairedSixLabels hlen j
  have he (a b : Fin 6) : p a = p b ↔ a = b := p.injective.eq_iff
  have h0 : T.a = p 0 := rfl
  have h1 : T.b = p 1 := rfl
  have h2 : T.lateral (j) = p 2 := rfl
  have h3 : T.lateral (finRotate D.length j) = p 3 := rfl
  have h4 : T.lateral (finRotate D.length (finRotate D.length j)) = p 4 := rfl
  have h5 : T.lateral (finRotate D.length (finRotate D.length (finRotate D.length j))) = p 5 := rfl
  change (∃ i, p 5 ∈ _ ∧ w ∈ _ ∧ p 5 ≠ w) ↔ w = p 0 ∨ w = p 1 ∨ w = p 4 ∨ w = p 2
  constructor
  · rintro ⟨i, hz, hw, hne⟩
    rcases finRotate_four_enumeration hlen j i with rfl | rfl | rfl | rfl
    · simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff, he, Fin.reduceEq, or_self] at hz
    · simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff, he, Fin.reduceEq, or_self] at hz
    · simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw | hw
      · exact Or.inl (hw)
      · exact Or.inr (Or.inl (hw))
      · exact Or.inr (Or.inr (Or.inl (hw)))
      · exact (hne hw.symm).elim
    · rw [finRotate_four_closed hlen] at hz hw
      simp only [h0, h1, h2, h3, h4, h5, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw | hw | hw
      · exact Or.inl (hw)
      · exact Or.inr (Or.inl (hw))
      · exact (hne hw.symm).elim
      · exact Or.inr (Or.inr (Or.inr (hw)))
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨finRotate D.length (finRotate D.length j), ?_⟩
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]
    · refine ⟨finRotate D.length (finRotate D.length j), ?_⟩
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]
    · refine ⟨finRotate D.length (finRotate D.length j), ?_⟩
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]
    · refine ⟨finRotate D.length (finRotate D.length (finRotate D.length j)), ?_⟩
      rw [finRotate_four_closed hlen]
      simp [h0, h1, h2, h3, h4, h5, he, Fin.reduceEq]

theorem paired_k3_outside_neighbors
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 3) (j : Fin D.length)
    (hz : T.pairedFiveLabels j 4 ∉ actualPolygonFanVertices hP A v) (w : Space 5) :
    Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (T.pairedFiveLabels j 4) w ↔
    w = T.pairedFiveLabels j 0 ∨ w = T.pairedFiveLabels j 1 ∨
      w = T.pairedFiveLabels j 2 ∨ w = T.pairedFiveLabels j 3 := by
  rw [T.outside_partner_edge_iff classification3D classification4D N S hLIB hS1 hB2
    hP hG hn hvG A hcover hz]
  exact T.five_tetrahedra_neighbors hlen j w

theorem paired_k4_outside_neighbors_4
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 4) (j : Fin D.length)
    (hz : T.pairedSixLabels hlen j 4 ∉ actualPolygonFanVertices hP A v) (w : Space 5) :
    Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (T.pairedSixLabels hlen j 4) w ↔
    w = T.pairedSixLabels hlen j 0 ∨ w = T.pairedSixLabels hlen j 1 ∨ w = T.pairedSixLabels hlen j 3 ∨ w = T.pairedSixLabels hlen j 5 := by
  rw [T.outside_partner_edge_iff classification3D classification4D N S hLIB hS1 hB2
    hP hG hn hvG A hcover hz]
  exact T.six_tetrahedra_neighbors_4 hlen j w

theorem paired_k4_outside_neighbors_5
    (classification3D : CitedClassification3D) (classification4D : CitedClassification4D)
    (N : LibraryNumericalData) (S : StageOneNumericalData)
    (hLIB : LIB N) (hS1 : S1 N S) (hB2 : CaseB.B2 (stageOneOmega S))
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n) (hn : 17 ≤ n)
    (hvG : v ∈ G.extremePoints ℝ) {H : Set (Space 5)} (A : ActualPolygonCycle P H)
    (hcover : TwoLargeFacesCoverAt P v G H) (hlen : D.length = 4) (j : Fin D.length)
    (hz : T.pairedSixLabels hlen j 5 ∉ actualPolygonFanVertices hP A v) (w : Space 5) :
    Edge (vertexFigure P v (vertexCentroid (vertices P (uniform_finitePolytope hP.1))))
      (T.pairedSixLabels hlen j 5) w ↔
    w = T.pairedSixLabels hlen j 0 ∨ w = T.pairedSixLabels hlen j 1 ∨ w = T.pairedSixLabels hlen j 4 ∨ w = T.pairedSixLabels hlen j 2 := by
  rw [T.outside_partner_edge_iff classification3D classification4D N S hLIB hS1 hB2
    hP hG hn hvG A hcover hz]
  exact T.six_tetrahedra_neighbors_5 hlen j w

end Uniform5.Composition.TypeIFanChart
