import Uniform5.CompositionActualStageOne

/-! Positive reciprocal regions keep all actual roots without presupposing
that every supplied reciprocal interval has a positive lower endpoint. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def positiveReciprocalRegion (I : ClosedRadiusInterval) : Set ℝ :=
  {R | 0 < R ∧ 1 / R ∈ I.carrier}

theorem positiveReciprocalRegion_eq (I : ClosedRadiusInterval) (hI : 0 < I.lo) :
    positiveReciprocalRegion I = (reciprocalRadiusInterval I hI).carrier := by
  ext R
  constructor
  · rintro ⟨hR, hs⟩
    exact (mem_reciprocalRadiusInterval_iff I hI hR).mpr hs
  · intro hR
    have hp : 0 < R := (reciprocalRadiusInterval_positive I hI).trans_le hR.1
    exact ⟨hp, (mem_reciprocalRadiusInterval_iff I hI hp).mp hR⟩

/-- Reciprocal overlap is witnessed at a strictly positive s. Intervals
meeting only at zero do not intersect at any finite positive radius. -/
theorem positiveReciprocalRegion_overlap (I J : ClosedRadiusInterval) :
    (positiveReciprocalRegion I ∩ positiveReciprocalRegion J).Nonempty ↔
      ∃ s, 0 < s ∧ s ∈ I.carrier ∧ s ∈ J.carrier := by
  constructor
  · rintro ⟨R, hR, hR'⟩
    exact ⟨1 / R, one_div_pos.mpr hR.1, hR.2, hR'.2⟩
  · rintro ⟨s, hs, hI, hJ⟩
    refine ⟨1 / s, ⟨one_div_pos.mpr hs, ?_⟩, ⟨one_div_pos.mpr hs, ?_⟩⟩ <;>
      simpa only [one_div_one_div]

abbrev StageOneRootIndex (S : StageOneNumericalData) :=
  Σ W : {W : LibraryCycleWord // W ∈ S.listed}, Fin (S.roots W.val).length

noncomputable def stageOneRootIndexFintype (S : StageOneNumericalData) :
    Fintype (StageOneRootIndex S) := by
  classical
  unfold StageOneRootIndex
  infer_instance
attribute [instance] stageOneRootIndexFintype

/-- Delete flat words and certified endpoint intervals individually. -/
abbrev RetainedRootIndex (S : StageOneNumericalData) :=
  {i : StageOneRootIndex S // S.flat i.1.val = false ∧ S.degenerate i.1.val i.2 = false}

noncomputable def retainedRootIndexFintype (S : StageOneNumericalData) :
    Fintype (RetainedRootIndex S) := by
  classical
  unfold RetainedRootIndex
  infer_instance
attribute [instance] retainedRootIndexFintype

noncomputable def retainedRootInterval (S : StageOneNumericalData) (i : RetainedRootIndex S) :
    ClosedRadiusInterval := (S.roots i.val.1.val)[i.val.2]

/-- Omega as a set of finite positive radii, with exact reciprocal meaning. -/
noncomputable def stageOneOmega (S : StageOneNumericalData) : Set ℝ :=
  ⋃ i : RetainedRootIndex S, positiveReciprocalRegion (retainedRootInterval S i)

noncomputable def retainedRootGraph (S : StageOneNumericalData) :
    SimpleGraph (RetainedRootIndex S) where
  Adj i j := i ≠ j ∧ (positiveReciprocalRegion (retainedRootInterval S i) ∩
    positiveReciprocalRegion (retainedRootInterval S j)).Nonempty
  symm := by rintro i j ⟨hne, R, hi, hj⟩; exact ⟨hne.symm, R, hj, hi⟩
  loopless := by intro i h; exact h.1 rfl

theorem retained_class_eq_of_radius (S : StageOneNumericalData)
    {i j : RetainedRootIndex S} {R : ℝ}
    (hi : R ∈ positiveReciprocalRegion (retainedRootInterval S i))
    (hj : R ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    (retainedRootGraph S).connectedComponentMk i =
      (retainedRootGraph S).connectedComponentMk j := by
  by_cases hij : i = j
  · rw [hij]
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨hij, R, hi, hj⟩

theorem S1.actual_radius_mem_omega {N : LibraryNumericalData} {S : StageOneNumericalData}
    (hS : S1 N S) {W : LibraryCycleWord} (hW : W.Admissible N)
    {R : ℝ} (hR : W.ActualRootFacts N R) : R ∈ stageOneOmega S := by
  obtain ⟨V, hV, i, _, hflat, hdeg, hi⟩ := hS.actual_root_witness hW hR
  let j : RetainedRootIndex S := ⟨⟨⟨V, hV⟩, i⟩, hflat, hdeg⟩
  exact mem_iUnion.mpr ⟨j, hR.radius_pos, hi⟩

theorem unitUniform5_radius_mem_omega {P G : Set (Space 5)} (hP : UnitUniform 5 P)
    {k : ℕ} (hG : PolygonFace P G k) (hk : k ≤ 16)
    (N : LibraryNumericalData) (S : StageOneNumericalData) (hLIB : LIB N) (hS : S1 N S)
    (hcoverage : ∀ K, Facet P K → ∃ n, Congruent K (N.model n)) :
    intrinsicRadius P ∈ stageOneOmega S := by
  obtain ⟨W, _, hW, hR⟩ := unitUniform5_actual_library_word hP hG hk N hLIB hcoverage
  exact hS.actual_radius_mem_omega hW hR

end Uniform5.Composition
