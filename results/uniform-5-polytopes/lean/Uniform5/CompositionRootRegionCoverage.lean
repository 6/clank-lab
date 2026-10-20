import Uniform5.CompositionReciprocalClassHull

/-! The endpoint hull of an overlap component introduces no additional
positive radius. Thus the actual radius classes partition stage-one Omega. -/
noncomputable section
namespace Uniform5.Composition
open Set Classical

/-- A connected walk transports any property preserved by adjacency. -/
private theorem reachable_preserves {ι : Type*} {G : SimpleGraph ι} {p : ι → Prop}
    (step : ∀ a b, G.Adj a b → p a → p b) {a b : ι} (h : G.Reachable a b) :
    p a → p b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons hab w ih => exact fun hp => ih (step _ _ hab hp)

/-- Every positive reciprocal point in a class hull is in one of its
actual retained intervals. Connected intervals cannot leave an internal gap. -/
theorem radiusClassRegion_interval_witness (S : StageOneNumericalData)
    (c : ActiveRootClass S) {R : ℝ} (hR : R ∈ radiusClassRegion S c) :
    ∃ i : RetainedRootIndex S,
      (retainedRootGraph S).connectedComponentMk i = c.val ∧
        R ∈ positiveReciprocalRegion (retainedRootInterval S i) := by
  let M := rootClassOccurrences S c.val
  have hM : M.Nonempty := activeClass_occurrences_nonempty c
  let s := 1 / R
  have hs : 0 < s := one_div_pos.mpr hR.1
  have hlo : (M.image fun i => max 0 (retainedRootInterval S i).lo).min' (hM.image _) ≤ s := hR.2.1
  have hhi : s ≤ (M.image fun i => (retainedRootInterval S i).hi).max' (hM.image _) := hR.2.2
  obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp
    (Finset.min'_mem (M.image fun i => max 0 (retainedRootInterval S i).lo) (hM.image _))
  obtain ⟨j, hj, hej⟩ := Finset.mem_image.mp
    (Finset.max'_mem (M.image fun i => (retainedRootInterval S i).hi) (hM.image _))
  have hic : (retainedRootGraph S).connectedComponentMk i = c.val :=
    (Finset.mem_filter.mp hi).2.1
  have hjc : (retainedRootGraph S).connectedComponentMk j = c.val :=
    (Finset.mem_filter.mp hj).2.1
  by_contra hnone
  have hnot : ∀ k ∈ M, s ∉ (retainedRootInterval S k).carrier := by
    intro k hk hsK
    exact hnone ⟨k, (Finset.mem_filter.mp hk).2.1, hR.1, hsK⟩
  have hilow : (retainedRootInterval S i).lo ≤ s :=
    (le_max_right 0 _).trans (hei ▸ hlo)
  have hibelow : (retainedRootInterval S i).hi < s := by
    by_contra hh
    exact hnot i hi ⟨hilow, le_of_not_gt hh⟩
  let p := fun k : RetainedRootIndex S =>
    (retainedRootGraph S).connectedComponentMk k = c.val ∧
      (retainedRootInterval S k).hi < s
  have step : ∀ a b, (retainedRootGraph S).Adj a b → p a → p b := by
    intro a b hab ha
    have hbc : (retainedRootGraph S).connectedComponentMk b = c.val :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab).symm.trans ha.1
    obtain ⟨r, hra, hrb⟩ := hab.2
    have hbm : b ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbc, r, hrb⟩
    refine ⟨hbc, ?_⟩
    have hbl : (retainedRootInterval S b).lo ≤ s :=
      hrb.2.1.trans (hra.2.2.trans ha.2.le)
    by_contra hh
    exact hnot b hbm ⟨hbl, le_of_not_gt hh⟩
  have hjbelow := reachable_preserves step
    (SimpleGraph.ConnectedComponent.exact (hic.trans hjc.symm)) ⟨hic, hibelow⟩
  exact (not_lt_of_ge (hej ▸ hhi)) hjbelow.2

/-- Class hull membership is precisely membership in a member interval. -/
theorem radiusClassRegion_mem_iff (S : StageOneNumericalData) (c : ActiveRootClass S)
    (R : ℝ) : R ∈ radiusClassRegion S c ↔
      ∃ i : RetainedRootIndex S,
        (retainedRootGraph S).connectedComponentMk i = c.val ∧
          R ∈ positiveReciprocalRegion (retainedRootInterval S i) := by
  constructor
  · exact radiusClassRegion_interval_witness S c
  · rintro ⟨i, hi, hR⟩
    exact radius_mem_classRegion S c hi hR

theorem radiusClassRegion_subset_stageOneOmega (S : StageOneNumericalData)
    (c : ActiveRootClass S) : radiusClassRegion S c ⊆ stageOneOmega S := by
  intro R hR
  obtain ⟨i, _, hi⟩ := radiusClassRegion_interval_witness S c hR
  exact mem_iUnion.mpr ⟨i, hi⟩

/-- Distinct active class regions are disjoint, including at positive endpoints. -/
theorem radiusClassRegion_eq_of_common_radius (S : StageOneNumericalData)
    {c d : ActiveRootClass S} {R : ℝ}
    (hc : R ∈ radiusClassRegion S c) (hd : R ∈ radiusClassRegion S d) : c = d := by
  obtain ⟨i, hi, hRi⟩ := radiusClassRegion_interval_witness S c hc
  obtain ⟨j, hj, hRj⟩ := radiusClassRegion_interval_witness S d hd
  apply Subtype.ext
  exact hi.symm.trans ((retained_class_eq_of_radius S hRi hRj).trans hj)

end Uniform5.Composition
