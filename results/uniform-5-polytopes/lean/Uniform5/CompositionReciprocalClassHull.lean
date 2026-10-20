import Uniform5.CompositionFilterClasses

/-! Closed class hulls in reciprocal radius, including the possible zero
endpoint. Positivity of that endpoint is a later conclusion, not an input. -/
noncomputable section
namespace Uniform5.Composition
open Set

abbrev ActiveRootClass (S : StageOneNumericalData) :=
  {c : RootRegionClass S // c ∈ activeRootClasses S}

theorem activeClass_occurrences_nonempty {S : StageOneNumericalData} (c : ActiveRootClass S) :
    (rootClassOccurrences S c.val).Nonempty := by
  classical
  exact (Finset.mem_filter.mp c.property).2

/-- Endpoint hull of the positive parts of every member reciprocal interval.
The lower endpoint can be zero; no positive-endpoint certificate is assumed. -/
noncomputable def reciprocalClassHull (S : StageOneNumericalData) (c : ActiveRootClass S) :
    ClosedRadiusInterval := by
  classical
  let M := rootClassOccurrences S c.val
  have hM := activeClass_occurrences_nonempty c
  let lows := M.image fun i => max 0 (retainedRootInterval S i).lo
  let highs := M.image fun i => (retainedRootInterval S i).hi
  refine ⟨lows.min' (hM.image _), highs.max' (hM.image _), ?_⟩
  obtain ⟨i, hi⟩ := hM
  obtain ⟨R, hR⟩ := (Finset.mem_filter.mp hi).2.2
  have hs : 0 < 1 / R := one_div_pos.mpr hR.1
  exact (Finset.min'_le _ _ (Finset.mem_image_of_mem (fun j =>
      max 0 (retainedRootInterval S j).lo) hi)).trans
    ((max_le hs.le hR.2.1).trans (hR.2.2.trans
      (Finset.le_max' _ _ (Finset.mem_image_of_mem
        (fun j => (retainedRootInterval S j).hi) hi))))

theorem reciprocalClassHull_lo_nonneg (S : StageOneNumericalData) (c : ActiveRootClass S) :
    0 ≤ (reciprocalClassHull S c).lo := by
  classical
  apply (Finset.le_min'_iff _ ((activeClass_occurrences_nonempty c).image
    (fun i => max 0 (retainedRootInterval S i).lo))).mpr
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact le_max_left _ _

theorem reciprocalClassHull_hi_pos (S : StageOneNumericalData) (c : ActiveRootClass S) :
    0 < (reciprocalClassHull S c).hi := by
  classical
  obtain ⟨i, hi⟩ := activeClass_occurrences_nonempty c
  obtain ⟨R, hR⟩ := (Finset.mem_filter.mp hi).2.2
  exact ((one_div_pos.mpr hR.1).trans_le hR.2.2).trans_le
    (Finset.le_max' _ _ (Finset.mem_image_of_mem
      (fun j => (retainedRootInterval S j).hi) hi))

theorem reciprocal_mem_classHull (S : StageOneNumericalData) (c : ActiveRootClass S)
    {i : RetainedRootIndex S} {R : ℝ}
    (hi : (retainedRootGraph S).connectedComponentMk i = c.val)
    (hR : R ∈ positiveReciprocalRegion (retainedRootInterval S i)) :
    1 / R ∈ (reciprocalClassHull S c).carrier := by
  classical
  have hm : i ∈ rootClassOccurrences S c.val :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, R, hR⟩
  constructor
  · exact (Finset.min'_le _ _ (Finset.mem_image_of_mem
      (fun j => max 0 (retainedRootInterval S j).lo) hm)).trans
      (max_le (one_div_pos.mpr hR.1).le hR.2.1)
  · exact hR.2.2.trans (Finset.le_max' _ _ (Finset.mem_image_of_mem
      (fun j => (retainedRootInterval S j).hi) hm))

noncomputable def radiusClassRegion (S : StageOneNumericalData) (c : ActiveRootClass S) : Set ℝ :=
  positiveReciprocalRegion (reciprocalClassHull S c)

theorem radius_mem_classRegion (S : StageOneNumericalData) (c : ActiveRootClass S)
    {i : RetainedRootIndex S} {R : ℝ}
    (hi : (retainedRootGraph S).connectedComponentMk i = c.val)
    (hR : R ∈ positiveReciprocalRegion (retainedRootInterval S i)) :
    R ∈ radiusClassRegion S c := ⟨hR.1, reciprocal_mem_classHull S c hi hR⟩

/-- Once positivity is derived, the class region is the literal closed
radius interval with reciprocal endpoints. -/
theorem radiusClassRegion_eq (S : StageOneNumericalData) (c : ActiveRootClass S)
    (hpos : 0 < (reciprocalClassHull S c).lo) :
    radiusClassRegion S c = (reciprocalRadiusInterval (reciprocalClassHull S c) hpos).carrier :=
  positiveReciprocalRegion_eq _ hpos

end Uniform5.Composition
