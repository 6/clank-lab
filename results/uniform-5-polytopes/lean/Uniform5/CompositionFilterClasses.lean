import Uniform5.CompositionLibrarySides
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-! Radius classes and FILTER with exact semantic side requirements. Empty
positive reciprocal regions carry no radius and are omitted from the count. -/
noncomputable section
namespace Uniform5.Composition
open Set

abbrev RootRegionClass (S : StageOneNumericalData) := (retainedRootGraph S).ConnectedComponent

noncomputable def rootRegionClassFintype (S : StageOneNumericalData) :
    Fintype (RootRegionClass S) := Fintype.ofFinite _
attribute [instance] rootRegionClassFintype

noncomputable def rootClassOccurrences (S : StageOneNumericalData) (c : RootRegionClass S) :
    Finset (RetainedRootIndex S) := by
  classical
  exact Finset.univ.filter fun i => (retainedRootGraph S).connectedComponentMk i = c ∧
    (positiveReciprocalRegion (retainedRootInterval S i)).Nonempty

noncomputable def activeRootClasses (S : StageOneNumericalData) : Finset (RootRegionClass S) := by
  classical
  exact Finset.univ.filter fun c => (rootClassOccurrences S c).Nonempty

noncomputable def rootClassCycles (S : StageOneNumericalData) (c : RootRegionClass S) :
    Finset LibraryCycleWord := by
  classical
  exact (rootClassOccurrences S c).image fun i => i.val.1.val

noncomputable def filteredClassCycles (N : LibraryNumericalData) (S : StageOneNumericalData)
    (c : RootRegionClass S) : Finset LibraryCycleWord :=
  (libraryFilterIncidence N).survivors (rootClassCycles S c)

noncomputable def survivingRootClasses (N : LibraryNumericalData) (S : StageOneNumericalData) :
    Finset (RootRegionClass S) := by
  classical
  exact (activeRootClasses S).filter fun c => (filteredClassCycles N S c).Nonempty

/-- Computation FILTER states these two counts; actual geometric survival
is proved separately and is not a field of the computed hypothesis. -/
structure FILTER (N : LibraryNumericalData) (S : StageOneNumericalData) : Prop where
  classes : (activeRootClasses S).card = 4224
  surviving : (survivingRootClasses N S).card = 563

theorem mem_rootClassCycles_of_radius (S : StageOneNumericalData)
    {i : RetainedRootIndex S} {R : ℝ}
    (hR : R ∈ positiveReciprocalRegion (retainedRootInterval S i)) :
    i.val.1.val ∈ rootClassCycles S ((retainedRootGraph S).connectedComponentMk i) := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, R, hR⟩, rfl⟩

theorem rootClassCycles_subset_listed (S : StageOneNumericalData) (c : RootRegionClass S) :
    rootClassCycles S c ⊆ S.listed := by
  classical
  intro W hW
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
  exact i.val.1.property

/-- Every actual root word is represented in the class of any other
interval containing the same radius. No FILTER count is needed. -/
theorem S1.actual_word_in_class {N : LibraryNumericalData} {S : StageOneNumericalData}
    (hS : S1 N S) {W : LibraryCycleWord} (hW : W.Admissible N)
    {R : ℝ} (hR : W.ActualRootFacts N R) {j : RetainedRootIndex S}
    (hj : R ∈ positiveReciprocalRegion (retainedRootInterval S j)) :
    ∃ V ∈ rootClassCycles S ((retainedRootGraph S).connectedComponentMk j),
      W.classCode = V.classCode := by
  obtain ⟨V, hV, i, hcode, hflat, hdeg, hi⟩ := hS.actual_root_witness hW hR
  let q : RetainedRootIndex S := ⟨⟨⟨V, hV⟩, i⟩, hflat, hdeg⟩
  have hq : R ∈ positiveReciprocalRegion (retainedRootInterval S q) := ⟨hR.radius_pos, hi⟩
  have hm := mem_rootClassCycles_of_radius S hq
  rw [retained_class_eq_of_radius S hq hj] at hm
  exact ⟨V, hm, hcode⟩

/-- Once geometric support is proved, the existing finite-filter invariant
retains every actual word. This theorem introduces no survival assumption. -/
theorem supported_words_survive (N : LibraryNumericalData) (S : StageOneNumericalData)
    (c : RootRegionClass S) {T : Set LibraryCycleWord}
    (hT : (libraryFilterIncidence N).Supported T)
    (hsub : T ⊆ (rootClassCycles S c : Set LibraryCycleWord)) :
    T ⊆ (filteredClassCycles N S c : Set LibraryCycleWord) :=
  (libraryFilterIncidence N).supported_subset_survivors hT hsub

end Uniform5.Composition
