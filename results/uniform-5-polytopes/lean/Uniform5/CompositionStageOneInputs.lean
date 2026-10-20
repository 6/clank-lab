import Uniform5.CompositionLibraryCycle
import Uniform5.CompositionCyclicMetrics
import Uniform5.CompositionRootIntervals

/-! Exact semantic words and the named stage-one computed input. -/
noncomputable section
namespace Uniform5.Composition
open Set

abbrev LibraryPolygonSize := {k : ℕ // 3 ≤ k ∧ k ≤ 16}
abbrev LibraryCycleLength := {n : ℕ // 3 ≤ n}

instance libraryCycleLength_neZero (n : LibraryCycleLength) : NeZero n.val :=
  ⟨by have := n.property; omega⟩

/-- A raw word retains its representative for the certified numerical test. -/
structure LibraryCycleWord where
  polygon : LibraryPolygonSize
  length : LibraryCycleLength
  word : CyclicWord length.val CanonicalFacetName CellType

abbrev LibraryCycleClass := Σ _ : LibraryPolygonSize,
  (Σ n : LibraryCycleLength, CyclicWord.Class n.val CanonicalFacetName CellType)

namespace LibraryCycleWord
noncomputable def classCode (W : LibraryCycleWord) : LibraryCycleClass :=
  ⟨W.polygon, W.length, Quotient.mk CyclicWord.wordSetoid W.word⟩

noncomputable def closure (W : LibraryCycleWord) (N : LibraryNumericalData) (s : ℝ) : ℝ :=
  W.word.closure W.polygon.val (intrinsicRadius ∘ N.model) (intrinsicRadius ∘ cellTypeModel) s

noncomputable def angleSum (W : LibraryCycleWord) (N : LibraryNumericalData) : ℝ :=
  W.word.angleSum W.polygon.val (intrinsicRadius ∘ N.model) (intrinsicRadius ∘ cellTypeModel)

noncomputable def maxRadius (W : LibraryCycleWord) (N : LibraryNumericalData) : ℝ :=
  W.word.maxRadius (intrinsicRadius ∘ N.model)

noncomputable def lowerAngleSum (W : LibraryCycleWord) (N : LibraryNumericalData) : ℝ :=
  ∑ i, (N.angleBall (W.word.facet i) W.polygon.val (W.word.cell i)
    (W.word.cell (finRotate W.length.val i))).lower

/-- This is the paper's exact numerical pruning predicate. It uses the
exported lower bounds, not an assumed equality with the exact angle sum. -/
noncomputable def Admissible (W : LibraryCycleWord) (N : LibraryNumericalData) : Prop :=
  W.word.Valid (fun f a b => ModelPolygonWord (N.model f) W.polygon.val
    (cellTypeModel a) (cellTypeModel b)) ∧ W.lowerAngleSum N ≤ 2 * Real.pi

/-- The intended finite geometric domain of the closure expression. -/
noncomputable def Domain (W : LibraryCycleWord) (N : LibraryNumericalData) (s : ℝ) : Prop :=
  let ρ := unitPolygonRadius W.polygon.val
  let d := fun i => Real.sqrt ((intrinsicRadius (cellTypeModel (W.word.cell i))) ^ 2 - ρ ^ 2)
  let α := fun i => facetWordAngle W.polygon.val (intrinsicRadius (N.model (W.word.facet i)))
    (intrinsicRadius (cellTypeModel (W.word.cell i)))
    (intrinsicRadius (cellTypeModel (W.word.cell (finRotate W.length.val i))))
  0 < 1 - ρ ^ 2 * s ^ 2 ∧
    (∀ i, 0 < Real.sqrt (1 - cyclePolarCosine ρ (d i) s ^ 2)) ∧
    ∀ i, closureArgument ρ (d i) (d (finRotate W.length.val i)) (α i) s ∈ Icc (-1) 1

end LibraryCycleWord

namespace LibraryCycleClass
noncomputable def closure (c : LibraryCycleClass) (N : LibraryNumericalData) (s : ℝ) : ℝ :=
  CyclicWord.classClosure c.2.2 c.1.val (intrinsicRadius ∘ N.model)
    (intrinsicRadius ∘ cellTypeModel) s

noncomputable def angleSum (c : LibraryCycleClass) (N : LibraryNumericalData) : ℝ :=
  CyclicWord.classAngleSum c.2.2 c.1.val (intrinsicRadius ∘ N.model)
    (intrinsicRadius ∘ cellTypeModel)

noncomputable def maxRadius (c : LibraryCycleClass) (N : LibraryNumericalData) : ℝ :=
  CyclicWord.classMaxRadius c.2.2 (intrinsicRadius ∘ N.model)
end LibraryCycleClass

namespace LibraryCycleWord
theorem closure_eq_of_class {U V : LibraryCycleWord} (h : U.classCode = V.classCode)
    (N : LibraryNumericalData) (s : ℝ) : U.closure N s = V.closure N s :=
  congrArg (fun c => LibraryCycleClass.closure c N s) h

theorem angleSum_eq_of_class {U V : LibraryCycleWord} (h : U.classCode = V.classCode)
    (N : LibraryNumericalData) : U.angleSum N = V.angleSum N :=
  congrArg (fun c => LibraryCycleClass.angleSum c N) h

theorem maxRadius_eq_of_class {U V : LibraryCycleWord} (h : U.classCode = V.classCode)
    (N : LibraryNumericalData) : U.maxRadius N = V.maxRadius N :=
  congrArg (fun c => LibraryCycleClass.maxRadius c N) h
end LibraryCycleWord

/-- Raw stage-one output: no completeness or root property is a data field. -/
structure StageOneNumericalData where
  listed : Finset LibraryCycleWord
  roots : LibraryCycleWord → List ClosedRadiusInterval
  reciprocalBall : LibraryCycleWord → RationalBall
  flat : LibraryCycleWord → Bool
  degenerate : (W : LibraryCycleWord) → Fin (roots W).length → Bool

namespace StageOneNumericalData
noncomputable def count (D : StageOneNumericalData) (p : LibraryCycleWord → Prop) : ℕ := by
  classical
  exact (D.listed.filter p).card

noncomputable def degenerateCount (D : StageOneNumericalData) : ℕ := by
  classical
  exact ∑ W ∈ D.listed,
    (Finset.univ.filter (fun i : Fin (D.roots W).length => D.degenerate W i = true)).card

/-- A certified individual interval contains exactly the endpoint root
in the geometric domain. It is not a claim about every root of its word. -/
noncomputable def EndpointInterval (D : StageOneNumericalData) (N : LibraryNumericalData)
    (W : LibraryCycleWord) (i : Fin (D.roots W).length) : Prop :=
  let e := 1 / W.maxRadius N
  e ∈ (D.roots W)[i].carrier ∧ W.Domain N e ∧ W.closure N e = 0 ∧
    ∀ s ∈ (D.roots W)[i].carrier, W.Domain N s → W.closure N s = 0 → s = e
end StageOneNumericalData

/-- The mathematical output of computation S1, clauses (i)--(iii), over
exact semantic library words. All counts are explicit. Root coverage uses
the extended reciprocal ball and the paper's clipped geometric domain.
The search stops at retained leaves of width below `10⁻²⁰`; that algorithmic
threshold is not a bound on the merged root intervals exported here. -/
structure S1 (N : LibraryNumericalData) (D : StageOneNumericalData) : Prop where
  cycle_count : D.listed.card = 14965
  listed_admissible : ∀ W ∈ D.listed, W.Admissible N
  distinct_classes : ∀ U ∈ D.listed, ∀ V ∈ D.listed,
    U.classCode = V.classCode → U = V
  complete : ∀ W : LibraryCycleWord, W.Admissible N → ∃ V ∈ D.listed, W.classCode = V.classCode
  reciprocal_enclosed : ∀ W ∈ D.listed,
    (D.reciprocalBall W).Contains (1 / W.maxRadius N)
  roots_cover : ∀ W ∈ D.listed, ∀ s ∈ Icc 0 (D.reciprocalBall W).upper,
    W.Domain N s → W.closure N s = 0 → ∃ I ∈ D.roots W, s ∈ I.carrier
  with_roots : D.count (fun W => D.roots W ≠ []) = 14428
  without_roots : D.count (fun W => D.roots W = []) = 537
  flat_exact : ∀ W ∈ D.listed, D.flat W = true ↔ W.angleSum N = 2 * Real.pi
  flat_count : D.count (fun W => D.flat W = true) = 7080
  degenerate_exact : ∀ W ∈ D.listed, ∀ i,
    D.degenerate W i = true ↔ D.EndpointInterval N W i
  degenerate_count : D.degenerateCount = 57

end Uniform5.Composition
