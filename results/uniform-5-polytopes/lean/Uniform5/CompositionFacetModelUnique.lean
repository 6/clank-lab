import Uniform5.CompositionPolyhedronModelUnique
import Uniform5.CompositionProductAssociativity

/-! A literal facet-catalogue name determines one intrinsic congruence class. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- Every one of the 214 concrete facet names has a unique whole-body
congruence type. No uniformity, chosen-model agreement, or numerical
certificate premise is required. -/
theorem facetLibraryModel_unique {n : FacetLibraryName} {P : Set E} {Q : Set F}
    (hP : FacetLibraryModel n P) (hQ : FacetLibraryModel n Q) : Congruent P Q := by
  cases n with
  | wythoff d m => exact namedWythoff4Model_unique hP hQ
  | exceptional i =>
    fin_cases i
    · exact congruent_trans hP (congruent_symm hQ)
    · exact congruent_trans hP (congruent_symm hQ)
  | polyhedronPrism i =>
    obtain ⟨A, hA, hPA⟩ := hP
    obtain ⟨B, hB, hQB⟩ := hQ
    have hAB := congruent_product (namedPolyhedronModel_unique hA hB) (congruent_refl unitInterval)
    exact congruent_trans hPA (congruent_trans hAB (congruent_symm hQB))
  | antiprismPrism i => exact congruent_trans hP (congruent_symm hQ)
  | duoprism i => exact congruent_trans hP (congruent_symm hQ)

end Uniform5.Composition
