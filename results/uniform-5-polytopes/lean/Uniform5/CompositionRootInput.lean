import Uniform5.CompositionSignatures
import Uniform5.CompositionClosureEven

/-! ROOT over the whole surviving class, with an edge of the actual
signature as its witness. No shape uniqueness is included. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Computation ROOT: a signature edge has exactly one zero on the whole
reciprocal class interval, nonzero opposite endpoint signs, and derivative
excluding zero throughout that interval. The 629 count belongs to S2. -/
structure ROOT (N : LibraryNumericalData) (S : StageOneNumericalData)
    (T : StageTwoNumericalData S) : Prop where
  edge_root : ∀ c, c.val ∈ survivingRootClasses N S →
    ∀ (σ : VertexFigureSignature), σ ∈ T.signatures c →
    ∃ W ∈ σ.edges,
      W.closure N (reciprocalClassHull S c).lo *
        W.closure N (reciprocalClassHull S c).hi < 0 ∧
      (∀ s ∈ (reciprocalClassHull S c).carrier, deriv (W.closure N) s ≠ 0) ∧
      ∃! s, s ∈ (reciprocalClassHull S c).carrier ∧ W.closure N s = 0

namespace ROOT
variable {N : LibraryNumericalData} {S : StageOneNumericalData}
  {T : StageTwoNumericalData S} (hROOT : ROOT N S T)
include hROOT

/-- ROOT itself rules out a zero lower reciprocal endpoint for a class
carrying a listed signature. No endpoint positivity input is added. -/
theorem class_lower_pos (c : ActiveRootClass S) (hc : c.val ∈ survivingRootClasses N S)
    {σ : VertexFigureSignature}
    (hσ : σ ∈ T.signatures c) : 0 < (reciprocalClassHull S c).lo := by
  obtain ⟨W, _, _, hd, _⟩ := hROOT.edge_root c hc σ hσ
  exact class_lower_pos_of_derivative_exclusion S c W N hd

theorem class_radius_interval (c : ActiveRootClass S) (hc : c.val ∈ survivingRootClasses N S)
    {σ : VertexFigureSignature}
    (hσ : σ ∈ T.signatures c) :
    radiusClassRegion S c =
      (reciprocalRadiusInterval (reciprocalClassHull S c) (hROOT.class_lower_pos c hc hσ)).carrier :=
  radiusClassRegion_eq S c (hROOT.class_lower_pos c hc hσ)

/-- Two realizations with the listed signature and their actual closure
equations have equal radii. This does not identify their geometric shapes. -/
theorem radius_unique (c : ActiveRootClass S) (hc : c.val ∈ survivingRootClasses N S)
    {σ : VertexFigureSignature}
    (hσ : σ ∈ T.signatures c) {R R' : ℝ}
    (hR : R ∈ radiusClassRegion S c) (hR' : R' ∈ radiusClassRegion S c)
    (hσR : σ.RadiusCompatible N R) (hσR' : σ.RadiusCompatible N R') : R = R' := by
  obtain ⟨W, hW, _, _, s, _, hs⟩ := hROOT.edge_root c hc σ hσ
  have he : 1 / R = 1 / R' :=
    (hs _ ⟨hR.2, hσR W hW⟩).trans (hs _ ⟨hR'.2, hσR' W hW⟩).symm
  simpa only [one_div_one_div] using congrArg (fun x : ℝ => 1 / x) he

end ROOT
end Uniform5.Composition
