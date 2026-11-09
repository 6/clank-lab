import ABC.Cert

/-!
# The KAM input (K″): its statement

`KAMInput` is the output of the KAM step (steps R1–R7 of the paper's appendix) in graph form. In every
neighbourhood of the certified fixed point there is a positive-measure family of
`P`-invariant closed curves. In a bi-Lipschitz chart `h` around `p` they are radial graphs
`ψ ↦ g(ψ, s)(cos ψ, sin ψ)`, and their label `s` is Lipschitz on their union. The tube proof
(`TubeProof.lean`) takes it as a hypothesis; `ABC.S4.kam_input` (`S4/KAMInput.lean`) proves it
from Pöschel's Theorem A (`ABC/Cited/Poschel.lean`), with the certified facts `CertFacts p` as
a hypothesis rather than the certificate axiom, through Floquet
reduction, the time-periodic Birkhoff normal form and elliptic rescaling (`S4/`).
-/

open MeasureTheory Set Metric

namespace ABC

/-- (K″) at every certified fixed point and in every neighbourhood of it. -/
def KAMInput : Prop :=
  ∀ (p : E 2), CertFacts p → ∀ (δ : ℝ), 0 < δ →
  ∃ (h : OpenPartialHomeomorph (E 2) (E 2)) (ρ L : ℝ) (K : Set ℝ) (g : ℝ → ℝ → ℝ),
    0 < ρ ∧ 0 < L ∧ closedBall (0 : E 2) ρ ⊆ h.source ∧ h 0 = p ∧
    (∀ u ∈ closedBall (0 : E 2) ρ, ∀ v ∈ closedBall (0 : E 2) ρ,
      dist (h u) (h v) ≤ L * dist u v ∧ dist u v ≤ L * dist (h u) (h v)) ∧
    h '' closedBall 0 ρ ⊆ ball p δ ∧
    IsCompact K ∧ 0 < volume K ∧
    (∀ s ∈ K, Continuous (fun ψ => g ψ s) ∧ (∀ ψ, g (ψ + 2 * Real.pi) s = g ψ s) ∧
      ∀ ψ, 0 < g ψ s ∧ g ψ s < ρ) ∧
    (∀ s ∈ K, ∀ s' ∈ K, ∀ ψ ψ' : ℝ,
      |s - s'| ≤ L * dist (polarPt (g ψ s) ψ) (polarPt (g ψ' s') ψ')) ∧
    ∀ s ∈ K, retMap '' (h '' curve g s) = h '' curve g s

end ABC
