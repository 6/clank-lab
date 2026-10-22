import EKG.SelfPairing

/-! State `u` contains entries `0,...,u`. Haver's `EKG.priorPeak` is the
supremum over `range u`, strictly before `u`. This differs from the inclusive
`EKG3.priorPeak` used by Lemma D. -/
namespace EKG3
open EKG

/-- The exact Haver unpaired set, including its possible last-tick endpoint. -/
def LemmaAStatement : Prop :=
  ∀ (s : GreedySeq) (u i : ℕ), i ∈ unpairedPrimeUps s u →
    (s.a i).Prime ∧ 2 * s.a i < frontier s u ∧
      frontier s u < 2 * s.a i + 6 * EKG.priorPeak (earlyEvenCount s) u + 6

end EKG3
