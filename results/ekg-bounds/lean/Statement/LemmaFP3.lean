import EKG.PrimeEstimates
import EKG.Canonical
import EKG.Frontier

namespace EKG3.P3

/-- The middle-range consequence (T') and its prefix fact.
Archive state `u` is manuscript state `t=u+1`; hence `t+2=u+3`,
and `E(L_T-2)` is archive state `L_T-3`, for `L_T=16000000000`. -/
def MiddleRangeTPrime : Prop :=
  (∀ u : ℕ, 13328000000 ≤ EKG.frontier EKG.canonical u →
    EKG.frontier EKG.canonical u < 10^205 →
    (u : ℝ) + 3 < 14 * (EKG.frontier EKG.canonical u : ℝ) / 13) ∧
  13328000000 ≤ EKG.frontier EKG.canonical (16000000000 - 3)

/-- Lemma F over the actual sequence. Manuscript `a(n)` is archive
`actualA (n-1)`: here the archive index is `i` and manuscript `n=i+1`. -/
def LemmaFStatement : Prop :=
  MiddleRangeTPrime →
  ∀ i : ℕ, 10^156 ≤ i+1 →
    13 * (i+1) < 28 * EKG.actualA i ∧ 7 * EKG.actualA i < 12 * (i+1)

end EKG3.P3
