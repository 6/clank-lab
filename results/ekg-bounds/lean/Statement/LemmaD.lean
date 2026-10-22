import EKG.Span

/-! State `u` includes entries `0,...,u`, i.e. `UsedBefore s.a (u+1)`.
The manuscript's state `t` is therefore `u+1`. Integer threshold `e+Y+1`
represents the half-integer level `e+Y+1/2`. -/
namespace EKG3
open EKG

noncomputable def priorPeak (s : GreedySeq) (u : ℕ) : ℕ :=
  (Finset.range (u+1)).sup (earlyEvenCount s)

/-- Indices of the used odd non-tick values strictly above `frontier+Y`.
Injectivity of `s.a` makes its cardinality the requested value count. -/
noncomputable def oddExcess (s : GreedySeq) (u Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (u+1)).filter (fun i =>
    ¬ 2 ∣ s.a i ∧ frontier s u + Y < s.a i ∧ ¬ spanTickValue (s.a i))

noncomputable def roughSet (s : GreedySeq) (u Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (frontier s u + Y) (nonTickTop s u)).filter (fun m =>
    ∀ r : ℕ, r.Prime → r ∣ m → Y+1 ≤ 2*(earlyEvenCount s u+1)*r)

/-- Lemma D in zero-based archive conventions, without analytic hypotheses. -/
def LemmaDStatement : Prop :=
  ∀ (s : GreedySeq) (u Y : ℕ), 6 * priorPeak s u + 7 ≤ Y →
    (oddExcess s u Y).card ≤
      Nat.primeCounting (Nat.sqrt (frontier s u + Y + 1)) + (roughSet s u Y).card

end EKG3
