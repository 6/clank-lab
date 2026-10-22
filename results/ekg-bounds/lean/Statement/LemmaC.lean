import EKG.HoleCounting

/-! State `u` contains entries `0,...,u`, i.e. manuscript `t=u+1`.
Only states strictly before `u` are bounded. `Clock.holes` is the hole set
in the exact clock, equal to `HoleCounting.holesBelow`. -/
namespace EKG3
open EKG

/-- Local geometric bound for an unused composite. -/
def LemmaC1Statement : Prop :=
  ∀ (s : GreedySeq) (u : ℕ) (M : ℕ → ℕ), Monotone M →
    (∀ w, w < u → earlyEvenCount s w ≤ M (frontier s w)) →
    ∀ h, 15 ≤ h → ¬ h.Prime → h < frontier s u →
      ¬ UsedBefore s.a (u+1) h →
      frontier s u - h ≤
        2 * h.minFac * (Nat.primeCounting (Nat.sqrt h) + M h + 4)

/-- Local bound on exactly the unused composites counted by the clock. -/
def LemmaC2Statement : Prop :=
  ∀ (s : GreedySeq) (u : ℕ) (M : ℕ → ℕ), Monotone M →
    (∀ w, w < u → earlyEvenCount s w ≤ M (frontier s w)) →
    (Clock.holes s u).card ≤ Nat.primeCounting (Nat.sqrt (frontier s u)) *
      (Nat.primeCounting (Nat.sqrt (frontier s u)) + M (frontier s u) + 5)

def LemmaCStatement : Prop := LemmaC1Statement ∧ LemmaC2Statement

end EKG3
