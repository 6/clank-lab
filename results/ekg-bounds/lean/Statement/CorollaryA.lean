import Statement.LemmaA

namespace EKG3
open EKG

/-- Abstract bounded bootstrap. `Kfin` is already subsumed by `hbase`;
no fixed finite-prefix bound is needed in this statement. -/
def BoundedCorollaryAStatement : Prop :=
  ∀ (s : GreedySeq) (E1 e0 : ℕ) (M BT : ℕ → ℕ), Monotone M →
    (∀ x y, ((Finset.Ioc x (x+y)).filter Nat.Prime).card ≤ BT y) →
    (∀ u, frontier s u < e0 → earlyEvenCount s u ≤ M (frontier s u)) →
    (∀ e, 2 ∣ e → e0 ≤ e → e < E1 →
      Nat.primeCounting (Nat.sqrt e) + 2 + BT (3*M e+2) ≤ M e) →
    ∀ u, frontier s u < E1 → earlyEvenCount s u ≤ M (frontier s u)

end EKG3
