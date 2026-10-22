import Statement.CorollaryA
import EKG3.LemmaA

namespace EKG3
open EKG

/-- Inject the exact Haver unpaired set into one block. Natural subtraction
is safe even if the intended block begins below zero: then use `(0,y]`. -/
private theorem unpaired_card_le (s : GreedySeq) (u B : ℕ)
    (hpeak : EKG.priorPeak (earlyEvenCount s) u ≤ B)
    (BT : ℕ → ℕ)
    (hBT : ∀ x y, ((Finset.Ioc x (x+y)).filter Nat.Prime).card ≤ BT y) :
    (unpairedPrimeUps s u).card ≤ BT (3*B+2) := by
  classical
  let x := frontier s u / 2 - (3*B+3)
  let y := 3*B+2
  have hcard : (unpairedPrimeUps s u).card ≤
      ((Finset.Ioc x (x+y)).filter Nat.Prime).card := by
    apply Finset.card_le_card_of_injOn s.a
    · intro i hi
      obtain ⟨hp, hlo, hhi⟩ := lemmaA s u i hi
      obtain ⟨r, hr⟩ := (frontier_spec s u).2.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ?_, hp⟩
      have hp2 := hp.two_le
      dsimp [x, y]
      constructor <;> omega
    · exact fun i _ j _ hij => s.injective hij
  exact hcard.trans (hBT x y)

/-- Strong induction uses `hboot` only at the current frontier `< E1`.
The initial state has count zero, so there is no small-state or `e0` premise. -/
theorem boundedCorollaryA : BoundedCorollaryAStatement := by
  intro s E1 e0 M BT hM hBT hbase hboot u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hu
    by_cases he0 : frontier s u < e0
    · exact hbase u he0
    have hb := hboot (frontier s u) (frontier_spec s u).2.1 (by omega) hu
    by_cases hu0 : u = 0
    · subst u
      rw [FiniteBase.earlyEvenCount_eq s (by omega : 0 < 13)]
      have hz : FiniteBase.earlyCountValue 0 = 0 := by decide
      rw [hz]
      exact Nat.zero_le _
    have hpeak : EKG.priorPeak (earlyEvenCount s) u ≤ M (frontier s u) := by
      apply Finset.sup_le
      intro j hj
      have hju := Finset.mem_range.mp hj
      have hfront := frontier_monotone s (Nat.le_of_lt hju)
      exact (ih j hju (by omega)).trans (hM hfront)
    have hc := unpaired_card_le s u (M (frontier s u)) hpeak BT hBT
    have hee := earlyEvenCount_le_unpaired s u (by omega)
    omega

/-- A finite-prefix version exposing the otherwise unnecessary `Kfin`.
Its two base conditions imply precisely the abstract theorem's `hbase`. -/
theorem boundedCorollaryA_of_finite_bound
    (s : GreedySeq) (E1 e0 Kfin : ℕ) (M BT : ℕ → ℕ)
    (hM : Monotone M)
    (hBT : ∀ x y, ((Finset.Ioc x (x+y)).filter Nat.Prime).card ≤ BT y)
    (hfinite : ∀ u, frontier s u < e0 → earlyEvenCount s u ≤ Kfin)
    (hdom : ∀ e, e < e0 → Kfin ≤ M e)
    (hboot : ∀ e, 2 ∣ e → e0 ≤ e → e < E1 →
      Nat.primeCounting (Nat.sqrt e) + 2 + BT (3*M e+2) ≤ M e) :
    ∀ u, frontier s u < E1 → earlyEvenCount s u ≤ M (frontier s u) :=
  boundedCorollaryA s E1 e0 M BT hM hBT
    (fun u hu => (hfinite u hu).trans (hdom _ hu)) hboot

end EKG3
