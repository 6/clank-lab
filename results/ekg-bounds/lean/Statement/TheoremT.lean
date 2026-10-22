/- The P3/B3′/L1 restatement, with the new computed prefix and no
analytic premises, is in `Statement/TheoremTP3.lean`. -/

import Statement.LemmaD
import Statement.LemmaF

/-! Manuscript `a(n)` is `actualA (n-1)`. Archive state `u` is manuscript
state `t=u+1`; in particular `E(n)` is `frontier canonical (n-1)`.
The six integer fields are represented by naturals: all are nonnegative
in the checker (coverage, M and domains), so no signed data are discarded. -/
namespace EKG3

def e0 : ℕ := 2239000000
def E1 : ℕ := 10^205
def Kfin : ℕ := 182
def L : ℕ := 16000000000

noncomputable def dusart65 (x : ℝ) : ℝ :=
  x / Real.log x * (1 + 1.2762 / Real.log x)
noncomputable def dusart67U (x : ℝ) : ℝ :=
  x / Real.log x * (1 + 1 / Real.log x + 2.334 / Real.log x ^ 2)
noncomputable def piL (x : ℝ) : ℝ :=
  x / Real.log x * (1 + 1 / Real.log x + 2 / Real.log x ^ 2)
noncomputable def piU (x : ℝ) : ℝ :=
  if 2953652302 ≤ x then min (dusart65 x) (dusart67U x) else dusart65 x
noncomputable def bt (y : ℝ) : ℝ := 2*y / Real.log y

/-- Dusart 2010, arXiv:1002.0442v1, Theorem 6.9, (6.5) and (6.7), with
corrected thresholds. The printed thresholds 88783 and 2953652287 are refuted
at the threshold itself: π(88783) = 8596 < piL 88783 = 8596.042…, and
π(2953652287) = 142325757 > dusart67U 2953652287 = 142325756.338….
The target's `audits/check_dusart_thresholds.py` checks both witnesses and
that each bound holds at 88789 and 2953652302. -/
def Dusart2010 : Prop :=
  (∀ x : ℝ, 1 < x → EKG.realPrimeCount x ≤ dusart65 x) ∧
  (∀ x : ℝ, 88789 ≤ x → piL x ≤ EKG.realPrimeCount x) ∧
  (∀ x : ℝ, 2953652302 ≤ x → EKG.realPrimeCount x ≤ dusart67U x)

/-- Montgomery–Vaughan, Theorem 2 at modulus 1. -/
def BT : Prop := ∀ x y : ℝ, 0 < x → 1 < y →
  EKG.realPrimeCount (x+y) - EKG.realPrimeCount x < bt y

/-- Arithmetic large sieve, after `G(Q)>log Q`, on exactly Lemma D's
rough set. The interval has N consecutive integers; it may be empty.
Avoidance of residue zero follows from the explicit prime-divisor premise,
not from a further assumption about the sequence. -/
def ArithmeticLargeSieve : Prop :=
  ∀ u Y N Q : ℕ, 3 ≤ Q →
    (∀ m ∈ roughSet EKG.canonical u Y,
      m ≤ EKG.frontier EKG.canonical u + Y + N) →
    (∀ m ∈ roughSet EKG.canonical u Y, ∀ p : ℕ,
      p.Prime → p ≤ Q → ¬ p ∣ m) →
    ((roughSet EKG.canonical u Y).card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ)^2) / Real.log Q

def FiniteFa : Prop := ∀ i : ℕ, i+1 ≤ L →
  (13*(i+1) ≤ 28*EKG.actualA i ∧ 7*EKG.actualA i ≤ 12*(i+1)) ∧
  (13*(i+1) = 28*EKG.actualA i ↔ i+1 = 28) ∧
  (7*EKG.actualA i = 12*(i+1) ↔ i+1 = 7)

def FiniteFb : Prop := e0 ≤ EKG.frontier EKG.canonical (L-3)

def FiniteFc : Prop := ∀ u : ℕ, EKG.frontier EKG.canonical u < e0 →
  EKG.earlyEvenCount EKG.canonical u ≤ Kfin

structure CoverRow where
  ea : ℕ
  eb : ℕ
  M : ℕ
  Y : ℕ
  Q : ℕ
  hc : ℕ
  deriving DecidableEq

namespace CoverRow
noncomputable def S (r : CoverRow) : ℝ :=
  2*((r.M : ℝ)+1)^2 + 2*((r.M : ℝ)+1)*Real.sqrt (((r.M : ℝ)+1)^2+r.eb)
noncomputable def pU (r : CoverRow) : ℝ := piU (Real.sqrt r.eb)
noncomputable def Ostar (r : CoverRow) : ℝ :=
  ((r.Y+1)/2 : ℕ) + piU (Real.sqrt ((r.eb : ℝ)+r.Y+1)) +
    (r.S-r.Y+(r.Q : ℝ)^2)/Real.log r.Q
noncomputable def Hstar (r : CoverRow) : ℝ := r.pU*(r.pU+r.M+5)
noncomputable def Amin (r : CoverRow) : ℝ :=
  piL r.ea - 2*piU ((r.eb : ℝ)/2) + piL ((r.ea : ℝ)/3)
noncomputable def Amax (r : CoverRow) : ℝ :=
  piU r.eb - 2*piL ((r.ea : ℝ)/2) + piU ((r.eb : ℝ)/3)

/-- Exactly the per-row hypotheses of CHAIN.md, plus positive interval
width (coverage check 1). Derived expressions are definitions, not inputs. -/
def Conditions (r : CoverRow) : Prop :=
  r.ea < r.eb ∧
  6*r.M+7 ≤ r.Y ∧ (r.Y : ℝ) < r.S ∧
  3 ≤ r.Q ∧ (r.Q : ℝ) ≤ ((r.Y : ℝ)+1/2)/(2*((r.M : ℝ)+1)) ∧
  15 ≤ r.hc ∧
  r.pU+2+bt (3*(r.M : ℝ)+2) ≤ r.M ∧
  (r.hc : ℝ)+2*Real.sqrt r.hc*(piU (Real.sqrt r.hc)+r.M+4) < r.ea ∧
  (r.M : ℝ)+r.Ostar+1-r.Amin < (r.ea : ℝ)/13 ∧
  r.Amax+r.Hstar+2 < (r.ea : ℝ)/8 ∧
  7*r.S+12*(r.Amax+r.Hstar+4) < 5*(r.ea : ℝ) ∧
  13*((r.eb : ℝ)-r.Amin+r.M+r.Ostar) < 28*(r.hc : ℝ)
end CoverRow

/-- The first row starts at `a`, has M at least `b`, and subsequent rows
abut and have nondecreasing M. The empty tail checks the final endpoint. -/
def CoverChain (a b : ℕ) : List CoverRow → Prop
  | [] => E1 ≤ a
  | r :: rs => r.ea = a ∧ b ≤ r.M ∧ r.Conditions ∧ CoverChain r.eb r.M rs

def CertifiedCover : Prop := ∃ rows : List CoverRow, CoverChain e0 Kfin rows

def TheoremTConclusion : Prop :=
  (∀ i : ℕ, L < i+1 → EKG.frontier EKG.canonical i < E1 →
    13*(i+1) < 28*EKG.actualA i ∧ 7*EKG.actualA i < 12*(i+1)) ∧
  (∀ i : ℕ, L < i+1 → i+1 < 10^203 →
    13*(i+1) < 28*EKG.actualA i ∧ 7*EKG.actualA i < 12*(i+1)) ∧
  (∀ u : ℕ, e0 ≤ EKG.frontier EKG.canonical u →
    EKG.frontier EKG.canonical u < E1 →
    (u : ℝ)+3 < 14*(EKG.frontier EKG.canonical u : ℝ)/13)

def TheoremTStatement : Prop :=
  Dusart2010 → BT → ArithmeticLargeSieve →
  FiniteFa → FiniteFb → FiniteFc → CertifiedCover → TheoremTConclusion

def Conj3Statement : Prop := ∀ i : ℕ,
  (13*(i+1) ≤ 28*EKG.actualA i ∧ 7*EKG.actualA i ≤ 12*(i+1)) ∧
  (13*(i+1) = 28*EKG.actualA i ↔ i+1 = 28) ∧
  (7*EKG.actualA i = 12*(i+1) ↔ i+1 = 7)

def Conj3OfInputsStatement : Prop :=
  Dusart2010 → BT → ArithmeticLargeSieve →
  FiniteFa → FiniteFb → FiniteFc → CertifiedCover →
  RosserSchoenfeld1962 → Conj3Statement

end EKG3
