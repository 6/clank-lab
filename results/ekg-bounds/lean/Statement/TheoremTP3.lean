import Statement.TheoremT
import Statement.PiBoundsP3
import Statement.LemmaD
import Statement.LemmaF

/-! Manuscript `a(n)` is `actualA (n-1)`. Archive state `u` is manuscript
state `t=u+1`; in particular `E(n)` is `frontier canonical (n-1)`.
The seven integer fields are represented by naturals: all are nonnegative
in the checker (coverage, M and domains), so no signed data are discarded. -/
namespace EKG3.P3

def e0 : ℕ := 13328000000
def E1 : ℕ := 10^205
def Kfin : ℕ := 329
def L : ℕ := 16000000000

noncomputable def piU (x : ℝ) : ℝ :=
  if x < 256 then EKG.realPrimeCount x else U3 x
noncomputable def piL (x : ℝ) : ℝ :=
  if x < 256 then EKG.realPrimeCount x else L3 x
noncomputable def bt (y : ℝ) (q : ℕ) : ℝ :=
  (y + (q : ℝ)^2) / (Real.log ((q : ℝ)+1) + 1.07) + piU q

/-- Both independent prefix implementations in finite/runs/ report
maxK = 329 below frontier 14,130,000,000 and
E(16,000,000,000) = 16,230,216,746. Both first reach frontier
14,130,000,000 at manuscript state 13,928,388,828 < L-2, which
supports Fb by monotonicity. Fb remains an explicit computed premise at
E(L-2), archive state L-3. -/
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
  bq : ℕ
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

/-- P3/B3′/L1 row conditions from tail/discharge, including positive
interval width and the integer BT witness domain. Derived expressions
are definitions, not inputs. -/
def Conditions (r : CoverRow) : Prop :=
  r.ea < r.eb ∧
  6*r.M+7 ≤ r.Y ∧ (r.Y : ℝ) < r.S ∧
  3 ≤ r.Q ∧ (r.Q : ℝ) ≤ ((r.Y : ℝ)+1/2)/(2*((r.M : ℝ)+1)) ∧
  15 ≤ r.hc ∧
  (6 ≤ r.bq ∧ r.pU+2+bt (3*(r.M : ℝ)+2) r.bq ≤ r.M) ∧
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
  FiniteFa → FiniteFb → FiniteFc → CertifiedCover → TheoremTConclusion

end EKG3.P3

namespace EKG3
abbrev CertifiedCoverP3 := P3.CertifiedCover
abbrev FiniteFbP3 := P3.FiniteFb
abbrev FiniteFcP3 := P3.FiniteFc

def Conj3OfComputationsStatement : Prop :=
  FiniteFa → FiniteFbP3 → FiniteFcP3 → CertifiedCoverP3 → Conj3Statement
end EKG3
