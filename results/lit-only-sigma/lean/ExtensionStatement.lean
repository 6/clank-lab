import LitOnlySigma
import Mathlib.Logic.Equiv.Fin.Basic

namespace LitOnlySigma

/-- The three antipodal outer pairs, in the published labeling. -/
def antipodalPair (i : Fin 3) (v : Fin 7) : Prop :=
  v.val = i.val ∨ v.val = i.val + 3

/-- Exactly two entire antipodal pairs; the hub is dark. -/
def TypeA (x : Configuration 7) : Prop :=
  ∃ omitted : Fin 3, ∀ v, x v = true ↔
    ∃ i : Fin 3, i ≠ omitted ∧ antipodalPair i v

/-- All six outer vertices lit, with the hub dark. -/
def TypeB (x : Configuration 7) : Prop :=
  ∀ v, x v = true ↔ v.val < 6

/-- The hub and three cyclically consecutive outer vertices lit. -/
def TypeC (x : Configuration 7) : Prop :=
  ∃ first : Fin 6, ∀ v, x v = true ↔
    v = 6 ∨ ∃ j : Fin 3, v.val = (first.val + j.val) % 6

def ThreeTypes (x : Configuration 7) : Prop := TypeA x ∨ TypeB x ∨ TypeC x

/-- Endpoint frozen before supporting proofs: EXACT orbit, not just containment. -/
def ThreeTypeStatement : Prop :=
  (∀ x, InCertificate x ↔ ThreeTypes x) ∧
  (∀ x, Reachable (litOnlyMove graph) start x ↔ ThreeTypes x) ∧
  (∀ x v, ThreeTypes x → ThreeTypes (litOnlyMove graph x v)) ∧
  TypeA start ∧ lightNumber start = 4 ∧
  Reachable (regularMove graph) start (decode 0)

/-- Independent copies inside each fiber; all base edges become complete cross edges. -/
def fiberVertex {m : ℕ} (v : Fin (7 * m)) : Fin 7 :=
  (finProdFinEquiv.symm v).1

def fiberCopy {m : ℕ} (v : Fin (7 * m)) : Fin m :=
  (finProdFinEquiv.symm v).2

def blowup (m : ℕ) : Graph (7 * m) := fun u v => graph (fiberVertex u) (fiberVertex v)

def uniformLift (m : ℕ) (x : Configuration 7) : Configuration (7 * m) :=
  fun v => x (fiberVertex v)

def uniformStart (m : ℕ) : Configuration (7 * m) := uniformLift m start

/-- No exact graph-wide discrepancy value is asserted, and m is arbitrary positive. -/
def UniformBlowupStatement : Prop := ∀ m : ℕ, 0 < m →
  Undirected (blowup m) ∧ Connected (blowup m) ∧
  (∀ v, blowup m v v = false) ∧
  regularMinimum (blowup m) (uniformStart m) = 0 ∧
  litOnlyMinimum (blowup m) (uniformStart m) = 4 * m ∧
  4 * m ≤ discrepancy (blowup m) ∧ 7 * m < 2 * discrepancy (blowup m) ∧
  (∀ parts, ¬ CompleteMultipartite (blowup m) parts)

end LitOnlySigma
