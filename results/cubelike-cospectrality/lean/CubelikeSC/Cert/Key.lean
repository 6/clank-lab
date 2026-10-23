import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Powerset
import CubelikeSC.Cert.Defs

/-!
# The cosets and the key of a case

`caseCoset n B t u` is coset `u` of the case `(n, B, t)` in the checker's
format; the key is coset `0` followed by the other seven sorted by `(μ_u, r_u)`.
`covered` looks the key up among the certificate entries for `n`. This module
imports little, so the kernel cover checks that use it stay small.
-/

namespace CubelikeSC.Cert

open CubelikeSC

/-- The coset `u` of the case `(n, B, t)`. -/
def caseCoset (n : ℕ) (B : Finset (Fin 8)) (t : Fin 8) (u : Fin 8) : Coset :=
  if u = 0 then (true, 16 * (B.card : ℤ) - n, (n : ℤ) % 4)
  else (false, mu 3 B u, ((n : ℤ) - 2 * (bdot 3 u t : ℤ)) % 4)

def allU : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Order of the sorted keys: by `μ`, then by `r` (as in the certificate file). -/
def keyLe (x y : Coset) : Prop := x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 ≤ y.2.2)

instance : DecidableRel keyLe := fun x y => by unfold keyLe; infer_instance

def tailU : List (Fin 8) := [1, 2, 3, 4, 5, 6, 7]

/-- The key of the case `(n, B, t)`. -/
def caseKey (n : ℕ) (B : Finset (Fin 8)) (t : Fin 8) : List Coset :=
  caseCoset n B t 0 :: (tailU.map (caseCoset n B t)).insertionSort keyLe

/-- The case `(n, B, t)` finds a certificate entry. -/
def covered (certs : ℕ → List Entry) (n : ℕ) (B : Finset (Fin 8)) (t : Fin 8) : Bool :=
  (certs n).any fun e => e.1 == n && e.cosets == caseKey n B t

end CubelikeSC.Cert
