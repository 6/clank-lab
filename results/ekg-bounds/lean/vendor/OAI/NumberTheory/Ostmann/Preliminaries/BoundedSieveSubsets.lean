import Mathlib

namespace OAI

/-! # The retained Euler weights lie at the original integer sieve level -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def boundedSieveSubsets (P : Finset ℕ) (Q : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun U : Finset ℕ => (∏ p ∈ U, p) ≤ Q

end Ostmann

end OAI
