import Mathlib

namespace OAI

/-! # Exact residue decompositions of the original giant sums -/

namespace Ostmann
open scoped BigOperators Classical

def reducedResidues (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => a.Coprime q)

end Ostmann

end OAI
