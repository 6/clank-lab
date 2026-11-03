import GR22.UnitA
import GR22.UnitB
import GR22.UnitC
import GR22.UnitD
import GR22.UnitE
import GR22.Positional
import GR22.Sanity

/-!
# Assembly: Gutiérrez–Rosas Question 1, settled

Discharges the interface hypotheses of units B, C and E with units A and D. The three
endpoint propositions of `GR22.Endpoint` are proved here, together with uniqueness of Schur
expansions (so the hook+column coefficient is well defined) and their existence for every
iterated plethysm (so `Question1` isn't vacuous). `question1Positional` is the positional form of
Question 1 (zeros kept), and `offByOne_false` (in `Sanity.lean`) refutes a shifted reflection.
-/

namespace GR22

theorem fullEndpoint : FullEndpoint :=
  fullEndpoint_of atA_complete atA_plethysm (schur_atA_of atA_complete)

theorem question1 : Question1 := question1_of fullEndpoint

theorem iterated_has_expansion (ns : List ℕ) (hns : ∀ n ∈ ns, 1 ≤ n) :
    ∃ c, SchurExpansion ns.prod (iterated ns) c :=
  iterated_expansion_exists expansionsExist ns hns

theorem question1Positional : Question1Positional := question1Positional_of fullEndpoint

end GR22
