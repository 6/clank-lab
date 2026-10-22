/- Adapted from targets/thomson-10/lp-formal/n10/Thomson10/Definitions.lean (supplied accepted N10 LP proof). N9 design: aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, proof/lean/ThomsonN9/LP/Concrete.lean. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators
noncomputable section
namespace ThomsonN10.Cert.LP
abbrev Point := EuclideanSpace ℝ (Fin 3)
def energy (p : Fin 10 → Point) : ℝ :=
  ∑ i : Fin 10, ∑ j ∈ Finset.univ.filter (fun j : Fin 10 => i < j), ‖p i - p j‖⁻¹
end ThomsonN10.Cert.LP
