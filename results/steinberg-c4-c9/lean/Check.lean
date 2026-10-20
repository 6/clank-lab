import Steinberg.RotationControls
import Steinberg.Cycles
import Steinberg.Noncolorable

namespace Steinberg

/-- The published graph has a spherical rotation, no simple C4 or C9,
and no proper three-coloring. All three properties concern this one graph. -/
theorem counterexample :
    HasSphericalRotation graph rotation ∧
    (∀ v (p : graph.Walk v v), p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 9) ∧
    IsEmpty (graph.Coloring (Fin 3)) :=
  ⟨has_spherical_rotation, no_forbidden_cycles, not_three_colorable⟩

/-- info: 'Steinberg.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms counterexample

end Steinberg

-- Independent, fully qualified checks of the statement and certificate API.
example : SimpleGraph (Fin 82) := Steinberg.graph

example :
    Steinberg.HasSphericalRotation Steinberg.graph Steinberg.rotation ∧
    (∀ v (p : Steinberg.graph.Walk v v),
      p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 9) ∧
    IsEmpty (Steinberg.graph.Coloring (Fin 3)) := Steinberg.counterexample

example (f : List (List (Nat × Bool))) :
    LocalRup.Unsat f =
      (∀ a : Nat → Bool,
        ¬ (f.all (fun c => c.any (fun l => a l.1 == l.2)) = true)) := rfl

example : ∀ f : List (List (Nat × Bool)), LocalRup.Unsat f →
    (Std.Sat.CNF.mk f.toArray).Unsat := LocalRup.toStd_unsat

example : LocalRup.SymmetryFree.cnf =
    Std.Sat.CNF.mk LocalRup.SymmetryFree.input.toArray := rfl

example : LocalRup.Unsat LocalRup.SymmetryFree.input :=
  LocalRup.SymmetryFree.LeanCertificate.raw_unsat

example : Std.Sat.CNF.Unsat LocalRup.SymmetryFree.cnf :=
  LocalRup.SymmetryFree.LeanCertificate.cnf_unsat

example : Steinberg.computedCNF = LocalRup.SymmetryFree.cnf :=
  Steinberg.computedCNF_eq

namespace Steinberg

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Corrupt the actual symmetry-free certificate by turning its first
addition into an unjustified empty clause while retaining its actual hints. -/
theorem certificate_corruption_rejected :
    LocalRup.stepCheck LocalRup.SymmetryFree.state1
      (.add 737 [] LocalRup.SymmetryFree.hints1) = false := by decide +kernel

/-- info: 'Steinberg.certificate_corruption_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms certificate_corruption_rejected

end Steinberg
