import Check
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Inspect transitive dependencies of every declaration in our namespace,
-- including definitions and auxiliary proof declarations, not just the endpoint.
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let isCompilerStage := match name with
      | .str _ last => last.startsWith "_cstage"
      | _ => false
    if (`LitOnlySigma).isPrefixOf name && !isCompilerStage then
      let deps ← Lean.collectAxioms name
      for dep in deps do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dep do
          throwError "Unapproved logical dependency in {name}: {dep}"
      count := count + 1
  if count = 0 then
    throwError "No LitOnlySigma declarations found"
  logInfo m!"PASS dependency audit: {count} declarations; only standard Lean foundations"

/-- info: 'LitOnlySigma.certificate_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LitOnlySigma.certificate_closed
/-- info: 'LitOnlySigma.litOnly_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LitOnlySigma.litOnly_lower
/-- info: 'LitOnlySigma.regularMinimum_le_litOnlyMinimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LitOnlySigma.regularMinimum_le_litOnlyMinimum
/-- info: 'LitOnlySigma.reachable_iff_changing_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LitOnlySigma.reachable_iff_changing_steps
/-- info: 'LitOnlySigma.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LitOnlySigma.counterexample
/-- info: 'LitOnlySigma.not_conjecture5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LitOnlySigma.not_conjecture5
/-- info: 'LitOnlySigma.rejects_deleted_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LitOnlySigma.rejects_deleted_state
