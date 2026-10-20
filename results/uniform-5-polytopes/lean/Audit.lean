import Uniform5
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Inspect the transitive dependencies of every declaration in the project namespace.
run_cmd do
  let env ← getEnv
  let mut count := 0
  let mut state : Lean.CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    if (`Uniform5).isPrefixOf name then
      -- Share the pinned collector's visited set across roots: each checked
      -- kernel declaration is traversed once, while all roots are still audited.
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run state
      state := next
      let ⟨_, deps⟩ := state
      for dep in deps do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dep do
          throwError "Unapproved logical dependency in {name}: {dep}"
      count := count + 1
  if count = 0 then
    throwError "No Uniform5 declarations found"
  logInfo m!"PASS dependency audit: {count} Uniform5 declarations; only standard Lean foundations"

-- Headline theorem audits, in addition to the exhaustive namespace audit.
#print axioms Uniform5.Composition.mainClassification
#print axioms Uniform5.Composition.classification_of_core_inputs
#print axioms Uniform5.Composition.unitUniform5_smallFaces_known
#print axioms Uniform5.Composition.unitUniform5_largeFace_known
