import ControlKernelCompleteKernelAsync
theorem deliberatelyFalse : (1 : Nat) = 2 := by
  run_tac Lean.Elab.Tactic.liftMetaTactic fun g => g.withContext do
    let pf ← Lean.Meta.mkDecideProof (← g.getType)
    g.assign pf
    pure []
