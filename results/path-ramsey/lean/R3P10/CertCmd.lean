import Lean
import R3P10.Cert

/-! # `lrat_cube`: a K_18 cube's certificate as a theorem

`lrat_cube name i "P.paths" "P.lrat"` reads the two files, adds their
contents as string definitions `name.paths` and `name.proof`, compiles the
Boolean `name.check := checkCube i name.paths name.proof`, and adds

  `theorem name : UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits (finalCubes.getD i []))`

with proof `checkCube_sound encode_k18 (Lean.ofReduceBool name.check true rfl)`.
The declaration goes straight to the kernel (`addDecl`), which evaluates
`name.check` once with the compiled code; the elaborator does not
evaluate it. File reading is untrusted: only the kernel's verdict on the
resulting terms matters. -/

namespace R3P10

open Lean Elab Command Meta

def addStrDef (n : Name) (s : String) : CoreM Unit := do
  let d : DefinitionVal := { name := n, levelParams := [], type := mkConst ``String,
                              value := mkStrLit s, hints := .opaque, safety := .safe }
  addAndCompile (.defnDecl d)

/-- Add `name.check : Bool := value`, compiled, and the theorem `name`
proved by `sound` applied to `Lean.ofReduceBool name.check true rfl`. -/
def addNativeThm (name : Name) (value : Expr) (sound : Expr) : MetaM Unit := do
  let chk := name ++ `check
  let d : DefinitionVal := { name := chk, levelParams := [], type := mkConst ``Bool,
                              value, hints := .abbrev, safety := .safe }
  addAndCompile (.defnDecl d)
  let tt := mkConst ``Bool.true
  let h := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst chk) tt
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) tt)
  let pf := mkApp sound h
  let ty ← inferType pf
  addDecl (.thmDecl { name, levelParams := [], type := ty, value := pf })

/-- `native_decide_thm name : P` proves the decidable `P` by
`of_decide_eq_true (Lean.ofReduceBool name.check true rfl)` with
`name.check := decide P`, evaluated once by the kernel. -/
elab "native_decide_thm " id:ident " : " t:term : command => do
  let name := (← getCurrNamespace) ++ id.getId
  liftTermElabM do
    let p ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let p ← instantiateMVars p
    let inst ← instantiateMVars (← synthInstance (mkApp (mkConst ``Decidable) p))
    addNativeThm name (mkApp2 (mkConst ``Decidable.decide) p inst)
      (mkApp2 (mkConst ``of_decide_eq_true) p inst)

elab "lrat_cube " id:ident i:num ps:str pf:str : command => do
  let name := (← getCurrNamespace) ++ id.getId
  let paths ← IO.FS.readFile ps.getString
  let proof ← IO.FS.readFile pf.getString
  liftTermElabM do
    addStrDef (name ++ `paths) paths
    addStrDef (name ++ `proof) proof
    let args := #[mkNatLit i.getNat, mkConst (name ++ `paths), mkConst (name ++ `proof)]
    addNativeThm name (mkAppN (mkConst ``checkCube) args)
      (mkAppN (mkConst ``checkCube_sound) (args.push (mkConst `R3P10.encode_k18)))

end R3P10

namespace R3P10
open Lean Elab Command Meta

/-- `lrat_cube_c name i "C.cert"`: as `lrat_cube`, for a compact certificate. -/
elab "lrat_cube_c " id:ident i:num cf:str : command => do
  let name := (← getCurrNamespace) ++ id.getId
  let cert ← IO.FS.readFile cf.getString
  liftTermElabM do
    addStrDef (name ++ `cert) cert
    let args := #[mkNatLit i.getNat, mkConst (name ++ `cert)]
    addNativeThm name (mkAppN (mkConst ``checkCubeC) args)
      (mkAppN (mkConst ``checkCubeC_sound) (args.push (mkConst `R3P10.encode_k18)))

end R3P10

namespace R3P10
open Lean Elab Command Meta

/-- `lrat_unsat name n m F "C.cert"` proves `UnsatWithPaths n m F` from a
compact certificate, by `checkCompact_sound (Lean.ofReduceBool name.check true rfl)`
with `name.check := checkCompact n m F name.cert`. -/
elab "lrat_unsat " id:ident n:num m:num F:term:max cf:str : command => do
  let name := (← getCurrNamespace) ++ id.getId
  let cert ← IO.FS.readFile cf.getString
  liftTermElabM do
    let f ← Term.elabTerm F (some (mkConst ``R3P10.CNF))
    Term.synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    addStrDef (name ++ `cert) cert
    let args := #[mkNatLit n.getNat, mkNatLit m.getNat, f, mkConst (name ++ `cert)]
    addNativeThm name (mkAppN (mkConst ``checkCompact) args)
      (mkAppN (mkConst ``checkCompact_sound) args)

end R3P10

namespace R3P10
open Lean Elab Command Meta

/-- `cube_range name pre a b` proves `∀ i, a ≤ i → i < b → CubeOK i` from the
theorems `pre<i>` (each `CubeOK i` up to unfolding), `a ≤ i < b`, as the term
`range_cons pre<a> (range_cons pre<a+1> (... (range_nil b)))`. -/
elab "cube_range " id:ident pre:ident a:num b:num : command => do
  let ns ← getCurrNamespace
  let name := ns ++ id.getId
  let (a, b) := (a.getNat, b.getNat)
  liftTermElabM do
    let P := mkConst ``CubeOK
    let mut t := mkApp2 (mkConst ``range_nil) P (mkNatLit b)
    for k in (List.range (b - a)).reverse do
      let i := a + k
      let cube := mkConst (ns ++ pre.getId.appendAfter (toString i))
      t := mkAppN (mkConst ``range_cons) #[P, mkNatLit i, mkNatLit b, cube, t]
    let ty ← inferType t
    addDecl (.thmDecl { name, levelParams := [], type := ty, value := t })

end R3P10
