import Hyp108
import Hyp149
import Hyp710

open Lean Elab Command

/-! Chapter 3 of `L20261018.tex` -- challenge side: every proof replaced by `sorry`.
Statements are cloned from the project's own theorems (same `levelParams`, same
`type` expression), so the two modules agree structurally by construction. -/

run_cmd do
  let specs : List (Name × Name) := [
    (`tm_4_1a, ``L20261018.cup_basis_change),
    (`tm_4_1b, ``L20261018.basis_change_brauer),
    (`tm_4_2, ``L20261018.orth_eq_bot_paper),
    (`tm_4_3_1, ``L20261018.thm_ramified_1_paper),
    (`tm_4_4, ``L20261018.corollary_4_4_paper)
  ]
  for (newName, oldName) in specs do
    let env ← getEnv
    let some ci := env.find? oldName | throwError "missing declaration: {oldName}"
    let (levelParams, type, value) ← do
      match ci with
      | .thmInfo ti => pure (ti.levelParams, ti.type, mkApp2 (mkConst ``sorryAx [0]) ti.type (mkConst ``Bool.true))
      | _ => throwError "not a theorem: {oldName}"
    liftCoreM <| addDecl (.thmDecl { name := newName, levelParams := levelParams, type := type, value := value })
