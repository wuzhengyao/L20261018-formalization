import Hyp801
import Hyp803

open Lean Elab Command

/-! Chapter 4 of `L20261018.tex`, **UNCONDITIONAL** level -- solution side: the project's own proof terms, replayed by the kernel.
Statements are cloned from the project's own theorems (same `levelParams`, same
`type` expression), so the two modules agree structurally by construction.
None of them takes a residual-map argument (`d`, `hd_infl`, `hd_cup_pi`):
`d` is *constructed* in `L20261018.exists_residueMap`. -/

run_cmd do
  let specs : List (Name × Name) := [
    (`tm_u_d, ``L20261018.exists_residueMap),
    (`tm_u_trf, ``L20261018.tameResidueFacts_uncond),
    (`tm_u_4_2, ``L20261018.orth_eq_bot_viaResidue),
    (`tm_u_4_3_1, ``L20261018.thm_ramified_1_viaResidue),
    (`tm_u_4_4, ``L20261018.corollary_4_4_viaResidue),
    (`tm_u_hyp, ``L20261018.ch4TameSymbolHyp_viaResidue),
    (`tm_u_disj, ``L20261018.disjoint_viaResidue)
  ]
  for (newName, oldName) in specs do
    let env ← getEnv
    let some ci := env.find? oldName | throwError "missing declaration: {oldName}"
    let (levelParams, type, value) ← do
      match ci with
      | .thmInfo ti => pure (ti.levelParams, ti.type, ti.value)
      | _ => throwError "not a theorem: {oldName}"
    liftCoreM <| addDecl (.thmDecl { name := newName, levelParams := levelParams, type := type, value := value })
