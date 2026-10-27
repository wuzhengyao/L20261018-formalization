import L20261018.A
import L20261018.Hyp22
import L20261018.Hyp86
import L20261018.Hyp23
import L20261018.Hyp21
import L20261018.Hyp10
import L20261018.Hyp12
import L20261018.Hyp13

open Lean Elab Command

/-! Chapter 3 of `L20261018.tex` -- challenge side: every proof replaced by `sorryAx`.
Statements are cloned from the project's own theorems (same `levelParams`, same
`type` expression), so the two modules agree structurally by construction. -/

run_cmd do
  let specs : List (Name × Name) := [
    (`tm_3_1_1, ``L20261018.lemma_3_1_1_kummer),
    (`tm_3_1_2, ``L20261018.BiKummerData.lemma_3_1_2),
    (`tm_3_1_3, ``L20261018.lemma_3_1_3_kummer),
    (`tm_3_2_1, ``L20261018.theorem_3_2_1_kummer'),
    (`tm_3_2_2, ``L20261018.theorem_3_2_2_kummer'),
    (`tm_3_3_1, ``CrossedProductNrd.hNrd_crossedProduct),
    (`tm_nrd_inc, ``CrossedProductNrd.nrd_inc),
    (`tm_3_3_2, ``explicitCup_projection_res_right),
    (`tm_3_3_3, ``L20261018.lemma_3_3_3_kummer),
    (`tm_3_4, ``L20261018.prop_3_4_first_three),
    (`tm_3_5_1a, ``L20261018.three_five_one_add),
    (`tm_3_5_1b, ``GaloFive.theorem_3_5_1_galo),
    (`tm_3_5_2, ``L20261018.BiKummerData.theorem_3_5_2),
    (`tm_3_6, ``L20261018.BiKummerData.theorem_3_6)
  ]
  for (newName, oldName) in specs do
    let env ← getEnv
    let some ci := env.find? oldName | throwError "missing declaration: {oldName}"
    let (levelParams, type, value) ← do
      match ci with
      | .thmInfo ti => pure (ti.levelParams, ti.type, {value})
      | _ => throwError "not a theorem: {oldName}"
    liftCoreM <| addDecl (.thmDecl { name := newName, levelParams := levelParams, type := type, value := value })
