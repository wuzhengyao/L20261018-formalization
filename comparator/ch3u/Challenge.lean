import L20261018

open Lean Elab Command

/-! Chapter 3 of `L20261018.tex` -- challenge side: every proof replaced by `sorry`.
Statements are cloned from the project's own theorems (same `levelParams`, same
`type` expression), so the two modules agree structurally by construction. -/

run_cmd do
  let specs : List (Name × Name) := [
    (`tm_3u_1_1, ``L20261018.lemma_3_1_1_kummer),
    (`tm_3u_1_2, ``RootsOfUnityExists.lemma_3_1_2_galo'),
    (`tm_3u_1_3, ``L20261018.lemma_3_1_3_kummer),
    (`tm_3u_2_1, ``L20261018.theorem_3_2_1_kummer'),
    (`tm_3u_2_2, ``L20261018.theorem_3_2_2_kummer'),
    (`tm_3u_3_1, ``CrossedProductNrd.hNrd_crossedProduct),
    (`tm_3u_3_3, ``L20261018.lemma_3_3_3_kummer),
    (`tm_3u_5_1, ``GaloFive.theorem_3_5_1_galo)
  ]
  for (newName, oldName) in specs do
    let env ← getEnv
    let some ci := env.find? oldName | throwError "missing declaration: {oldName}"
    let (levelParams, type, value) ← do
      match ci with
      | .thmInfo ti => pure (ti.levelParams, ti.type, mkApp2 (mkConst ``sorryAx [0]) ti.type (mkConst ``Bool.true))
      | _ => throwError "not a theorem: {oldName}"
    liftCoreM <| addDecl (.thmDecl { name := newName, levelParams := levelParams, type := type, value := value })
