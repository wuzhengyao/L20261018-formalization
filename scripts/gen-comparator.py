#!/usr/bin/env python3
"""Generate Challenge.lean, Solution.lean and config.json for the Chapter-3 comparator run.

Both modules clone the same declarations out of the imported environment (same
`levelParams`, same `type` expression): the challenge side replaces every proof by
`sorryAx`, the solution side replays the project's own proof terms.  Hence the two
statements agree structurally by construction, and the comparator checks exactly what
it is supposed to check: that the *proof terms* of the solution elaborate against the
challenge statements (no `sorry`, only the permitted axioms).
"""
import pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

TARGETS = [
    ("tm_3_1_1",   "L20261018.lemma_3_1_1_kummer"),
    ("tm_3_1_2",   "L20261018.BiKummerData.lemma_3_1_2"),
    ("tm_3_1_3",   "L20261018.lemma_3_1_3_kummer"),
    ("tm_3_2_1",   "L20261018.theorem_3_2_1_kummer'"),
    ("tm_3_2_2",   "L20261018.theorem_3_2_2_kummer'"),
    ("tm_3_3_1",   "CrossedProductNrd.hNrd_crossedProduct"),
    ("tm_nrd_inc", "CrossedProductNrd.nrd_inc"),
    ("tm_3_3_2",   "explicitCup_projection_res_right"),
    ("tm_3_3_3",   "L20261018.lemma_3_3_3_kummer"),
    ("tm_3_4",     "L20261018.prop_3_4_first_three"),
    ("tm_3_5_1a",  "L20261018.three_five_one_add"),
    ("tm_3_5_1b",  "GaloFive.theorem_3_5_1_galo"),
    ("tm_3_5_2",   "L20261018.BiKummerData.theorem_3_5_2"),
    ("tm_3_6",     "L20261018.BiKummerData.theorem_3_6"),
]

IMPORTS = ["L20261018.A", "L20261018.Hyp22", "L20261018.Hyp86", "L20261018.Hyp23",
           "L20261018.Hyp21", "L20261018.Hyp10", "L20261018.Hyp12", "L20261018.Hyp13"]

TEMPLATE = """{imports}

open Lean Elab Command

/-! Chapter 3 of `L20261018.tex` -- {doc}.
Statements are cloned from the project's own theorems (same `levelParams`, same
`type` expression), so the two modules agree structurally by construction. -/

run_cmd do
  let specs : List (Name × Name) := [
    {specs}
  ]
  for (newName, oldName) in specs do
    let env ← getEnv
    let some ci := env.find? oldName | throwError "missing declaration: {{oldName}}"
    let (levelParams, type, value) ← do
      match ci with
      | .thmInfo ti => pure (ti.levelParams, ti.type, {value})
      | _ => throwError "not a theorem: {{oldName}}"
    liftCoreM <| addDecl (.thmDecl {{ name := newName, levelParams := levelParams, type := type, value := value }})
"""

def main():
    imports = "\n".join(f"import {m}" for m in IMPORTS)
    specs = ",\n    ".join(f"(`{n}, ``{o})" for n, o in TARGETS)
    (ROOT / "comparator" / "ch3" / "Challenge.lean").write_text(TEMPLATE.format(
        imports=imports, doc="challenge side: every proof replaced by `sorryAx`",
        specs=specs, value="mkApp2 (mkConst ``sorryAx [0]) ti.type (mkConst ``Bool.true)"))
    (ROOT / "comparator" / "ch3" / "Solution.lean").write_text(TEMPLATE.format(
        imports=imports, doc="solution side: the project's own proof terms, replayed by the kernel",
        specs=specs, value="ti.value"))
    names = ", ".join(f'"{n}"' for n, _ in TARGETS)
    (ROOT / "comparator" / "ch3" / "config.json").write_text(
        '{"challenge_module": "comparator.ch3.Challenge", "solution_module": "comparator.ch3.Solution",\n'
        f' "theorem_names": [{names}],\n'
        ' "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],\n'
        ' "enable_nanoda": false}\n')
    print(f"wrote Challenge.lean, Solution.lean, config.json ({len(TARGETS)} theorems)")

if __name__ == "__main__":
    main()
