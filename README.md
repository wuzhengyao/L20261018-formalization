# L20261018 — Chapter 3, Lean 4 formalization

Lean 4 + [mathlib](https://github.com/leanprover-community/mathlib4) formalization of
**Chapter 3** of the paper `L20261018` (*bi-Kummer data, the rank barrier, and the
Hochschild–Serre computation*).  Twelve numbered statements (3.1(1)–3.6) are formalized
as **14 Lean theorems**; the abstract layer lives in `L20261018/A.lean`, the concrete
objects (Kummer classes, crossed products, cup-product transport, local fields) in the
numbered `Hyp*` modules.

Nothing else is needed to read or build this: mathlib is fetched by Lake, and the
TauCeti modules that the development imports are vendored under `TauCeti/`.

## Contents

```
lakefile.toml, lean-toolchain    build configuration (toolchain v4.35.0, mathlib pinned)
L20261018/*.lean                 96 modules: the Chapter-3 development
TauCeti/*.lean                   542 vendored TauCeti modules (Apache-2.0, see TauCeti/NOTICE)
comparator/ch3/                  comparator inputs for Chapter 3: Challenge.lean,
                                 Solution.lean, config.json (14 theorems)
run-comparator.sh                build + run the comparator check of one chapter
scripts/gen-comparator.py        regenerates comparator/ch3/{Challenge,Solution,config.json}
scripts/install-comparator-tools.sh, scripts/validate-comparator-tools.sh
scripts/patches/…                landrun ABI patch (see the install script's header)
```

`L20261018/` is flat on purpose: the modules were developed incrementally as
`Hyp1`, `Hyp2`, … and import each other by those names
(`import L20261018.Hyp22`, …).  `A.lean` holds the abstract statements; the `Hyp*`
files contain the concrete instances and the auxiliary lemmas they need.

## Build

```bash
# toolchain: leanprover/lean4:v4.35.0 (elan installs it from lean-toolchain)
lake exe cache get     # download prebuilt mathlib oleans (recommended)
lake build             # TauCeti (vendored) + L20261018 + comparator/ch3
```

Pins: mathlib `aa35a481e5f0cdb3b04a899ead15d6ca7305a624` (see `lakefile.toml`), Lean
`v4.35.0` (see `lean-toolchain`).  If you already have mathlib checked out at that
commit, you can replace the `[[require]]` block by a `path = "…/mathlib4"` requirement.

## Comparator check

[`comparator`](https://github.com/leanprover/comparator) replays the proof terms in an
independent kernel and checks them against separately generated statements.

```bash
bash scripts/install-comparator-tools.sh   # comparator + lean4export + landrun into .tools/
source .tools/env.sh                       # puts them on PATH
./run-comparator.sh                        # regenerates comparator/ch3, builds, runs comparator
```

Expected last line: `Your solution is okay!`  The two modules `comparator/ch3/Challenge.lean`
and `comparator/ch3/Solution.lean` clone the same declarations out of the imported environment (same
`levelParams`, same `type` expression), so the statements agree by construction; the
challenge side replaces every proof by `sorryAx`, the solution side replays the project's
own proof terms.  `config.json` permits exactly `propext`, `Quot.sound`,
`Classical.choice`.

## Statement map (paper → Lean)

| Paper | Lean declaration (module) |
|---|---|
| 3.1(1) `U ∩ U^⊥ = 0` | `L20261018.lemma_3_1_1_kummer` (`Hyp22`) |
| 3.1(2) `res|_{U^⊥}` injective | `L20261018.BiKummerData.lemma_3_1_2` (`A`); Galois form `lemma_3_1_2_galo` (`Hyp42`) |
| 3.1(3) `rank Φ ≥ 2` | `L20261018.lemma_3_1_3_kummer` (`Hyp22`) |
| 3.2(1) `rank Φ = 2 ⇒ ind ≤ p` | `L20261018.theorem_3_2_1_kummer'` (`Hyp86`) |
| 3.2(2) `ind = p² ⇒ rank Φ ≥ 3` | `L20261018.theorem_3_2_2_kummer'` (`Hyp86`) |
| 3.3(1) `N ⊆ S` | `CrossedProductNrd.hNrd_crossedProduct` (`Hyp23`) + `nrd_inc` (`Hyp21`) |
| 3.3(2) `N ⊆ U^⊥` | `explicitCup_projection_res_right` (`Hyp10`); continuous form in `Hyp11` |
| 3.3(3) `U^⊥ ⊆ R` | `L20261018.lemma_3_3_3_kummer` (`Hyp22`) |
| 3.4 (first three items) | `L20261018.prop_3_4_first_three` (`A`) |
| 3.5(1) | `L20261018.three_five_one_add` (`Hyp12`) + `GaloFive.theorem_3_5_1_galo` (`Hyp13`) |
| 3.5(2) | `L20261018.BiKummerData.theorem_3_5_2` (`A`) |
| 3.6 | `L20261018.BiKummerData.theorem_3_6` (`A`) |

## Status

The development contains no `sorry` and, by the comparator run, every one of the 14
theorems depends only on `propext`, `Classical.choice` and `Quot.sound`.  The abstract
statements (`A.lean`) are the ones to read first: they fix the interfaces
(`BiKummerData`, the Kummer map, `ind`) that the concrete modules instantiate.

## Chapters

| Chapter | Status | Where |
|---|---|---|
| 3 | **included** — 12 statements (3.1–3.6), 14 Lean theorems | `L20261018/`, `comparator/ch3/` |
| 4, 5, … | planned; each will be added once its formalization is complete | future `Hyp*` modules + `comparator/chN/` |

The layout is meant to grow: a new chapter adds its Lean modules under `L20261018/`
(the campaign numbered them consecutively, so imports keep working) and its own
`comparator/chN/` directory; `lakefile.toml` needs no change, and
`./run-comparator.sh chN` runs its check.

Not included: the paper sources (kept in the author's repository), the Chapter-4
development so far, and the campaign's working notes.  `.lake/` and `lake-manifest.json` are
build products and are ignored.

## License

The `L20261018` development: MIT.  The vendored `TauCeti/` files: Apache-2.0 (see
`TauCeti/LICENSE` and `TauCeti/NOTICE`).
