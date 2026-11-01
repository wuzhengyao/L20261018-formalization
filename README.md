# L20261018 — Chapters 3 & 4, Lean 4 (minimal snapshot)

Source-closed snapshot of the Lean 4 formalisation of chapters 3–4 of `L20261018.tex`,
checked with the official `comparator`. mathlib is pinned in `lakefile.toml`, TauCeti is
vendored (`TauCeti/`, Apache-2.0); nothing else is needed.

## Finding a result

Four entry points, in the order that usually works:

1. **`DECLARATIONS.md`** — every declaration, its module and line. Ctrl-F the declaration
   name or a keyword, read off the module, open it. When a module formalises a specific
   item of the paper, its `paper` column carries the `@source` locator (e.g.
   `lem:ramified-vanishing`).
2. **The directory indexes** — [`L20261018/README.md`](L20261018/README.md) maps the paper's
   own items onto modules and lists what each comparator group actually re-checks.  Every
   directory has a `README.md` listing its modules in proof order, with the declarations each
   one contributes.
3. **The module path** — the directory is the paper's own chapter/section, the file name is
   `StepNNN_<what the step proves>`. The numbers are order preserving within a directory, so
   reading `Ch4/Step001…` upwards reads chapter 4's proof in the order it was built.
4. **`RENAME-MAP.tsv`** — the historical `HypNNN` module names onto this layout (old module,
   old file, new module, new file, size, paper locator, heading). The Lean *docstrings* still
   refer to the campaign's own `HypNNN` labels; resolve one with
   `grep -P '\tHyp161\t' RENAME-MAP.tsv`, which gives the module the label now lives in.

No module was merged into another: one module per proof step, as before the reorganisation;
only names and locations changed. The invariant that was checked is that the set of
`(declaration, line)` pairs is *identical* before and after (2 636 of them).

Merging each directory into one module was tried and does not work: the topic directories are
not dependency layers, so the merged modules would import each other in a cycle (19 of the 20
directories form one strongly connected component of the import graph). `scripts/dependency-layers.py`
prints that verdict with witness modules; `scripts/merge-directory.py` is the merge tool that a
cycle-free group would use, and it records the scope rules a merge has to respect.

## Chapter 4 — unconditional

```bash
lake exe cache get          # once: prebuilt mathlib oleans
./run-comparator.sh ch4u    # → Your solution is okay!
```

`comparator/ch4u` checks 7 declarations:

| paper | declaration |
|---|---|
| `prop:prelim-residue`(1) | `exists_residueMap` — `d` is **constructed**, not assumed |
| " | `tameResidueFacts_uncond` |
| 4.2 `lem:ramified-vanishing` | `orth_eq_bot_viaResidue` |
| 4.3(1) `thm:ramified` | `thm_ramified_1_viaResidue` |
| 4.4 | `corollary_4_4_viaResidue` |
| chapter-4 named slot | `ch4TameSymbolHyp_viaResidue`, `disjoint_viaResidue` |

**Unconditional** = none of them takes a residual map (`d`, `hd_infl`, `hd_cup_pi`) as an
argument; `d` is built inside. They quantify over arbitrary `a₁ a₂ : GaloBase.V`, not just
Kummer classes of field elements, and the hypotheses left are the paper's own:
`char K ≠ p`, `p ≠ 2`, `v(π) = 1`, `(a₁)∪(a₂) ≠ 0`, `v̄|_U ≠ 0`.

## Chapter 3

```bash
./run-comparator.sh ch3u    # 8 declarations: the paper's own statements, unconditional
./run-comparator.sh         # 14 declarations: also the general algebraic layer
```

`ch3u` is the chapter's own statements, and they are unconditional at the paper's hypothesis
level: the abstract hypotheses of the source development are all discharged — `hker` by
`RootsOfUnityExists.lemma_3_1_2_galo'`, `ind`+`hind` by `H2Bridge.hind_kummer`, `hNrd` by
`hNrd_crossedProduct` (crossed products). What is left are the paper's own hypotheses
(`p` odd, `(a₁)∪(a₂) ≠ 0`). The default `ch3` list additionally covers the general algebraic
layer (`BiKummerData`, `three_five_one_add`, the two short exact sequences), where the
carriers are parameters by design.

## Library layout

The directory tree follows the paper: `Ch2` is its section 2 (preliminaries), `Ch3` and `Ch4`
are sections 3 and 4, `Infra` is the general tooling that no single paper statement owns, and
`Witness` collects the concrete fields used to discharge the nonemptiness obligations.

```
L20261018/
  Core/                      carriers of the paper's objects, master abstract statements
  Ch2/Brauer/                sec. 2.1  central simple algebras, Brauer group, crossed/symbol algebras
  Ch2/Kummer/                sec. 2.2  Kummer theory, cup products, the cyclic norm criterion
  Ch2/Hensel/Valuation/      sec. 2.4  valuations, integrality, the uniformizer, Hensel
  Ch2/Hensel/ResidueMap/     sec. 2.4  the residue map, its exact sequence, (R1) and (R2)
  Ch2/Hensel/TameSymbol/     sec. 2.4  the tame symbol and the Merkurjev-Suslin closure
  Ch2/Hensel/Inertia/        sec. 2.4  inertia, K_nr, the cohomological dimension of I
  Ch2/Hensel/UnitsCupVanish/ sec. 2.4  the named hypothesis `UnitsCupVanish` and its discharge
  Ch2/Rost/                  sec. 2.5  Rost invariant, Suslin groups, cohomological dimension
  Ch3/BiKummer/              sec. 3.1  the bi-Kummer structure, the rank barrier, the norm image
  Ch3/NormImage/             sec. 3.2  the norm image sequence, the dimension formula, 3.6
  Ch4/                       sec. 4    Hensel valuations and ramification in the first slot
  Witness/                   concrete witnesses: Q_7, F_7((t)), explicit models
  Infra/Cohomology/          general cohomology infrastructure; the paper's sec. 2.3
                             Hochschild-Serre tooling lives in these five directories
  Infra/Cohomology/Boundary/     the Hochschild-Serre boundary map, assembled
  Infra/Cohomology/Conjugation/  conjugation invariance of H¹(I, μ_p)
  Infra/Cohomology/Coinduced/    coinduced modules, invariants, GS (6.17)
  Infra/Cohomology/ResidueLES/   the continuous residue long exact sequence
  Infra/Galois/              absolute Galois group carriers and subgroup plumbing
  Infra/Algebra/             general algebra: linear algebra, group theory, adjoin-root tooling
L20261018.lean               root module: imports every submodule
```

## Other files

* **`DECLARATIONS.md`** — every declaration, its module, line and paper item.  Generated by
  `python3 scripts/gen-declarations.py` (`--check` to verify it is current).
* **`L20261018/README.md`** and one `README.md` per directory — the paper→module map and the
  per-directory module lists.  Generated by `python3 scripts/gen-directory-index.py`; it
  fails if a comparator target is not a declaration of the development.
* **`RENAME-MAP.tsv`** — the historical-name map, generated by the rename pass.
* **`WORKFLOW.md`** — the formalisation workflow distilled from this project (reusable).
* **`comparator/`** — `{ch3, ch3u, ch4u}/{Challenge,Solution}.lean` + `config.json`; all
  comparator sources import the root module `L20261018`.
* **`lakefile.toml`** — mathlib pinned to `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`.
  Its `L20261018` stanza lists `globs = ["L20261018", "L20261018.+"]` — the bare name is
  needed because the root module `L20261018.lean` exists.

All three groups were rebuilt from these sources and pass (Lean `v4.35.0`, mathlib
`aa35a481`). If that exact mathlib commit is already built on your machine, the repository
compiles fully offline; one command makes the two edits that takes (the `require` stanza and a
path `lake-manifest.json`) after checking the toolchain and the pin:

```bash
python3 scripts/use-local-mathlib.py on /path/to/mathlib4    # → lake build works offline
python3 scripts/use-local-mathlib.py off                    # restore the committed lakefile
```

`lakefile.toml` is tracked, so do not commit the `on` state.

One command runs every gate -- build, the three comparator groups, the toolchain self-test
and the generated documentation -- and prints PASS/FAIL per gate:

```bash
bash scripts/check-all.sh          # ~15 min from cold;  --fast for the doc gates only
```

`TauCeti/` is Apache-2.0 (see `TauCeti/NOTICE`); the `L20261018/` sources are part of the
paper's formalisation and carry no separate licence.
