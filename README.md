# L20261018 — Chapters 3 & 4, Lean 4 formalisation (minimal snapshot)

This repository is a **minimal, source-closed** snapshot of the Lean 4 formalisation of
Chapters 3 and 4 of the paper `L20261018.tex`. It is extracted from a larger private
development (the campaign project); everything needed to build and to run the
**comparator** check is vendored here.

## What is covered

### Chapter 3 — 14 theorems (`comparator/ch3`)

`3.1(1)(2)(3)`, `3.2(1)(2)`, `3.3(1)(2)(3)`, `3.4`,
`3.5(1)` (abstract form + Galois form), `3.5(2)`, `3.6`.

### Chapter 4 — 6 theorems (**the whole chapter**), at the paper's own hypothesis level (`comparator/ch4`)

| paper item | Lean declaration |
|---|---|
| 4.1-1a `lem:basis-change` | `L20261018.cup_basis_change` |
| 4.1-1b `lem:basis-change` | `L20261018.basis_change_brauer` |
| 4.2 `lem:ramified-vanishing` | `L20261018.orth_eq_bot_paper` |
| 4.3(1) `thm:ramified` | `L20261018.thm_ramified_1_paper` |
| 4.3(2) `thm:ramified` | `L20261018.thm_ramified_2_paper` |
| 4.4 `§4` corollary | `L20261018.corollary_4_4_paper` |

4.2 / 4.3(1) / 4.4 all take the **same** entry point: a linear map `d` together with
`prop:prelim-residue(1)`'s two properties (`hd_infl`/`hd_cup_pi`). They assume **no**
finiteness of the residue field, **no** `FiniteDimensional` of `H¹`, and do **not**
use the Merkurjev–Suslin theorem (which the paper states in §2 but never cites).

4.3(2) (`rank Φ ≥ 3`) is a thin wrapper over the Chapter 3 rank-barrier theorem
(`theorem_3_2_2_kummer'`), exactly as in the paper's proof ("substitute ind(D)=p² into
thm:rank-barrier(2)").

## Build and run the comparator

Prerequisites: `elan` (Lean `v4.35.0`, see `lean-toolchain`), network for the first
`lake exe cache get`, and the comparator toolchain on `PATH`
(`landrun`, `lean4export`, `comparator`).

```bash
lake exe cache get          # prebuilt mathlib oleans (pinned commit in lakefile.toml)
lake build                  # TauCeti (vendored subset) + L20261018 + comparator modules
./run-comparator.sh ch3     # Chapter 3 : 14 theorems
./run-comparator.sh ch4     # Chapter 4 :  5 theorems
```

Each comparator run replays the proof terms in the Lean kernel and checks the
statement against a `sorry`-challenge module with the same types, under the permitted
axioms `propext`, `Quot.sound`, `Classical.choice`.

## What the comparator does **not** check

`comparator` is a **proof** checker, not a **specification** checker. It verifies that, for each
名字 in `comparator/*/config.json`, the `Challenge` and `Solution` modules carry the same statement,
that the solution's proof term is accepted by the Lean kernel, and that the axioms used are within
`permitted_axioms`. It does **not**:

* check **coverage** — a statement that is not listed is invisible to it (the lists were built by
  hand; 4.3(2) was missing from an earlier revision for exactly this reason);
* check whether the **hypotheses are discharged** — 4.2 / 4.3 / 4.4 take
  `prop:prelim-residue(1)`'s two properties (`hd_infl`, `hd_cup_pi`) as hypotheses, on both sides,
  so a conditional theorem passes exactly like an unconditional one. This is faithful to the paper
  (which quotes those properties from GS 6.8.8 rather than proving them), but the comparator cannot
  tell the difference;
* check whether the hypothesis class is **inhabited** — the only machine-checked inhabitant in the
  source development needs `[Finite ResidueField]` and `[IsDiscreteValuationRing]`, i.e. it is a
  *conditional* witness, not an unconditional one.

Coverage and fidelity were checked separately against the paper text (see the source project's
`S62-CH4-FINAL.md` / `S62-CH4-FIDELITY.md`).

## Recorded verification (2026-11-01)

```
Chapter 3 : "Your solution is okay!"   (exit 0, 14/14)
Chapter 4 : "Your solution is okay!"   (exit 0,  6/6)  -- including 4.3(2)
```

Both were produced by `lake env comparator` in a wrapper project whose
`.lake/build/lib/lean` is a symlink farm over the compiled closure; the same
mechanism is used by `run-comparator.sh` here.

> Note. An earlier record (2026-10-27) of the Chapter 3 check was **not**
> reproducible on 2026-11-01: `lean4export` aborted with
> `Constant GaloBase.instSemigroupVZModAbsoluteGaloisGroupMuP_scratch not found in
> environment`. Root cause: one compiled artefact (`Hyp14.olean`) had been produced
> under a module named `scratch`, so its anonymous instance carried the suffix
> `_scratch` instead of `_Hyp14`; the name no longer existed, which is invisible to
> `#check`/`#print axioms` but fatal to a kernel replay. Recompiling `Hyp14` from
> source fixed it and the Chapter 3 check then passed. This is why the snapshot
> ships **sources** and asks you to build them.

## Layout

```
TauCeti/            vendored subset of TauCeti (Apache-2.0, see TauCeti/NOTICE)
L20261018/          the development: one module per proof step (`A`, `Galo`, `Hyp*`)
comparator/ch3/     Challenge.lean (proofs = sorry), Solution.lean (real proofs), config.json
comparator/ch4/     idem for Chapter 4
lakefile.toml       mathlib pinned to aa35a481e5f0cdb3b04a899ead15d6ca7305a624
run-comparator.sh   build + run the comparator of one chapter
```

## Licence

`TauCeti/` is Apache-2.0 (see `TauCeti/NOTICE`). The `L20261018/` sources are part of
the paper's formalisation; no separate licence is granted here.
