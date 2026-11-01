# L20261018 — Chapters 3 & 4, Lean 4 (minimal snapshot)

Source-closed snapshot of the Lean 4 formalisation of chapters 3–4 of `L20261018.tex`,
with the **official comparator** checks. mathlib is pinned in `lakefile.toml`, TauCeti is
vendored (`TauCeti/`, Apache-2.0); nothing else is needed.

## Verify Chapter 4 — unconditional

```bash
lake exe cache get          # once: prebuilt mathlib oleans
./run-comparator.sh ch4u    # build, then run the comparator
```

Expect `Lean default kernel accepts the solution` / **`Your solution is okay!`**.

`comparator/ch4u` checks these 7 declarations:

| paper | declaration |
|---|---|
| `prop:prelim-residue`(1) | `exists_residueMap` — `d` is **constructed**, not assumed |
| " | `tameResidueFacts_uncond` |
| 4.2 `lem:ramified-vanishing` | `orth_eq_bot_viaResidue` |
| 4.3(1) `thm:ramified` | `thm_ramified_1_viaResidue` |
| 4.4 | `corollary_4_4_viaResidue` |
| chapter-4 named slot | `ch4TameSymbolHyp_viaResidue`, `disjoint_viaResidue` |

**"Unconditional" =** none of the seven takes a residual map (`d`, `hd_infl`, `hd_cup_pi`)
as an argument; `d` is built inside. They quantify over arbitrary `a₁ a₂ : GaloBase.V`
(not only Kummer classes of field elements), and the hypotheses left are the paper's own:
`char K ≠ p`, `p ≠ 2`, `v(π) = 1`, `(a₁)∪(a₂) ≠ 0`, `v̄|_U ≠ 0`.

## The other groups (same checker, different target lists)

| group | chapter | status |
|---|---|---|
| `./run-comparator.sh ch4` | 4, 6 theorems | full statements, **conditional**: 4.2/4.3(1)/4.4 take `d` + `hd_infl` + `hd_cup_pi` (the paper's own `prop:prelim-residue`(1)) |
| `./run-comparator.sh` (ch3) | 3, 14 theorems | 3.1–3.6 with the named hypotheses still open (`hker`, `ind`+`hind`, `hNrd`, `hproj`, `hcoh`+`hcyc`, `hkerd2`+`hd2surj`) — **not** unconditional |

So `ch4` = full statement, conditional; `ch4u` = full statement, unconditional. The checker
cannot tell the two apart — the difference is *which list you run*.

## What the comparator checks, and what it does not

Official tooling (`comparator v4.35.0`, `lean4export v4.35.0`, `landrun` sandbox): install
with `bash scripts/install-comparator-tools.sh`; its judgement power is itself certified by
`bash scripts/validate-comparator-tools.sh` (a positive control plus `statement mismatch`
and `illegal axiom` negative controls).

Per name in `comparator/*/config.json` it checks: (1) `Challenge` (`sorry` proof) and
`Solution` (the project's proof term) carry the **same statement**; (2) the kernel
**accepts** the solution; (3) axioms ⊆ `{propext, Quot.sound, Classical.choice}`.

It does **not** check coverage (unlisted statements are invisible — 4.3(2) was once
missing from `ch4`), whether the hypotheses are discharged, or whether the hypothesis
classes are inhabited (the Hensel setup is assumed; a concrete instance
`L20261018.FqXt.orth_eq_bot_uncond`, `ZMod 7((t))` with `p = 3`, lives in the sources).

Recorded passes: `ch3` 14/14, `ch4` 6/6 (2026-11-01), `ch4u` 7/7 (2026-11-08), all rebuilt
from the shipped sources. (An earlier `ch3` record was **not** reproducible: one artefact
had been compiled under a module named `scratch`, leaving a `_scratch` instance suffix that
`#check` cannot see but a kernel replay cannot survive. Hence: ships sources, you build.)

## Layout

```
TauCeti/          vendored subset of TauCeti (Apache-2.0)
L20261018/        the development: one module per proof step (A, Galo, Hyp*)
comparator/ch3/   Challenge.lean (proofs = sorry) + Solution.lean + config.json
comparator/ch4/   idem, chapter 4 at the paper hypothesis level
comparator/ch4u/  idem, chapter 4 unconditional
lakefile.toml     mathlib pinned to aa35a481e5f0cdb3b04a899ead15d6ca7305a624
```

`TauCeti/` is Apache-2.0 (see `TauCeti/NOTICE`); the `L20261018/` sources are part of the
paper's formalisation and carry no separate licence.
