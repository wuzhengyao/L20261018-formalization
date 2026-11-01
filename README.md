# L20261018 — Chapters 3 & 4, Lean 4 (minimal snapshot)

Source-closed snapshot of the Lean 4 formalisation of chapters 3–4 of `L20261018.tex`,
checked with the official `comparator`. mathlib is pinned in `lakefile.toml`, TauCeti is
vendored (`TauCeti/`, Apache-2.0); nothing else is needed.

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
./run-comparator.sh         # ch3: 14 theorems, 3.1–3.6
```

Chapter 3 is unconditional at the paper's hypothesis level: the abstract hypotheses of the
source development are all discharged — `hker` by `RootsOfUnityExists.lemma_3_1_2_galo'`,
`ind`+`hind` by `H2Bridge.hind_kummer`, `hNrd` by `hNrd_crossedProduct` (crossed products).
What is left are the paper's own hypotheses (`p` odd, `(a₁)∪(a₂) ≠ 0`, `N ⊆ U^⊥`) plus, for
3.4/3.5/3.6, the carriers of the general algebraic layer (`BiKummerData`, the two short exact
sequences), which are parameters there by design.

## Layout

```
TauCeti/          vendored subset of TauCeti (Apache-2.0)
L20261018/        the development: one module per proof step (A, Galo, Hyp*)
comparator/ch3/   Challenge.lean (proofs = sorry) + Solution.lean + config.json
comparator/ch4u/  idem, chapter 4 unconditional
lakefile.toml     mathlib pinned to aa35a481e5f0cdb3b04a899ead15d6ca7305a624
```

Both groups were rebuilt from these sources and pass on 2026-11-08 (Lean `v4.35.0`).
If the pinned mathlib is already built locally, point `require mathlib` at it by path and
`lake build` works offline.

`TauCeti/` is Apache-2.0 (see `TauCeti/NOTICE`); the `L20261018/` sources are part of the
paper's formalisation and carry no separate licence.
