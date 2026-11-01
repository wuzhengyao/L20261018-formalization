import Hyp472

/-!
# S40 R12：Kummer 系数映射的 `G`-等变性 ＋ `ofDiscreteModule` 包装 ⟹ **`∂₂`-候选**

## 本轮做什么

R11 给了 `kummerCoeffToKnrUnits : KummerCoeff K p →+ KnrUnits' K`（Kummer 系数降到 `K_nr^×`）。
本轮把它升成 **`TopRep ℤ G` 的态射**，从而在 `H^{n+2}` 上取函子像，再复合 `knrResidueMap'`，
得到论文 `prop:prelim-residue`(2) 的 **`∂₂`-候选**：

```
kummerResidueMap (n) : H^{n+2}(G, μ_p) ──→ H^{n+1}(G, ℚ/ℤ)
                     = knrResidueMap' n ∘ H^{n+2}(kummerCoeffToKnrUnits)
```

## 侦察收获（写入记录，避免重复）

`TauCeti` 已有：
* `kummerCoeff_continuousSMul : ContinuousSMul G (KummerCoeff K n)`；
* **`smul_kummerCoeff_eq_self : (μ_n ⊂ K) → g • x = x`**（⟹ **W4「`μ_n` 是平凡模」库内已有**，
  无须自建 `KummerCoeff ≅ trivial (ZMod n)` 的系数同构）；
* `KummerCoeff` 的 `⊥` 拓扑与 `DiscreteTopology`。

## 本件不声称什么

* 不声称 `∂₂` 的两条性质（`∂₂((u)∪(w)) = 0`、`∂₂((y)∪(π)) = y`）—— 那是 GS `:1050`，下一轮；
* 不声称 W5／W6。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-- ★★★★ **`knrMap` 在常系数单项式上的作用**：`single 0 ζ ↦ single 0 (σ ζ)`。 -/
theorem knrMap_single_zero (σ : TauCeti.AbsoluteGaloisGroup K) (ζ : (SeparableClosure K)ˣ) :
    knrMap σ (HahnSeries.single 0 ((ζ : SeparableClosure K)) : LaurentSeries (SeparableClosure K))
      = (HahnSeries.single 0 (((σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
          ((ζ : SeparableClosure K)))) : LaurentSeries (SeparableClosure K)) := by
  ext n
  rw [knrMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  rcases eq_or_ne n 0 with h | h
  · subst h; simp
  · simp [h]

/-- **W4 在**战役内早已完成**：`Hyp214.kummerCoeff_smul_trivial` 已是 `G` 在 `KummerCoeff`
上作用平凡的机检件（包装 TauCeti 的 `smul_kummerCoeff_eq_self`）。此处仅**引用核对**，
不重复声明（`RECON-R3` §90.2 记录该更正）。 -/
example (p : ℕ) [Fact p.Prime] [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (g : TauCeti.AbsoluteGaloisGroup K) (x : KummerCoeff K p) : g • x = x :=
  TauCeti.smul_kummerCoeff_eq_self hζ g x

variable {K : Type} [Field K]

/-- ★★★★★ **`G`-等变性**：`kummerCoeffToKnrUnits` 是 `G`-模态射。
（三轮的债，本轮按 `RECON-R3` §90.1 的归约收：两边都化到 `single 0 (σ ↑ζ)`。） -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8176 quote="$$0\to H^{i}(G,U_{nr})\to H^{i}(G,K_{nr}^{\times})\xrightarrow{r_{v}^{i}}"
theorem kummerCoeffToKnrUnits_equivariant (p : ℕ) [NeZero p]
    (σ : TauCeti.AbsoluteGaloisGroup K) (x : KummerCoeff K p) :
    kummerCoeffToKnrUnits (K := K) p (σ • x) = σ • kummerCoeffToKnrUnits (K := K) p x := by
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  show (HahnSeries.single 0 (((Additive.toMul (σ • x) : rootsOfUnity p (SeparableClosure K)) :
      (SeparableClosure K)ˣ) : SeparableClosure K) : LaurentSeries (SeparableClosure K))
    = knrMap σ (HahnSeries.single 0 ((((Additive.toMul x : rootsOfUnity p
        (SeparableClosure K)) : (SeparableClosure K)ˣ) : SeparableClosure K)) :
          LaurentSeries (SeparableClosure K))
  rw [knrMap_single_zero]
  congr 1

/-! ## 2. `ofDiscreteModule` 包装与 **`∂₂`-候选** -/

/-- ★★★★ **Kummer 系数到 `K_nr^×` 的 `TopRep ℤ G` 态射**。 -/
noncomputable def kummerCoeffToKnr (p : ℕ) [NeZero p] :
    ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup K) (KummerCoeff K p) ⟶
      ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup K) (KnrUnits' K) :=
  ofDiscreteModuleMap (AddMonoidHom.toIntLinearMap (kummerCoeffToKnrUnits (K := K) p))
    (kummerCoeffToKnrUnits_equivariant (K := K) p)

/-- ★★★★★ **`∂₂`-候选**（论文 `prop:prelim-residue`(2) 的载体）：

```
kummerResidueMap p n : H^{n+2}(G, μ_p) ──→ H^{n+1}(G, ℚ/ℤ)
                     = knrResidueMap' n ∘ H^{n+2}(kummerCoeffToKnr p)
```

`n = 0` 时就是 `∂₂ : H²(G, μ_p) → H¹(G, ℚ/ℤ)`。

论文 `raw/L20261018.tex:1050` 对它的要求是（逐字）：
`\partial_2((u)\cup(\pi))=(\bar u), \partial_2((\pi)\cup(u))=-(\bar u), \partial_2((u)\cup(w))=0`
—— 这三条是 ③ 的目标。 -/
noncomputable def kummerResidueMap (p : ℕ) [NeZero p] (n : ℕ) :
    continuousCohomology (n + 2)
        (ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup K) (KummerCoeff K p)) →
      continuousCohomology (n + 1)
        (ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup K) QoverZdisc) :=
  knrResidueMap' (K := K) n ∘
    ((ContinuousCohomology.continuousCohomologyFunctor ℤ (TauCeti.AbsoluteGaloisGroup K) (n + 2)).map
      (kummerCoeffToKnr (K := K) p)).hom

end L20261018

#print axioms L20261018.kummerCoeffToKnr
#print axioms L20261018.kummerResidueMap
