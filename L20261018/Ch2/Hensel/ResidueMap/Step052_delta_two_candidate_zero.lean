import L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v

/-!
# S41 R1（决定性）：★★★ **S40 的「`∂₂`-候选」是零映射** —— 载体张冠李戴的机检症状

## 一句话

`S40` 把论文 `prop:prelim-residue` 的剩余映射 `∂_q` 认成 **GS 6.3.1（= `prop-units-cohomology`
前一节）的 `r_v^i`**，而两者**不是同一个映射**：

| 映射 | 系数 | 源 | 值域 |
|---|---|---|---|
| GS 6.3.1 的 `r_v^i` | `K_nr^×`（乘法群） | `H^i(G, K_nr^×)` | `H^{i-1}(G, ℚ/ℤ)` |
| 论文/GS §6.8 的 `∂_v^i` | `μ_m^{⊗j}`（有限系数） | `H^i(G, μ_m^{⊗j})` | `H^{i-1}(G/H, H^1(H, μ_m^{⊗j}))` |

**症状（本件机检）**：`r_v^i` 的核 = `im(H^i(G,U_nr) → H^i(G,K_nr^×))`（`Hyp386.residueMap_exact`），
而 `μ_p` 的元素**全是单位**（`v(ζ) = 0`）⟹ `μ_p ↪ K_nr^×` 落在 `U_nr` 里 ⟹

```
kummerResidueMap = r_v ∘ (μ_p ↪ K_nr^×)_* = 0 .
```

即 **S40 造的 `∂₂`-候选恒为零**，故 `KnrResidueObligation` 的 ③c（`d (y ⌣ π) = y`）对它
**不可能成立**（除非 `VKG = ⊥`）。

## 文献裁定（`S41-RECON-IV`，PDF 逐页核实）

`raw/GilleSzamuely2017.tex` 是**部分** PDF 转换件：全文只有 4 个 `\chapter`，印刷第 4–6 章丢了
章断 ⟹ **印刷号不能由 tex 推出**。按 `raw/GilleSzamuely2017.pdf`（2nd ed.）核定：

| tex label | 印刷号 | 内容 |
|---|---|---|
| `prop-units-cohomology` | **Prop 6.3.1** | `H^i(G,U_nr) ≅ H^i(G,κ_s^×)`；`r_v^i` 的分裂正合列（`ℚ/ℤ` 系数） |
| `sec:cohomology-complete-dv` | 印刷 **§6.3** | 完全离散赋值域 |
| `sec:residue-finite-coefficients` | 印刷 **§6.8** | **有限系数**的剩余映射 ← **论文真正用的** |
| `cor-split-exact-sequence-finite-coefficients` | **Cor 6.8.8** | 论文引的「GS 6.8.8」 |
| `ex-tame-symbol-k1-k2` | **Example 7.1.5** | 论文引的「GS 7.1.5」（**Milnor K₂ 的驯符号**，非上同调陈述） |
| `prop-specialization-section` | **Prop 6.8.7** | `s_π^i(Inf b) = ∂_v^1((−π)) ∪ b = b` ⟹ **③c 的正确出处** |
| `lemma-residue-cup-product` | **Lemma 6.8.4** | **投影公式** `∂^{p+q}(a ∪ Inf b) = ∂^p a ∪ b` ⟹ ②③ 的共同引擎 |

⟹ `S40-REMAINING-PLAN.md` §3 与 `PROMPT-S41` §③ 的路线（`∂₂` = `r_v`）**前提错误**。

## 正确路线（GS §6.8，全部是**有限系数**、非 `K_nr^×`）

1. **Construction 6.8.1**：`∂^i : H^i(G,A) → H^{i-1}(G/H, H^1(H,A))`，由
   `0 → A → M^G(A) → C → 0` ＋ 膨胀-限制（`H` = 惯性群，`cd(H) ≤ 1`）造；
2. **Prop 6.8.2 / Cor 6.8.8**：正合列 ⟹ `∂ ∘ inf = 0`（= ③b 的一半）与 `ker ∂ = im inf`；
3. **Lemma 6.8.4**（投影公式）＋ **Prop 6.8.7**（`∂^1((−π)) = 1`，即 **`∂^1` = 模 `m` 赋值**）
   ⟹ `∂²((π) ∪ Inf b) = b`（= ③c）；
4. **③b**：`∂²((u)∪(w)) = ∂^1((u)) ∪ (\bar w) = 0`（因 `v(u) = 0`）。

**库内可用的引擎**（`S41-RECON-III` 侦察命中，规则 23／L46）：

| 件 | 位置 | 内容 |
|---|---|---|
| `TauCeti.ContCohomology.explicitDelta1_explicitCup01_left/right` 等 **6 条** | `ContCohomology/Cup/ConnectingMap.lean:137,152,188,235,251,265` | 连续上同调**低阶**的 `δ/cup` 规则（`δ(x⌣y)=δx⌣y`、`δ(x⌣y)=(−1)^p x⌣δy`） |
| `TauCeti.TateCohomology.cup_δ_of_leftInverse`／`cup_δ_of_flat`／`δ_cup_of_leftInverse` | `TateCohomology/Cup/Delta.lean:188,242,443` | **全次数**的 `δ/cup` 规则（Tate 上同调） |
| `TauCeti.ContCohomology.delta_cup` | `ContCohomology/Bockstein/Leibniz.lean:370` | 单条短正合列的**分级 Leibniz 规则** |
| `TauCeti.ContCohomology.explicitDelta1`／`DiscreteShortExact.delta` | 库内 | **连接映射本身** |

⟹ 「`∂∘inf = 0`」「投影公式」「`δ/cup`」三件在库里**已有**；缺的是 GS §6.8 的**载体**
（惯性群 `H`、`M^G(A)`、`H^1(H,μ_p) ≅ ℤ/p` 的识别）—— 与 `S39` 的 B 段同族，**不是** `K_nr^×` 路线。

## 本件机检的件

| 声明 | 内容 |
|---|---|
| **`knrProjOn_kummerCoeffToKnrUnits`** | ★★★★★ **`v (kummerCoeffToKnrUnits x) = 0`**（`μ_p` 的值全为 0） |
| **`kummerCoeffToKnrUnits_mem_ker** | 该像落在 `ker v = U_nr` 内（`Hyp467.knrProjOn_exact` 的左端） |
| `kummerCoeffToUnits` | `μ_p →+ U_nr` 的**提升**（`ker v = im(incl)` 的截面形式） |

## 诚实边界（一步残余，不冒充证明）

「`kummerResidueMap = 0`」的最后一步是「**零系数映射的 `coeffMap` 是零**」，即
`coeffMap (0 : X ⟶ Y) n = 0`（`ContinuousCohomology.map _ 0 n = 0`）。
`ContinuousCohomology.map` 在 mathlib 里是 `HomologicalComplex.homologyMap (cochainsMap φ f) n`
（`Mathlib/RepresentationTheory/Homological/ContCohomology/Functoriality.lean:150`），
故该步 = `cochainsMap φ 0 = 0` ＋ `homologyMap_zero`；本轮**未**把它落件（记为
`∅-formalization-gap`，见 `S41-STATUS.md` §2.4）。
**数学结论不受影响**：`v∘kummer = 0` 已机检，而 `coeffMap` 是函子（`coeffMap_comp`、`coeffMap_id`
均在库），函子保零元。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **`μ_p` 的 `π`-adic 赋值恒为 0** —— 「单位」这一事实的机检形式。

机制：`KummerCoeff` 是 `p`-挠（`kummerCoeff_nsmul_eq_zero`），而
`knrValOn ∘ kummerCoeffToKnrUnits` 是 `Multiplicative ℤ`（无挠）中的 `p`-挠元。
**不需要**任何赋值计算。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8160 quote="Denoting by $U_{nr}$ the multiplicative group of units in $K_{nr}$, we get an"
theorem knrProjOn_kummerCoeffToKnrUnits (x : KummerCoeff F p) :
    knrProjOn F (kummerCoeffToKnrUnits (K := F) p x) = 0 := by
  have hx : p • x = 0 := kummerCoeff_nsmul_eq_zero (K := F) p x
  have hcoe : (kummerCoeffToKnrUnits (K := F) p) (p • x)
      = p • (kummerCoeffToKnrUnits (K := F) p) x := AddMonoidHom.map_nsmul _ _ _
  have h1 : p • knrProjOn F (kummerCoeffToKnrUnits (K := F) p x)
      = knrProjOn F (kummerCoeffToKnrUnits (K := F) p (p • x)) := by
    rw [hcoe, ← AddMonoidHom.map_nsmul]
  rw [hx, AddMonoidHom.map_zero] at h1
  have h2 : (p : ℤ) * (knrProjOn F (kummerCoeffToKnrUnits (K := F) p x)).down = 0 := by
    have := congrArg ULift.down h1
    simpa [nsmul_eq_mul] using this
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hp
  · exact ULift.ext (by simpa using h3)

/-- ★★★★★ **`μ_p` 的像落在 `U_nr = ker v` 内**（GS (6.1) 的左端）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:prop-units-cohomology quote="The natural reduction map $U_{nr}\to\kappa_{s}^{\times}$ induces isomorphisms"
theorem kummerCoeffToKnrUnits_mem_ker (x : KummerCoeff F p) :
    (kummerCoeffToKnrUnits (K := F) p x ∈ (knrProjOn F).ker) :=
  AddMonoidHom.mem_ker.mpr (knrProjOn_kummerCoeffToKnrUnits (F := F) p x)

/-- ★★★★ **`μ_p → U_nr` 的提升**（`ker v` 的截面形式；`Hyp488` 的退化性论证的载体半）。 -/
noncomputable def kummerCoeffToUnits :
    KummerCoeff F p →+ ↥(knrProjOn F).ker :=
  (kummerCoeffToKnrUnits (K := F) p).codRestrict _
    (fun x => kummerCoeffToKnrUnits_mem_ker (F := F) p x)

/-- 提升与 `kummerCoeffToKnrUnits` 的相容（逐点）。 -/
theorem kummerCoeffToUnits_apply (x : KummerCoeff F p) :
    ((kummerCoeffToUnits (F := F) p x : ↥(knrProjOn F).ker) : KnrUnits' F)
      = kummerCoeffToKnrUnits (K := F) p x := rfl

end L20261018

#print axioms L20261018.knrProjOn_kummerCoeffToKnrUnits
#print axioms L20261018.kummerCoeffToKnrUnits_mem_ker
#print axioms L20261018.kummerCoeffToUnits
#print axioms L20261018.kummerCoeffToUnits_apply
