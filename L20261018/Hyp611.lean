import L20261018.Hyp607
import L20261018.Hyp610

/-!
# S51 R2：**第 4 章证明结构索引 ＋ 六档归一**（`residueSpan = ⊥` 是唯一正规形）

## 0 为什么需要这一件（用户 2026-10-31 指令：「整理证明结构」）

战役已累积 605 个 `Hyp*` 文件、**2606 条声明**，其中 **1543 条无外部消费者**（机器统计见
`PROOF-MAP.md` §2）——即绝大多数是各文件内部的中间步。真正到终点的有**两条**互不相同的路：
`residueSpan = ⊥`（五档）与 `residueSpan ≤ range infl₂` ＋ 消失性（档 ⑥）。
本件证明**它们其实是同一个正规形**：

```
            档 1 有限  ┐
            档 2 p-可除 ├─ residueSpan = ⊥
            档 3 循环   │      （Hyp302／Hyp430／Hyp290／Hyp607 直给）
            档 4 完备   │
            档 5 dim≤1  ┘
            档 6 (CI)+H²(Γ⧸I,μ_p)=0 ── 本件 `residueSpan_eq_bot_of_subsingleton_H2_residue`
                    ↓
        ch4TameSymbolHyp_of_residueSpan_eq_bot      ← 唯一的下游装配（本件）
                    ↓
        Ch4TameSymbolHyp  ⟺  TameResidueFacts        （Hyp526，双向）
```

⟹ **六档＝一个正规形 ＋ 六个充分条件**。此前的写法把「档」与「装配」混在一起
（`ch4TameSymbolHyp_of_*` 共 18 个变体，见 `PROOF-MAP.md` §3），本件把装配收到一处。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`residueSpan_eq_bot_of_subsingleton_H2_residue`** | ★★★★★ **档 ⑥ ⟹ `residueSpan = ⊥`**（六档的共同核） |
| **`tameResidueFacts_Galo_of_residueSpan_eq_bot`** | `residueSpan = ⊥` ＋ `(R1)`（`Hyp319.residuePhi_injective_t1`，**无条件**）⟹ `TameResidueFacts` |
| **`ch4TameSymbolHyp_of_residueSpan_eq_bot`** | ★★★★★ **唯一的下游装配**：`residueSpan = ⊥` ⟹ `Ch4TameSymbolHyp` |
| `ch4TameSymbolHyp_of_subsingleton_H2_residue'` | **回归对照**：档 ⑥ 经正规形重走一遍，与 `Hyp610` 的直接路线结论一致 |

## 2 与库内已有件的关系（L47 ④：先查库，登记净增量）

* `Hyp607.tameResidueFacts_of_residueSpan_eq_bot`（抽象层）与 `Hyp526`（`⟺`）**已有**；
  本件的 `tameResidueFacts_Galo_of_residueSpan_eq_bot` 只是把 `(R1)` 的**无条件**版
  （`Hyp319.residuePhi_injective_t1`）接上去，**净增量为零**，属"接口运输"。
* `Hyp604.ch4TameSymbolHyp_of_tameResidueFacts` **已有**（走 `GsResidueData`）；
  本件的 `ch4TameSymbolHyp_of_residueSpan_eq_bot` ＝ 它与 `Hyp607` 的合成，
  **净增量 = 把 18 个 `ch4TameSymbolHyp_of_*` 变体收成一个入口**（结构性，非数学）。
* 档 ⑥ 的 `residueSpan = ⊥` 这一步是**新内容**：它把 `Hyp610` 的两条假设接到正规形上。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section NormalForm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **档 ⑥ ⟹ 六档的共同正规形 `residueSpan = ⊥`**。

由 `Hyp610.residueSpan_le_range_infl2Res`（`(CI) ⟹ residueSpan ≤ range infl₂`）
＋ `Hyp610.range_infl2Res_eq_bot_of_subsingleton`（`Subsingleton ⟹ range infl₂ = ⊥`）得。 -/
theorem residueSpan_eq_bot_of_subsingleton_H2_residue
    (hpF : IsUnit (p : F))
    (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]
    (hCI : ∀ y : VKG F p v hpF,
      ∃ a : ResH1Type (F := F) p I, infl1Res (F := F) p I a = (y : GaloBase.V F p))
    (hκ : Subsingleton (ResH2Type (F := F) p I)) :
    residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF) = ⊥ :=
  le_bot_iff.mp <|
    (range_infl2Res_eq_bot_of_subsingleton (F := F) (p := p) (I := I) hκ) ▸
      residueSpan_le_range_infl2Res (F := F) (p := p) (v := v) (I := I) hpF hCI

/-- ★★★★★ **`residueSpan = ⊥` ＋ (R1) ⟹ `TameResidueFacts`**（Galo 层）。

`(R1)` 用**无条件**的 `Hyp319.residuePhi_injective_t1`（无 `[Finite 𝓀[F]]`）。 -/
theorem tameResidueFacts_Galo_of_residueSpan_eq_bot
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hbot : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) = ⊥) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) :=
  tameResidueFacts_of_residueSpan_eq_bot _ _ _
    (residuePhi_injective_t1 (F := F) (p := p) hp hζ hv hπ hp2) hbot

/-- ★★★★★ **第 4 章的唯一下游装配**：`residueSpan = ⊥` ⟹ `Ch4TameSymbolHyp`。

五档（`Hyp302` 有限／`Hyp430` 可除／`Hyp430` 循环／`Hyp290` 完备／`Hyp607` `dim≤1`）
与档 ⑥（经 `residueSpan_eq_bot_of_subsingleton_H2_residue`）**全部**经此一格落到结论。 -/
theorem ch4TameSymbolHyp_of_residueSpan_eq_bot
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hbot : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) = ⊥) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  (ch4TameSymbolHyp_iff_tameResidueFacts (F := F) (p := p) (v := v) (π := π) hpF hπ).mpr
    (tameResidueFacts_Galo_of_residueSpan_eq_bot (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hv hπ hp2 hbot)

/-- ★★★★ **回归对照（档 ⑥ 的两条路线一致）**：经正规形重走档 ⑥，与 `Hyp610` 的
直接路线（`ch4TameSymbolHyp_of_subsingleton_H2_residue`）给同一结论。

两条路线的差别只在中间格：直接路线用 `Hyp449.ch4TameSymbolHyp_iff_disjoint`
（`Disjoint` 形态），本路用 `Hyp526`（`TameResidueFacts` 形态）。 -/
theorem ch4TameSymbolHyp_of_subsingleton_H2_residue'
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]
    (hCI : ∀ y : VKG F p v hpF,
      ∃ a : ResH1Type (F := F) p I, infl1Res (F := F) p I a = (y : GaloBase.V F p))
    (hκ : Subsingleton (ResH2Type (F := F) p I)) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  ch4TameSymbolHyp_of_residueSpan_eq_bot (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2
    (residueSpan_eq_bot_of_subsingleton_H2_residue (F := F) (p := p) (v := v) (I := I) hpF hCI hκ)

end NormalForm

/-! ## 3 证明结构索引（`#check` 机检；`PROOF-MAP.md` §1 的每一格都取自本节的读数） -/

section SpineIndex

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

-- (R1)：无条件
#check @residuePhi_injective_t1

-- 终局等价（不可再缩）
#check @ch4TameSymbolHyp_iff_tameResidueFacts
#check @ch4TameSymbolHyp_iff_disjoint

-- 唯一的下游装配
#check @ch4TameSymbolHyp_of_residueSpan_eq_bot

-- 档 1–5：各给 `residueSpan = ⊥`
#check @unitsCupVanish_of_finite
#check @unitsCupVanish_of_divisible
#check @unitsCupVanish_of_cyclicUnits
#check @unitsCupVanish_complete
#check @residueSpan_eq_bot_of_finrank_le_one

-- 档 6：给 `residueSpan = ⊥`（经 `H²(Γ⧸I,μ_p) = 0` ＋ `(CI)`）
#check @residueSpan_eq_bot_of_subsingleton_H2_residue
#check @ch4TameSymbolHyp_of_subsingleton_H2_residue

-- 档 6 的两条引擎（库内 `TopPairing.cup_map` ＋ `Subsingleton`）
#check @infl2Res_cupRes
#check @range_infl2Res_eq_bot_of_subsingleton

-- 库内机械（**不是**自建；`PROOF-MAP.md` §4 的 `LIB` 行）
#check @TauCeti.ContinuousCohomology.infl
#check @TauCeti.TopPairing.cup_map
#check @TauCeti.TopPairing.cup_infl

end SpineIndex

end L20261018

#print axioms L20261018.residueSpan_eq_bot_of_subsingleton_H2_residue
#print axioms L20261018.tameResidueFacts_Galo_of_residueSpan_eq_bot
#print axioms L20261018.ch4TameSymbolHyp_of_residueSpan_eq_bot
#print axioms L20261018.ch4TameSymbolHyp_of_subsingleton_H2_residue'
