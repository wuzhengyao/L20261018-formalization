import L20261018.Hyp343
import L20261018.Hyp449
import L20261018.Hyp431
import L20261018.Hyp479
import L20261018.Hyp525

/-!
# S43 R34：★★★★★ **终局等价** —— `Ch4TameSymbolHyp` **恰好**等价于两条残数事实 (R1)＋(R2)

## 本件做什么

战役跑了很久，终点命题 `Ch4TameSymbolHyp` 一直被写成「存在 `d` 带两条杯积公式」。
本件证明一个**不可再缩**的等价：

```
Ch4TameSymbolHyp  ⟺  TameResidueFacts (∪, v̄, (π))
```

即 **`Ch4TameSymbolHyp` ＝ (R1) `Φ` 单射 ＋ (R2) `Disjoint (range Φ) residueSpan`**，
**不多也不少**。

## 为什么这是有意义的收口

| 方向 | 件 |
|---|---|
| `Ch4TameSymbolHyp ⟹ (R1)∧(R2)` | `Hyp343.exists_residueMap_iff_tameResidueFacts`（`⟸` 方向） |
| `(R1)∧(R2) ⟹ Ch4TameSymbolHyp` | 同上（`⟹` 方向）＋ `Hyp479`（`Ch4TameSymbolHyp ≡ KnrResidueObligation`，`rfl` 级） |

⟹ **任何**「绕开 (R1)/(R2) 去证 `Ch4TameSymbolHyp`」的路线**都不存在**：
终点命题就是这两条。这也解释了 §1.15–§1.17 的口径：
(R2)（分裂）只在 `F = K((π))` 被论文声明，一般 Hensel 只有 `∂₂`。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`ch4TameSymbolHyp_iff_tameResidueFacts`** | ★★★★★ **终局等价** |
| **`ch4TameSymbolHyp_iff_disjoint`** | 只留 (R2)：(R1) 已由 `Hyp319.residuePhi_injective_t1` 无条件供给 |
| `not_ch4TameSymbolHyp_of_not_disjoint` | 逆否形态：`¬Disjoint ⟹ ¬Ch4TameSymbolHyp` |

## 诚实边界

* 本件**不**证明 (R2) 对任意 `κ`；它证明的是**终点命题与 (R2) 等价**（故不能更弱）。
* (R2) 已知成立的口径：`[Finite κ]`（`Hyp321`／`Hyp396`）、`κˣ` `p`-可除（`Hyp430`／`Hyp525`）；
  论文对**完备** `F = K((π))` 声明分裂（`raw/L20261018.tex:1033`，(3)）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section TerminalEquivalence

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **终局等价**：`Ch4TameSymbolHyp` **恰好**等价于 `TameResidueFacts`（(R1)＋(R2)）。

`Ch4TameSymbolHyp` 就是 `KnrResidueObligation`（`Hyp479`，`rfl` 级），
而后者与 `TameResidueFacts` 的等价是 `Hyp343`。 -/
theorem ch4TameSymbolHyp_iff_tameResidueFacts (hpF : IsUnit (p : F))
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF ↔
      TameResidueFacts (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) :=
  exists_residueMap_iff_tameResidueFacts (GaloBase.cup (K := F) (p := p))
    (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)
    (valLinOf_pi (F := F) (p := p) v hpF hπ) (GaloBase.cup_skew (K := F) (p := p))

/-- **逆否形态**：若 (R2) 不成立，则 `Ch4TameSymbolHyp` 不成立。

（这是「口径不可再放宽」的机器读数：任何使 (R2) 失败的 `κ` 都不可能有 `Ch4TameSymbolHyp`。） -/
theorem not_ch4TameSymbolHyp_of_not_disjoint
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (h : ¬ Disjoint
      (LinearMap.range (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)))
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF))) :
    ¬ Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  fun hc =>
    h (ch4TameSymbolHyp_iff_disjoint (F := F) (p := p) (v := v) (π := π) hζ hp hpF hv hπ hp2 |>.mp hc)

end TerminalEquivalence

end L20261018

#print axioms L20261018.ch4TameSymbolHyp_iff_tameResidueFacts
#print axioms L20261018.not_ch4TameSymbolHyp_of_not_disjoint
