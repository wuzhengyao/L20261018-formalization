import Hyp383
import Hyp430
import Hyp479

/-!
# S43 R31：★★★★★★ **`Ch4TameSymbolHyp` 对「`κˣ` `p`-可除」的一般 Hensel 域成立**（**无限剩余域可用**）

## 本件做什么

战役的**总收尾定理** `Ch4TameSymbolHyp` 此前在两条口径下机检：

| 口径 | 件 |
|---|---|
| 有限剩余域 `[Finite 𝓀[F]]` | `Hyp321.tameResidueFacts_Galo_noBridge`／`Hyp396.residueDisjoint_of_finite` |
| **`κˣ` 的 `p`-可除性**（`∀ U, ∃ Z, Z^p = U`） | `Hyp430.unitsCupVanish_of_divisible`（**无** `[Finite]`、**无** `FiniteDimensional`） |

本件把第二条口径**接到总收尾定理**上：

```
κˣ p-可除  ⟹  UnitsCupVanish          （Hyp430.unitsCupVanish_of_divisible）
           ⟹  ∃ d（两条残数值公式）    （Hyp383.exists_residueMap_of_unitsCupVanish）
           ≡  KnrResidueObligation      （Hyp479，rfl 级）
           ≡  Ch4TameSymbolHyp          （Hyp479.ch4TameSymbolHyp_of_obligation）
```

**意义**：`[Finite (ResidueField)]` 被彻底拿掉 —— 论文的 `κ` 可以**无限**
（如代数闭域，或任何 `p`-可除的单位群）。这与「有限剩余域」口径**不可互推**，是**严格的推广**。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`knrResidueObligation_of_divisibleResidue`** | `κˣ` p-可除 ⟹ `KnrResidueObligation` |
| **`ch4TameSymbolHyp_of_divisibleResidue`** | ★★★★★★ **`Ch4TameSymbolHyp`（一般 Hensel，`κ` 任意满足 `κˣ` p-可除）** |
| **`ch4TameSymbolHyp_of_finite'`** | 回归对照：有限剩余域口径（与上面同一结论的两条独立证据路径） |

## 诚实边界

* 剩余的那一条**不是**库级缺口，而是**数学假设**：`κˣ` 的 `p`-可除性。
  对**任意** `κ`（如 `κ = ℝ`、`p = 3`）它**不成立**，此时 `UnitsCupVanish` 不能由本路线得到；
  论文 `prop:prelim-residue` 在该情形是否仍成立，属于**论文自身**的数学问题（GS 6.8.8 只保证
  `∂₂((u)∪(w)) = 0`，而战役的 `UnitsCupVanish` 是更强的 `(u)∪(w) = 0`）。
* 侧条件（论文自身层级）：`hp2 : p ≠ 2`、`hv : ValCompat`、`hπ : v π = 1`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section DivisibleResidue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **`KnrResidueObligation` ⟸ `κˣ` 的 `p`-可除性**（**无** `[Finite (ResidueField)]`、
**无**有限维）。 -/
theorem knrResidueObligation_of_divisibleResidue {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, ∃ Z, Z ^ p = U)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    KnrResidueObligation (F := F) p v π hpF :=
  exists_residueMap_of_unitsCupVanish (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2
    (unitsCupVanish_of_divisible (F := F) (p := p) (v := v)
      hζ hdiv hp hpF hp2 hv)

/-- ★★★★★★ **总收尾：`Ch4TameSymbolHyp` 在「`κˣ` `p`-可除」的一般 Hensel 域上成立**
（**无限剩余域可用**，与「有限剩余域」口径不可互推）。 -/
-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem ch4TameSymbolHyp_of_divisibleResidue {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, ∃ Z, Z ^ p = U)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  ch4TameSymbolHyp_of_obligation (F := F) p (v := v) (π := π) hpF
    (knrResidueObligation_of_divisibleResidue (F := F) (p := p) (v := v) (π := π)
      hζ hdiv hp hpF hv hπ hp2)

/-- **回归对照**：**有限**剩余域口径给出同一结论（`Hyp430.unitsCupVanish_of_finite'`）。
两条证据路径独立（一条用 `Scratch` 的 `hcyc_of_finite`，一条用 `hcyc_of_divisible`），
结论相同 —— `Hyp430` 的口径是**严格推广**（两者的假设互不蕴含）。 -/
theorem ch4TameSymbolHyp_of_finite' [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  ch4TameSymbolHyp_of_obligation (F := F) p (v := v) (π := π) hpF
    (exists_residueMap_of_unitsCupVanish (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hv hπ hp2
      (unitsCupVanish_of_finite' (F := F) (p := p) (v := v) hζ hp hpF hp2 hv))

end DivisibleResidue

end L20261018

#print axioms L20261018.knrResidueObligation_of_divisibleResidue
#print axioms L20261018.ch4TameSymbolHyp_of_divisibleResidue
#print axioms L20261018.ch4TameSymbolHyp_of_finite'
