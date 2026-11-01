import Hyp546

/-!
# S45 R7：★★★★ **连续版 (6.15) 在战役群／模上开火** ＋ 基环对齐的**决定性测度**

## 测到的三件事（全部机检）

| # | 事实 | 机检形态 |
|---|---|---|
| 1 | **`muP F p = ofDiscreteModule (ZMod p) Γ ↥(ZMod p)`**（`rfl`） | `muP_eq_ofDiscreteModule` |
| 2 | **`CompactSpace (AbsoluteGaloisGroup F)` 可得**（`dimensionShiftIso` 的硬条件之一） | `compactSpace_absoluteGaloisGroup` |
| 3 | ★★★★ **`dimensionShiftIso` 在 `Γ = AbsoluteGaloisGroup F`、`M = ↥(ZMod p)` 上开火** ⟹ **连续版 (6.15) 存在** | `contCoindBotDimensionShiftTwo` |

## 仍未对齐的一处（**决定性负读数**）

`DiscreteShortExact.delta`／`dimensionShiftIso` 的载体是 **`ofDiscreteModule ℤ G M`**（`ℤ`-基底），
而战役的 `muP : TopRep (ZMod p) Γ`。实测（R7 探针，`/tmp/p7b.lean`）：

```
continuousCohomology 1 (ofDiscreteModule ℤ Γ ↥(ZMod p))  :  TopModuleCat ℤ
continuousCohomology 1 (muP F p)                          :  TopModuleCat (ZMod p)     -- 不同！
```

即 **`ℤ`-基底与 `ZMod p`-基底之间不是 defeq**（两个不同的 `TopModuleCat`）。
⟹ 还差一件**基环对齐**：`continuousCohomology n (ofDiscreteModule ℤ G M) ≃+ continuousCohomology n (ofDiscreteModule R G M)`
（作为加法群）。库内候选：`ContCohomology/RestrictScalars.lean`、`Additive.lean`、`Torsion.lean`（**未核**，下一轮核）。

## 机检内容

| 声明 | 内容 |
|---|---|
| `muP_eq_ofDiscreteModule` | ★★ `muP = ofDiscreteModule (ZMod p) Γ ↥(ZMod p)`（`rfl`） |
| `compactSpace_absoluteGaloisGroup` | ★★ `CompactSpace (AbsoluteGaloisGroup F)` |
| **`contCoindBotDimensionShiftTwo`** | ★★★★ **连续版 GS (6.15)**：`H²_cont(Γ, μ_p) ≅ H¹_cont(Γ, CoindQuotient Γ ⊥ μ_p)`（`ℤ`-基底） |
| `contCoindBotDimensionShiftTwo_type_lock` | 源/靶锁定 |

## 诚实边界

* 本件只把连续版 (6.15) **摆好**；`∂₂` 本体（＝(6.15)⁻¹ ≫ infl⁻¹ ≫ `deltaZeroBar`）仍未建。
* 连续版 `(F2)`／`(F1)`／`(d)` 未做；且须用 `DiscreteShortExact` 而非 `ShortComplex`（`S45-STATUS` §9）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

section BaseRing

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- ★★ **`muP` 就是 `ofDiscreteModule (ZMod p) Γ ↥(ZMod p)`**（`rfl`）。

这把战役载体接上 TauCeti 的 `ofDiscreteModule` API（`coindShortExact`／`dimensionShiftIso` 都用它）。 -/
theorem muP_eq_ofDiscreteModule :
    GaloBase.muP (K := F) (p := p)
      = TauCeti.ofDiscreteModule (ZMod p) (AbsoluteGaloisGroup F) (ZMod p) := (rfl)

/-- ★★ `AbsoluteGaloisGroup F` 紧（profinite）—— `dimensionShiftIso`／`delta` 的硬条件之一。 -/
theorem compactSpace_absoluteGaloisGroup :
    CompactSpace (AbsoluteGaloisGroup F) := inferInstance

end BaseRing

section Continuous615

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- ★★★★ **连续版 GS (6.15)**（离散版 = `Hyp227.coindBot_dimensionShift_two`）：

`H²_cont(Γ, μ_p) ≅ H¹_cont(Γ, CoindQuotient Γ ⊥ μ_p)`，即
`0 → μ_p → Coind(μ_p) → C → 0` 的长正合列 + `Coind` 在 `Γ` 上无环给出的维数平移。

载体是 `ofDiscreteModule ℤ`（TauCeti 的连续 API 一律 `ℤ`-基底）；与战役的 `muP`（`ZMod p`-基底）
之间还差一件**基环对齐**（见文件头「决定性负读数」）。 -/
noncomputable def contCoindBotDimensionShiftTwo :
    continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p))
      ≅ continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F)
          (CoindQuotient (AbsoluteGaloisGroup F) ⊥ (ZMod p))) :=
  dimensionShiftIso (AbsoluteGaloisGroup F) (ZMod p) 1 (by norm_num)

/-- 源/靶类型锁定：改动任一处的次数或模即使本引理编译失败。 -/
noncomputable def contCoindBotDimensionShiftTwo_type_lock :
    (continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p))
      ≅ continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F)
          (CoindQuotient (AbsoluteGaloisGroup F) ⊥ (ZMod p)))) :=
  contCoindBotDimensionShiftTwo (F := F) p

end Continuous615

end L20261018

#print axioms L20261018.muP_eq_ofDiscreteModule
#print axioms L20261018.compactSpace_absoluteGaloisGroup
#print axioms L20261018.contCoindBotDimensionShiftTwo
#print axioms L20261018.contCoindBotDimensionShiftTwo_type_lock
