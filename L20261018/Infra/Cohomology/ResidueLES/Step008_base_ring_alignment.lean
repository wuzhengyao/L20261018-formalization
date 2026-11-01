import L20261018.Infra.Cohomology.ResidueLES.Step007_continuous_615

/-!
# S45 R9：★★★★★ **基环对齐在战役载体上开火** —— `ℤ`-基底 ⟷ `ZMod p`-基底

## 本件做什么

`S45-STATUS` §10 测出：TauCeti 的连续 `delta`／`dimensionShiftIso` 一律 **`ℤ`-基底**
（`ofDiscreteModule ℤ G M`），而战役的 `muP : TopRep (ZMod p) Γ` 是 **`ZMod p`-基底**，
两者 `TopModuleCat ℤ` vs `TopModuleCat (ZMod p)` **不 defeq**。
§11 测出库内有桥：`TauCeti.ContCohomology.restrictScalarsIntEquiv`
（`RestrictScalars.lean:360`）：

```
restrictScalarsIntEquiv (X : TopRep k G) (n : ℕ) :
  ↑(continuousCohomology n (TopRep.restrictScalarsInt.obj X)).toModuleCat
    ≃+ ↑(continuousCohomology n X).toModuleCat
```

本件把它**在战役的真实群／模上开火**，得 `H¹`、`H²` 两座的战役侧桥。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`restrictScalarsInt_muP`** | ★★★★ `TopRep.restrictScalarsInt.obj (muP F p) = ofDiscreteModule ℤ Γ ↥(ZMod p)` |
| **`contH1BaseBridge`** | ★★★★★ `H¹_cont(Γ,μ_p)` 的 `ℤ`-基底侧 `≃+` 战役的 `GaloBase.V` |
| **`contH2BaseBridge`** | ★★★★★ `H²_cont(Γ,μ_p)` 的 `ℤ`-基底侧 `≃+` 战役的 `GaloBase.H2` |

## 为什么这两座桥是 (A) 的入口

`Hyp547.contCoindBotDimensionShiftTwo`（连续版 (6.15)）与未来的连续 `delta`／`deltaZeroBar`
都住在 `ℤ`-基底侧；有了 `contH2BaseBridge`／`contH1BaseBridge` 才能在
**(F2)／(F1)／(d)** 的每一步把两侧对接 —— 这正是离散侧靠 `Rep` 单一基底「免费」得到、
而连续侧必须显式接的两处。

## 诚实边界

* 本件**不给** `∂₂`：连续 `deltaZeroBar`／(F2)／(F1)／(d) 仍未建（`S45-STATUS` §11 的 ③–⑥）。
* 桥只对齐**加法群**（`≃+`），不升级到 `ZMod p`-线性同构；下游若需线性结构须另加一次 `map_smul` 记账。
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

section BaseRingBridge

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- ★★★★ **基环受限就是把 `ZMod p`-基底换成 `ℤ`-基底**：
`restrictScalarsInt.obj (muP F p)` 就是 `ofDiscreteModule ℤ Γ ↥(ZMod p)`。

这把战役载体（`muP`）与 TauCeti 连续 API 的基底（`ℤ`）对上，中间不需要任何转换数据。 -/
theorem restrictScalarsInt_muP :
    TopRep.restrictScalarsInt.obj (GaloBase.muP (K := F) (p := p))
      = TauCeti.ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p) := (rfl)

/-- ★★★★★ **`H¹` 的基环桥**：`ℤ`-基底侧 `≃+` 战役的 `GaloBase.V`。 -/
noncomputable def contH1BaseBridge :
    ↥(continuousCohomology 1
        (TauCeti.ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p))).toModuleCat
      ≃+ GaloBase.V F p :=
  restrictScalarsIntEquiv (GaloBase.muP (K := F) (p := p)) 1

/-- ★★★★★ **`H²` 的基环桥**：`ℤ`-基底侧 `≃+` 战役的 `GaloBase.H2`。 -/
noncomputable def contH2BaseBridge :
    ↥(continuousCohomology 2
        (TauCeti.ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p))).toModuleCat
      ≃+ GaloBase.H2 F p :=
  restrictScalarsIntEquiv (GaloBase.muP (K := F) (p := p)) 2

end BaseRingBridge

end L20261018

#print axioms L20261018.restrictScalarsInt_muP
#print axioms L20261018.contH1BaseBridge
#print axioms L20261018.contH2BaseBridge
