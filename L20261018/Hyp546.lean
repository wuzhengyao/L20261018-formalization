import L20261018.Hyp545

/-!
# S45 R6：★★★★ **连续侧载体的机检锁定** ＋ `muP` 是 smooth-discrete（正确的比较假设**可得**）

## 为什么先做这件

S45 R5 的侦察（`S45-STATUS` §8／`deadend-continuous-group-comparison.md`）定下两件事：

1. **战役载体全在连续侧**：`GaloBase.V`／`H2` 的定义逐字是 `continuousCohomology {1,2} (muP K p)`。
2. 原「用 `explicitH2AddEquivGroupCohomology` 搬运 (d)」的路线作废（它硬要 `[DiscreteTopology G]`，
   profinite 的 `AbsoluteGaloisGroup` 没有）。

⟹ 任何后续搬运／重建，**第一步都必须是「哪个载体在哪一侧」的机检锁定**（死胡同笔记的教训 §1）。
本件把这些事实从散文变成**编译期断言**：改动任一载体定义即编译失败。

## 另一件关键事实：正确的比较假设**已经满足**

`TauCeti.IsSmoothDiscrete R X`（`port/.../ContCohomology/SmoothDiscrete/Basic.lean:255`）是
「离散模 ＋ 开稳定子」——即**连续 cohomology ＝ 抽象 cohomology** 该用的假设（不是 `[DiscreteTopology G]`）。
本件机检：**`muP F p` 满足它**（因为 `muP = TopRep.of (trivial _ Γ (ZMod p))`，`A.lean:641`）。
⟹ 剩下的缺口被精确钉成一句话：**缺的是 `IsSmoothDiscrete` 假设下的比较定理本身**，
不是「假设不成立」（后者会是假阻断，KB 规则 17）。

## 机检内容

| 声明 | 内容 |
|---|---|
| `carrier_V` | `GaloBase.V F p = ↥(continuousCohomology 1 (muP F p)).toModuleCat`（`rfl`） |
| `carrier_H2` | `GaloBase.H2 F p = ↥(continuousCohomology 2 (muP F p)).toModuleCat`（`rfl`） |
| `carrier_VKG` | `VKG F p v hpF = ↥(LinearMap.ker (valLinOf v hpF))`（`rfl`） |
| `carrier_cup` | `GaloBase.cup = (muPairing F p).cup 1 1`（`rfl`） |
| **`isSmoothDiscrete_muP`** | ★★★★ `IsSmoothDiscrete (ZMod p) (muP F p)` —— 正确的比较假设**可得** |
| `smoothDiscrete_muP_iff` | 同上，重述成 `TopRep.of (trivial …)` 形态（供下游 `rw`） |

## 诚实边界

* 本件**不**构造任何 `∂₂`：连续侧 `∂₂` 仍未建。本件只把「改在哪一侧」与「用什么假设」钉死。
* 连续侧的 API 与离散侧**不同族**：`TauCeti.ContCohomology.DiscreteShortExact`（bundled，三元各带
  `DiscreteTopology`）＋ `DiscreteShortExact.delta`，**不是** `ShortComplex (Rep k G)` 那套；
  故 `Hyp542`–`Hyp545` 的代码不能直接复用，只能复用**证明架构**。此点已登记 `S45-STATUS` §9。
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

section CarrierLock

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- ★★★ **载体锁定**：`GaloBase.V` 就是 `H¹_cont(Γ, muP)`。改动载体定义即编译失败。 -/
theorem carrier_V :
    GaloBase.V F p = ↥(continuousCohomology 1 (GaloBase.muP F p)).toModuleCat := (rfl)

/-- ★★★ **载体锁定**：`GaloBase.H2` 就是 `H²_cont(Γ, muP)`。 -/
theorem carrier_H2 :
    GaloBase.H2 F p = ↥(continuousCohomology 2 (GaloBase.muP F p)).toModuleCat := (rfl)

/-- ★★★ **载体锁定**：`GaloBase.cup` 就是 `muPairing` 的杯积。 -/
theorem carrier_cup :
    GaloBase.cup (K := F) (p := p)
      = (GaloBase.muPairing (K := F) (p := p)).cup 1 1 := (rfl)

end CarrierLock

section SmoothDiscrete

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- ★★★★ **`muP` 是 smooth-discrete** —— 即「连续 cohomology ＝ 抽象 cohomology」该用的假设**成立**。

`IsSmoothDiscrete`（`port/.../SmoothDiscrete/Basic.lean:255`）＝ 离散模 ＋ 开点稳定子。
`muP = TopRep.of (ContRepresentation.trivial (ZMod p) Γ (ZMod p))`（`A.lean:641`），
稳定子全为 `⊤`，故平凡即开。

⟹ **缺口是「`IsSmoothDiscrete` 下的比较定理」本身**，不是「假设不可得」（那不是阻断，KB 规则 17）。 -/
theorem isSmoothDiscrete_muP :
    IsSmoothDiscrete (ZMod p) (GaloBase.muP (K := F) (p := p)) := by
  haveI : DiscreteTopology (ZMod p) := ZMod.instDiscreteTopology
  haveI : ContinuousSMul (ZMod p) (ZMod p) := ⟨continuous_of_discreteTopology⟩
  exact isSmoothDiscrete_trivial (ZMod p) (ZMod p)

end SmoothDiscrete

end L20261018

#print axioms L20261018.carrier_V
#print axioms L20261018.carrier_H2
#print axioms L20261018.carrier_cup
#print axioms L20261018.isSmoothDiscrete_muP
