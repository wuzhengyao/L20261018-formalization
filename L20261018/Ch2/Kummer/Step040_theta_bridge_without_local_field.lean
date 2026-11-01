import L20261018.Witness.Step032_f7t_v_finite_dimensional
import L20261018.Ch4.Step006_thm_ramified_no_d

/-!
# R1274（S36 C 项 基建）：**`θ`-桥去 `[IsNonarchimedeanLocalField]`**

`Hyp145` 的 `theta1`／`theta2`／`cup_compat_theta`（以及 `cup_compat_muP_zmod`）的**证明**
只用系数载体的比较（`h1ToVEquiv`＋`explicitH*AddEquivContinuousCohomologyOfDiscrete`），
但**陈述**带了 `[IsNonarchimedeanLocalField F]`（该文件的 `linter.unusedSectionVars false` 掩盖了这一点）。

⟹ 在函数域例子 `F = 𝔽₇((t))`（**不是**局部域）上，`4.3(1)`／`4.4` 的 `hne` 需要的正是这座桥。
本文件按 `Hyp145` 的证明**逐字重证**（仅去掉实例假设）：

| 声明 | 内容 |
|---|---|
| `theta1g`／`theta2g` | `GaloBase.V ≃ₗ H¹`／`GaloBase.H2 ≃ₗ H²` |
| `theta1g_apply`／`theta2g_apply` | 定义层取值 |
| —— | **以下两步未落地**：`cup_compat_muP_zmod` 的底层引理 `TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete` 仍带 `[IsNonarchimedeanLocalField]`，需继续向下「去假设」（见 `HANDOFF` §S36 第 8 轮） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- `Θ₁`：`h1ToVEquiv` 的逆，升级为 `≃ₗ`。 -/
noncomputable def theta1g :
    GaloBase.V F p ≃ₗ[ZMod p] H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p) :=
  (KummerBridge.h1ToVEquiv F p).symm.toLinearEquiv (fun c x => ZMod.map_smul _ c x)

/-- `Θ₂`：`EH2OfDiscrete` 的逆，升级为 `≃ₗ`。 -/
noncomputable def theta2g :
    GaloBase.H2 F p ≃ₗ[ZMod p] H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p) :=
  ((GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete).symm.toLinearEquiv
    (fun c x => ZMod.map_smul _ c x)

@[simp] theorem theta1g_apply (x : GaloBase.V F p) :
    theta1g (F := F) p x = (KummerBridge.h1ToVEquiv F p).symm x := rfl

@[simp] theorem theta2g_apply (y : GaloBase.H2 F p) :
    theta2g (F := F) p y
      = ((GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete).symm y := rfl

end L20261018

