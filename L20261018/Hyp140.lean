import Hyp139
import Hyp111

/-!
# R982：两个载体的**桥的第一段** —— Kummer 类在 `h1ToVEquiv` 下的像

第 4 章有两个载体：
- `GaloBase.V F p = continuousCohomology 1 (muP)`（`Hyp115`／`Hyp116`／`Hyp119`／`Hyp135` 用）；
- 显式 `ContCohomology.H1 (AbsoluteGaloisGroup F) (ZMod p)`（`Hyp111.thm_ramified_1`／`Hyp112` 用）。

**本轮确认它们不是同一类型**（`Check940` 实测：`rfl` 失败），必须经
`KummerBridge.h1ToVEquiv F p : H1 (AbsoluteGaloisGroup F) (ZMod p) ≃+ GaloBase.V F p` 搬运。

**本文件给出桥的第 1 段（`rfl` 级，免费）**：Kummer 类在两个载体上**逐点一致**
（因为 `GaloCup.kummerExplicit` 的定义就是 `kummerH1Equiv ((kummerMap a).toAdd)`，
而 `KummerBridge.kummerClass` 是同一个东西再过 `h1ToVEquiv`）。

**桥的第 2 段（下一轮）**：杯积相容 `Θ₂ (cupLin x y) = GaloBase.cup (Θ₁ x) (Θ₁ y)` ——
有了它就能把 `HenselResidueData` 沿 `(Θ₁, Θ₂, Θv)` 整体搬运，T4／T5 即不再接受 `D`。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **显式 Kummer 类就是 `kummerH1Equiv ∘ kummerMap`**（`kummerExplicit` 的定义）。 -/
theorem kummerExplicit_eq (hp : IsUnit (p : F)) (a : Fˣ) :
    GaloCup.kummerExplicit (F := F) (p := p) hp a
      = (KummerBridge.kummerH1Equiv F p hp) ((TauCeti.kummerMap F p hp a).toAdd) := rfl

/-- **桥的第 1 段**：`KummerBridge.kummerClass` 就是显式 Kummer 类沿 `h1ToVEquiv` 的像。 -/
theorem kummerClass_eq_h1ToVEquiv_kummerExplicit (hp : IsUnit (p : F)) (a : Fˣ) :
    KummerBridge.kummerClass F p hp a
      = KummerBridge.h1ToVEquiv F p (GaloCup.kummerExplicit (F := F) (p := p) hp a) := rfl

/-- 反向形式（供下游 `rw` 用）。 -/
theorem h1ToVEquiv_kummerExplicit_eq (hp : IsUnit (p : F)) (a : Fˣ) :
    KummerBridge.h1ToVEquiv F p (GaloCup.kummerExplicit (F := F) (p := p) hp a)
      = KummerBridge.kummerClass F p hp a := rfl

end L20261018
#print axioms L20261018.kummerClass_eq_h1ToVEquiv_kummerExplicit
