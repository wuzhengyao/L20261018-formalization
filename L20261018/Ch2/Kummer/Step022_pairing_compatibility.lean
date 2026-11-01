import L20261018.Ch2.Hensel.ResidueMap.Step023_hens_residue_data_transport

/-!
# R985：**桥第 2b 段的第一步 —— 配对相容**（`zmodMulPairing_eq_muPairing`）

⚠ **本轮只落了第 1 步**：`cup_compat_muP` 被 **`LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup F)`
实例合成超时**（`synthInstance.maxHeartbeats` 20000 用尽）挡住，见 `ASSUMPTIONS.md` R985 的卡点登记。

R984 的配方落地，用一个**关键简化**：把 `Θ₁`／`Θ₂` 直接取成
`muP` 自己的 `OfDiscrete` 比较，于是杯积相容**就是** TauCeti 的
`TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete`（`Cup/RestrictScalars.lean:330`）
逐字应用，只剩两个技术点：
1. `GaloBase.cup = muPairing.cup 1 1` —— 定义相等；
2. `μ := GaloCup.zmodMulPairing` 与 `muPairing.bil` 相容（`zmodMulPairing_eq_muPairing`，两边都是 `ZMod p` 乘法）。

与 `h1ToVEquiv` 的连接已由 `Hyp128.muP_explicitH1_eq_restrictScalars` 给出（点态），
下一轮用它把 `Θ₁` 换成 `h1ToVEquiv`，即可喂给 `Hyp141.henselResidueDataTransport`。
-/

set_option maxHeartbeats 4000000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- **配对相容**：`zmodMulPairing` 与 `muPairing.bil` 在载体上一致（两边都是 `ZMod p` 乘法）。 -/
theorem zmodMulPairing_eq_muPairing (x y : (GaloBase.muP F p).V) :
    GaloCup.zmodMulPairing p x y = (GaloBase.muPairing F p).bil x y := by
  rfl

end L20261018
#print axioms L20261018.zmodMulPairing_eq_muPairing

