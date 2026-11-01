import L20261018.Ch2.Kummer.Step022_pairing_compatibility

/-!
# R986：**桥第 2b 段 —— 杯积相容 `cup_compat_muP` 落成**

R985 的卡点（`LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup F)` 实例合成 20k heartbeats 超时）
**只是心跳预算不足**：本轮 `set_option synthInstance.maxHeartbeats 400000` 后实例搜到
（`Check943` 实测：`CompactSpace` 与 `LocallyCompactSpace` 都过）。

于是杯积相容就是 TauCeti 的
`TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete`（`Cup/RestrictScalars.lean:330`）
逐字应用（`Θ₁`／`Θ₂` 取 `muP` 自己的两个 `OfDiscrete` 比较，`μ := GaloCup.zmodMulPairing`，
相容性由 `Hyp142.zmodMulPairing_eq_muPairing`（`rfl`）供给）。

**⟹ 桥的三段（Kummer 类／结构搬运／杯积相容）现已全部落成。**
下一轮把 `Θ₁` 换成 `h1ToVEquiv`（`Hyp128` 点态 + `AddEquiv → LinearEquiv` 转换），
即可喂 `Hyp141.henselResidueDataTransport` 而重演 T4／T5。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- **杯积相容（`muP` 形态）**：`GaloBase.cup` 与显式杯积 `explicitCup11` 在 `muP` 的
`H¹`／`H²` `OfDiscrete` 比较下一致。 -/
theorem cup_compat_muP (x y : H1 (TauCeti.AbsoluteGaloisGroup F) (GaloBase.muP F p).V) :
    GaloBase.cup (K := F) (p := p)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete x)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete y)
      = (GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete
          (explicitCup11 (TauCeti.AbsoluteGaloisGroup F) (GaloBase.muP F p).V
            (GaloBase.muP F p).V (GaloBase.muP F p).V (GaloCup.zmodMulPairing p)
            continuous_of_discreteTopology (fun _ _ _ => rfl) x y) :=
  TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete
    (GaloBase.muPairing F p) (GaloCup.zmodMulPairing p)
    (zmodMulPairing_eq_muPairing (F := F) (p := p)) x y

end L20261018
#print axioms L20261018.cup_compat_muP
