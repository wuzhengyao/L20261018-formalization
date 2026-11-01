import Hyp363

/-!
# R1275（S36 C 项 基建）：θ-桥的**真假设**是 `[LocallyCompactSpace (AbsGal F)]`

`Hyp145.cup_compat_theta` 带 `[IsNonarchimedeanLocalField F]`，但 `Hyp363` 的追踪显示底层
`TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete` 只要
`[DiscreteTopology]`×3 ＋ `[ContinuousSMul]`×3 ＋ **`[LocallyCompactSpace G]`**（`G = AbsGal F`）。
而 `AbsoluteGaloisGroup F` 对**任意**域都是紧的（Krull 拓扑、profinite）
⟹ 局部紧性**自动**成立（实测 `inferInstance` 过）。

⟹ 函数域 `F = 𝔽₇((t))`（**不是**局部域）上 θ-桥可用。

| 声明 | 内容 |
|---|---|
| **`cup_compat_theta_locallyCompact`** | ★★★★★ `θ₂(x ∪ y) = θ₁x ∪' θ₁y`（假设改为 `LocallyCompactSpace`） |
| **`theta1_kummerClass`** | `θ₁ (kc a) = kummerExplicit a`（同假设） |
| **`cup_compat_theta_F`** | ★★★★★★ 在 `𝔽₇((t))` 上的实例（局部紧性自动） |
| **`theta1_kummerClass_F`** | ★★★★★★ 在 `𝔽₇((t))` 上的实例 |
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

section LocallyCompact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup F)]
  (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- **`ZMod p` 口径的杯积相容**（`LocallyCompactSpace` 版）。 -/
theorem cup_compat_muP_zmod_lc (x y : H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :
    GaloBase.cup (K := F) (p := p)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete x)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete y)
      = (GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete
          (Theo352.cupLin (F := F) (p := p) x y) := by
  rw [Theo352.cupLin_apply]
  exact TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete
    (GaloBase.muPairing F p) (GaloCup.zmodMulPairing p) (fun x y => rfl) x y

/-- ★★★★★ **杯积相容（`LocallyCompactSpace` 版）**。 -/
theorem cup_compat_theta_locallyCompact (x y : GaloBase.V F p) :
    theta2g (F := F) p (GaloBase.cup (K := F) (p := p) x y)
      = Theo352.cupLin (F := F) (p := p)
          (theta1g (F := F) p x) (theta1g (F := F) p y) := by
  have hx : (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
      (theta1g (F := F) p x) = x := by
    rw [theta1g_apply, ← h1ToVEquiv_apply_eq_muP, AddEquiv.apply_symm_apply]
  have hy : (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
      (theta1g (F := F) p y) = y := by
    rw [theta1g_apply, ← h1ToVEquiv_apply_eq_muP, AddEquiv.apply_symm_apply]
  have h := cup_compat_muP_zmod_lc (F := F) (p := p)
    (theta1g (F := F) p x) (theta1g (F := F) p y)
  rw [hx, hy] at h
  rw [theta2g_apply, h]
  exact AddEquiv.symm_apply_apply _ _

/-- ★★★★★ **`Θ₁` 把 `kc a` 送回 `kummerExplicit a`**（`LocallyCompactSpace` 版）。 -/
theorem theta1_kummerClass_lc (hp : IsUnit (p : F)) (a : Fˣ) :
    theta1g (F := F) p (KummerBridge.kummerClass F p hp a)
      = GaloCup.kummerExplicit (F := F) (p := p) hp a := by
  rw [theta1g_apply]
  rw [show KummerBridge.kummerClass F p hp a
    = KummerBridge.h1ToVEquiv F p
        (GaloCup.kummerExplicit (F := F) (p := p) hp a) from rfl]
  exact AddEquiv.symm_apply_apply _ _

end LocallyCompact

namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- ★★★★★★ **`𝔽₇((t))` 上的杯积相容**（`AbsGal` 紧 ⟹ 局部紧，自动）。 -/
theorem cup_compat_theta_F (x y : GaloBase.V (LaurentSeries (ZMod 7)) 3) :
    theta2g (F := LaurentSeries (ZMod 7)) 3
        (GaloBase.cup (K := LaurentSeries (ZMod 7)) (p := 3) x y)
      = Theo352.cupLin (F := LaurentSeries (ZMod 7)) (p := 3)
          (theta1g (F := LaurentSeries (ZMod 7)) 3 x)
          (theta1g (F := LaurentSeries (ZMod 7)) 3 y) :=
  cup_compat_theta_locallyCompact (F := LaurentSeries (ZMod 7)) 3 x y

/-- ★★★★★★ **`𝔽₇((t))` 上 `Θ₁ (kc a) = kummerExplicit a`**。 -/
theorem theta1_kummerClass_F (a : (LaurentSeries (ZMod 7))ˣ) :
    theta1g (F := LaurentSeries (ZMod 7)) 3
        (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries a)
      = GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
          three_isUnit_laurentSeries a :=
  theta1_kummerClass_lc (F := LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries a

end FqXt
end L20261018

#print axioms L20261018.cup_compat_theta_locallyCompact
#print axioms L20261018.FqXt.cup_compat_theta_F
#print axioms L20261018.FqXt.theta1_kummerClass_F
