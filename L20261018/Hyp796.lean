import L20261018.Hyp795

/-!
# S77 R4：第 5 步 (c) **杯积的载体比较** —— `∂²(cup y π)` 落成 `explicitCup01`

## 靶子

`PROMPT-S77` §1.4 把第 5 步 (c) 标为「**还差一条 cup 的载体比较**」：

```
GaloBase.cup = muPairing.cup 1 1  ⟷  连续侧 (ofDiscreteModulePairing mulPairing _).cup 1 1
```

本件**不需要**自建：库内 `Cup/Comparison.lean:319` 的 **`explicitAddEquiv_cup11`**
（NSW (1.4.2)）＋ 本战役 `Hyp156.cup_compat_theta_free` 恰好把这条比较**夹出来**。

## 路线（三块，全部库内／本战役已有）

```
GaloBase.cup x y
  = Θ₂⁻¹( cupLin (Θ₁x) (Θ₁y) )                    ← Hyp156.cup_compat_theta_free
      где Θ₁ = h1ToVEquiv.symm，Θ₂⁻¹ = (muP).explicitH2AddEquivContinuousCohomologyOfDiscrete
  ⟹ (rsie).symm (GaloBase.cup x y)
      = e₂ ( cupLin (Θ₁x) (Θ₁y) )                  ← 本件 `t1`（两个 ℤ/ZMod p 比较一致）
  ⟹ deltaTwoGaloBase' (GaloBase.cup x y)
      = deltaTwoCarrierInertia ( e₂ (cupLin (Θ₁x)(Θ₁y)) )
```

再把 `x := h1ToVEquiv (explicitInfl1 yb)`、`y := kummerClass π`、`Θ₁ y = e₁⁻¹ πc` 代入，
用 **`cupLin` 的斜对称**（`Hyp92.cupLin_skew`）把变量顺序摆成 `Hyp790` 的形状，
即得

```
deltaTwoGaloBase' (cup (Inf yb) π) = − explicitCup01 … (explicitCoeff0 contMHom z) yb
```

**⟹ 第 5 步 (c) 的载体比较已闭**：`projLin` 的取值就是一条 `explicitCup01`，
符号为 `−`（来自 `(1,1)` 杯积的斜对称，与 GS 用 `−π` 归一化同源）。

## 交付

| 声明 | 内容 |
|---|---|
| `zsie_symm_cup_eq` | ★★★★★ `(rsie).symm (cup x y) = e₂ (cupLin (Θ₁x) (Θ₁y))`（**cup 的载体比较**） |
| `cup11A_eq_e2_cupLin` | ★★★★ `cup11A (e₁ a) (e₁ b) = e₂ (cupLin a b)`（`explicitAddEquiv_cup11` 的 `cupLin` 形态） |
| **`deltaTwoGaloBase'_cup_eq_neg_explicitCup01`** | ★★★★★★ `∂²(cup (Inf yb) π) = − explicitCup01 …(contM-coeff)·yb` —— 第 5 步 (c) 的主桥 |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS77R4 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS77R4 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-! ## 1 两个 ℤ／`ZMod p` 比较一致（`rsie` 与 `ofDiscreteModuleRestrictScalarsIntEquiv`）

`h2ToGaloBase = e₂.trans rsie`，而 `explicitH2AddEquivContinuousCohomologyOfDiscrete muP
= e₂.trans ofDiscreteModuleRestrictScalarsIntEquiv`。两者的差别只是
`ofDiscreteModuleRestrictScalarsIntIso` 的 `eqToIso` 因子的位置——因此 `rsie.symm` 作用后一致。 -/

/-- ★★★★ **两个二次比较一致**：`(rsie).symm (e₂^muP w) = e₂ w`。

`ofDiscreteModuleRestrictScalarsIntEquiv_apply` 把 `e₂^muP` 展开成
`rsie (eqToHom … (e₂ w))`；`eqToHom` 在载体上是恒等（`rfl`）。 -/
theorem zsie_symm_explicitH2OfDiscrete (w : H2 (AbsoluteGaloisGroup F) (ZMod p)) :
    (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2).symm
      ((GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete w)
    = explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) w := by
  rw [show (GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete w
      = ofDiscreteModuleRestrictScalarsIntEquiv (GaloBase.muP F p) 2
        (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) w) from rfl,
    ofDiscreteModuleRestrictScalarsIntEquiv_apply, AddEquiv.symm_apply_apply]
  rfl

/-! ## 2 **cup 的载体比较** -/

/-- ★★★★★ **`GaloBase.cup` 在连续载体上就是 `e₂ ∘ cupLin`**。

`Hyp156.cup_compat_theta_free` 给 `Θ₂(cup x y) = cupLin (Θ₁x) (Θ₁y)`；取 `Θ₂⁻¹` 得
`cup x y = e₂^muP (cupLin …)`，再用 `zsie_symm_explicitH2OfDiscrete` 换掉 `rsie.symm`。 -/
theorem zsie_symm_cup_eq (x y : GaloBase.V F p) :
    (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2).symm
      (GaloBase.cup (K := F) (p := p) x y)
    = explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
        (Theo352.cupLin (p := p) ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm x)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm y)) := by
  have h := cup_compat_theta_free (F := F) p x y
  rw [theta2_free_apply] at h
  have h1 : GaloBase.cup (K := F) (p := p) x y
      = (GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete
          (Theo352.cupLin (p := p) (theta1_free p x) (theta1_free p y)) := by
    rw [← h, AddEquiv.apply_symm_apply]
  rw [h1, zsie_symm_explicitH2OfDiscrete, theta1_free_apply, theta1_free_apply]

/-- ★★★★ **`cup11A (e₁a) (e₁b) = e₂ (cupLin a b)`**：库内 `explicitAddEquiv_cup11` 的
`cupLin` 形态（配对 `mulPairing` 与 `GaloCup.zmodMulPairing` 在值上同为乘法，`rfl` 级）。 -/
theorem cup11A_eq_e2_cupLin (a b : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    ((ofDiscreteModulePairing (mulPairing (p := p)) (mulPairing_equivariant (F := F) p)).cup 1 1)
        ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) a)
        ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) b)
      = explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          (Theo352.cupLin (p := p) a b) := by
  rw [Theo352.cupLin_apply]
  exact explicitAddEquiv_cup11 (G := AbsoluteGaloisGroup F) (M := ZMod p) (N := ZMod p)
    (P := ZMod p) (mulPairing (p := p)) (mulPairing_equivariant (F := F) p) a b

/-! ## 3 第 5 步 (c) 的主桥 -/

variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★★★★ **`∂²(cup (Inf yb) π) = − explicitCup01 …(contM-系数)·yb`**（第 5 步 (c) 的主桥）。

装配顺序：`deltaTwoGaloBase'_apply`（拆 `rsie`）→ `zsie_symm_cup_eq`（cup 载体比较）→
`Θ₁ (h1ToVEquiv (explicitInfl1 yb)) = explicitInfl1 yb` → `cupLin_skew`（摆顺序）→
`cup11A_eq_e2_cupLin` ＋ `hπc`（把 `e₁(Θ₁π)` 认成 `πc`）→ **`Hyp790`**（GS 6.8.4 `p=q=1`）。

符号 `−` 来自 `(1,1)` 杯积斜对称；GS 在 `prop-specialization-section` 的证明里用 `−π` 归一化，
与此同源（`LESSONS` D74 ③④）。 -/
theorem deltaTwoGaloBase'_cup_eq_neg_explicitCup01 (hcop : p.Coprime q)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    (hp : IsUnit (p : F)) {pi0 : Fˣ}
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (yb : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (pic : continuousCohomology 1
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)))
    (hpi : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z)) = pic)
    (hpic : explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
        ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
          (KummerBridge.kummerClass F p hp pi0)) = pic) :
    deltaTwoGaloBase' (F := F) p q hcop
        (GaloBase.cup (K := F) (p := p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p))
            (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) yb))
          (KummerBridge.kummerClass F p hp pi0))
      = - explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          (H1 ↥(inertiaLoc F) (ZMod p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (H1 ↥(inertiaLoc F) (ZMod p))
          (smulPairingH1 (F := F) p) (smulPairingH1_continuous (F := F) p)
          (smulPairingH1_quotient_smul (F := F) p)
          (explicitCoeff0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            (contInvC (F := F) p (inertiaLoc F)) (contMHom (F := F) p (inertiaLoc F)) z)
          yb := by
  rw [deltaTwoGaloBase'_apply, zsie_symm_cup_eq]
  rw [show (KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
        ((KummerBridge.h1ToVEquiv (F := F) (p := p))
          (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) yb))
      = explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) yb from
    AddEquiv.symm_apply_apply _ _]
  rw [Theo352.cupLin_skew, map_neg, map_neg, ← cup11A_eq_e2_cupLin, hpic]
  rw [deltaTwoCarrierInertia_cup_eq_value (F := F) (p := p) (q := q) (hcop := hcop) z yb pic hpi]

end L20261018
