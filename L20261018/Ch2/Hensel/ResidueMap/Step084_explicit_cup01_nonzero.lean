import L20261018.Ch2.Hensel.ResidueMap.Step083_left_inverse_coeff_map

/-!
# S77 R7：第 5 步 (b) **完成** —— `explicitCup01` 在 `(contM z, yb)` 上非零

## 内容

把 `Hyp797`（一般形的非零性）与 `Hyp798`（左逆系数映射的存在性）接起来：

```
m := explicitCoeff0 contMHom z        -- = contM z.1 ≠ 0（Hyp795 ＋ coe_explicitCoeff0）
e  := Hyp798.exists_leftInverse_coeff … m hm      -- e (x • m) = x
⟹ explicitCup01 (smulPairingH1) m yb ≠ 0          -- yb ≠ 0
```

**⟹ 第 5 步 (b) 关闭**。与 `Hyp796` 合起来即
`projLin y = −explicitCup01 … ≠ 0`，再走 `Hyp779.exists_leftInverse_of_injective` ⟹ `hcup`。

## 交付

| 声明 | 内容 |
|---|---|
| **`explicitCup01_contM_ne_zero`** | ★★★★★★ `yb ≠ 0 ⟹ explicitCup01 …(explicitCoeff0 contMHom z)·yb ≠ 0` |
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

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
variable (hcop : p.Coprime q)

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS77R7 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS77R7 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- 技术实例：`μ_pᴵ` 上 `Γ⧸I` 连续作用（`PROMPT-S77` §3 已登记）。 -/
local instance instContSmulMuPInvS77R7 :
    ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) :=
  inferInstance

/-- ★★★★★★ **第 5 步 (b)**：`explicitCup01` 在 `(contM z, yb)` 上非零（`yb ≠ 0`）。

`m := explicitCoeff0 contMHom z` 的底层是 `contM z.1 ≠ 0`（`Hyp795`），故
`Hyp798` 给出左逆 `e`，`Hyp797` 立即给出非零性。 -/
theorem explicitCup01_contM_ne_zero (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' ζ : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers ζ = ⊤)
    (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p)
    {pi0 : Fˣ} (hpi : TauCeti.normalizedValuation F pi0 = Multiplicative.ofAdd (1 : ℤ))
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp pi0)))
    {yb : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))} (hyb : yb ≠ 0) :
    explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        (H1 ↥(inertiaLoc F) (ZMod p))
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
        (H1 ↥(inertiaLoc F) (ZMod p))
        (smulPairingH1 (F := F) p) (smulPairingH1_continuous (F := F) p)
        (smulPairingH1_quotient_smul (F := F) p)
        (explicitCoeff0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          (contInvC (F := F) p (inertiaLoc F)) (contMHom (F := F) p (inertiaLoc F)) z)
        yb ≠ 0 := by
  -- `m` 的底层 = `contM z.1 ≠ 0`
  have hm : (explicitCoeff0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (contInvC (F := F) p (inertiaLoc F)) (contMHom (F := F) p (inertiaLoc F)) z
      : H1 ↥(inertiaLoc F) (ZMod p)) ≠ 0 := by
    rw [coe_explicitCoeff0]
    exact contM_ne_zero (F := F) (p := p) hp hpq' hpi z hδ
  -- `ξ` 的坐标映射
  obtain ⟨e, hec, hleft⟩ :=
    exists_leftInverse_coeff (F := F) (p := p) (q := q) hpq ζ hζ hgen hm
  exact explicitCup01_ne_zero_of_leftInverse (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (M := H1 ↥(inertiaLoc F) (ZMod p))
    (N := ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (P := H1 ↥(inertiaLoc F) (ZMod p))
    (smulPairingH1 (F := F) p) (smulPairingH1_continuous (F := F) p)
    (smulPairingH1_quotient_smul (F := F) p) _ e hec hleft hyb

end L20261018
