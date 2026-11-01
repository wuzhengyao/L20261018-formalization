import L20261018.Hyp793

/-!
# S77 R2：第 5 步 (a) **收口** —— `contM z = explicitRes1 x`（进而 `= res₁V(kummerClass π)`）

## 靶子（`PROMPT-S77` §1.2）

```
contM z = explicitRes1 (kummerClass π)
```

## 打法（三块桥全部已机检，本轮只是**装配**）

```
e₁ (contM z) = δ⁰_I (e₀^I z)                          ← Hyp576.contM_eq
             = δ⁰_I (res_I (e₀^Γ (Inf z)))            ← Hyp793.h0Emb_res_infl（反向）
             = res_I (δ⁰_Γ (e₀^Γ (Inf z)))            ← Hyp792.res_delta_zero_apply（反向）
             = res_I (e₁ x)                           ← hδ : δ⁰_Γ(Inf z) = e₁ x
             = e₁ (explicitRes1 x)                    ← Hyp791.e1_explicitRes1（反向）
```

`e₁ = explicitH1AddEquivContinuousCohomology ↥I (ZMod p)` 是**加法等价** ⟹ 单射 ⟹ 消去。

## 交付

| 声明 | 内容 |
|---|---|
| **`contM_eq_explicitRes1`** | ★★★★★ `δ⁰(Inf z) = e₁ x ⟹ contM z = explicitRes1 x`（第 5 步 (a) 的**全部内容**） |
| **`contM_eq_res1V_kummerClass`** | ★★★★★ 同上取 `x = h1ToVEquiv.symm (kummerClass π) ⟹ contM z = res₁V(kummerClass π)` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS77R2 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS77R2 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 紧（闭 ＋ `Γ` 紧）。 -/
local instance instCompactInertiaLocS77R2 : CompactSpace ↥(inertiaLoc F) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaLoc F).isCompact

/-- ★★★★★ **第 5 步 (a) 的全部内容**：若 `δ⁰(Inf z) = e₁ x`，则 `contM z = explicitRes1 x`。

四块桥按 `Hyp576.contM_eq → Hyp793.h0Emb_res_infl → Hyp792.res_delta_zero_apply →
Hyp791.e1_explicitRes1` 的顺序开火，最后由 `e₁`（加法等价）单射消去。 -/
theorem contM_eq_explicitRes1
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (x : H1 (AbsoluteGaloisGroup F) (ZMod p))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) x) :
    contM (F := F) p (inertiaLoc F) (z.1)
      = explicitRes1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) x := by
  refine (explicitH1AddEquivContinuousCohomology ↥(inertiaLoc F) (ZMod p)).injective ?_
  rw [contM_eq, e1_explicitRes1, ← hδ, res_delta_zero_apply, h0Emb_res_infl]

variable [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **`contM z = res₁V(kummerClass π)`**：上一条取
`x = h1ToVEquiv.symm (kummerClass π)`（`res₁V` 的定义即 `explicitRes1 ∘ h1ToVEquiv.symm`）。

之后 `Hyp780.res1V_kummerClass_zmultiples_eq_top` 直接给出 `contM z` 生成 `H¹(I, μ_p)`。 -/
theorem contM_eq_res1V_kummerClass
    (hp : IsUnit (p : F)) {π : Fˣ}
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp π))) :
    contM (F := F) p (inertiaLoc F) (z.1)
      = res1V (F := F) (p := p) (KummerBridge.kummerClass F p hp π) := by
  rw [res1V_apply]
  exact contM_eq_explicitRes1 (F := F) p z _ hδ

end L20261018
