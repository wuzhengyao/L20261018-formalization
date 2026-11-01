import L20261018.Ch2.Hensel.ResidueMap.Step079_cont_m_eq_explicit_res

/-!
# S77 R3：第 5 步 (a) 的**结论** —— `contM z` 是 `H¹(I, μ_p)` 的**生成元**

## 靶子

第 5 步 (a) 的终点不是 `contM z = res₁V(π)` 本身，而是它的**推论**：

```
contM z ≠ 0          ∧          AddSubgroup.zmultiples (contM z) = ⊤
```

这两条是第 5 步 (b)（「生成元 × 非零类 ⟹ 杯积非零」）的**全部输入**。

## 打法（纯搬运）

```
contM z = res₁V(kummerClass π)                  ← Hyp794.contM_eq_res1V_kummerClass
res₁V(kummerClass π) ≠ 0                        ← Hyp775.res1V_kummerClass_ne_zero_of_uniformizer
zmultiples (res₁V(kummerClass π)) = ⊤           ← Hyp780.res1V_kummerClass_zmultiples_eq_top
```

`Hyp780` 的生成元性由「`Nat.card (H¹(I,ℤ/p)) = p` 是素数 ＋ 非零 ⟹ 生成」
（`Hyp761.zmultiples_eq_top_of_natCard_prime`）给出，**不是**新数学。

## 交付

| 声明 | 内容 |
|---|---|
| **`contM_ne_zero`** | ★★★★★ `contM z ≠ 0`（`π` 一致化元） |
| **`contM_zmultiples_eq_top`** | ★★★★★ `zmultiples (contM z) = ⊤`（**第 5 步 (a) 的终点**） |
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

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS77R3 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS77R3 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 紧（闭 ＋ `Γ` 紧）。 -/
local instance instCompactInertiaLocS77R3 : CompactSpace ↥(inertiaLoc F) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaLoc F).isCompact

/-- ★★★★★ **`contM z ≠ 0`**：`δ⁰(Inf z) = e₁(h1ToVEquiv.symm (kummerClass π))` 且 `π` 是一致化元。

`Hyp794` 把 `contM z` 换成 `res₁V(kummerClass π)`，非零性即
`Hyp775.res1V_kummerClass_ne_zero_of_uniformizer`（`p ∤ v(π) = 1`）。 -/
theorem contM_ne_zero
    (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp π))) :
    contM (F := F) p (inertiaLoc F) (z.1) ≠ 0 := by
  rw [contM_eq_res1V_kummerClass (F := F) (p := p) hp z hδ]
  exact res1V_kummerClass_ne_zero_of_uniformizer (F := F) (p := p) hp hpq' hπ

/-- ★★★★★★ **第 5 步 (a) 的终点**：`contM z` **生成** `H¹(I, ℤ/p)`。

由 `Hyp794` 换成 `res₁V(kummerClass π)`，再喂 `Hyp780`（`Nat.card` 素数 ＋ 非零 ⟹ 生成）。 -/
theorem contM_zmultiples_eq_top
    (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp π))) :
    AddSubgroup.zmultiples (contM (F := F) p (inertiaLoc F) (z.1)) = ⊤ := by
  rw [contM_eq_res1V_kummerClass (F := F) (p := p) hp z hδ]
  exact res1V_kummerClass_zmultiples_eq_top (F := F) (p := p) (q := q) hpq ζ hζ hgen hp hpq' hπ

end L20261018
