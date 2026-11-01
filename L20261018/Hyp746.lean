import L20261018.Hyp744
import L20261018.Hyp511
import TauCeti.NumberTheory.LocalField.Unramified.Kummer
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# S68 R1：**惯性限制 `res₁` 在战役载体上** —— `UnramifiedKummer` 的第一根支柱

## 本件做什么

`Hyp744.UnramifiedKummer` 说 `ker v̄ ⊆ range infl₁`。由**膨胀-限制正合列**（H¹ 层）
`range infl₁ = ker res₁`（`res₁` ＝ 限制到惯性 `I`），故它等价于 `ker v̄ ⊆ ker res₁`。
而 `ker res₁` 由 **TauCeti 的「不分歧 Kummer 理论」**
（`TauCeti/NumberTheory/LocalField/Unramified/Kummer.lean`）刻画为**单位类**：

> `explicitRes1_eq_zero_iff_exists_kummerMap`：
> 「在惯性上消失的 `H¹(G_K,μ_n)` 类 ⟺ 某个**单位**的 Kummer 类」。

于是 `ker v̄ = ker res₁` 归结为「`p ∣ v(a) ⟺ a` 的类可写成单位类」（`Hyp162.valLinOf_kummerClass`）。

## 本件交付（本文件只做**第一件**，其余见 `Hyp747`／`Hyp748`）

| 声明 | 内容 |
|---|---|
| `explicitRes1_explicitCoeff1Equiv_comp` | 系数等价与限制交换（`explicitMap1_comp` 的一般后果） |
| `res1V` | ★★★★ 惯性限制 `GaloBase.V F p →+ H¹(I, μ_p)`（战役载体，沿 `KummerBridge.h1ToVEquiv` 运回） |
| `res1V_kummerClass_eq_zero_iff` | ★★★★★ **`res1V (a) = 0 ⟺ (p:ℤ) ∣ v(a)`**（TauCeti 定理在战役载体上的形态） |

## 载体口径

* `Γ := AbsoluteGaloisGroup F`，`I := inertiaLoc F = (KnrLoc F).fixingSubgroup`（`Hyp380`）；
* `Hyp511.map_inertiaSubgroup_eq_inertiaLoc` 把 TauCeti 的
  `(inertiaSubgroup F).map (absoluteGaloisGroupRestrictEquiv F)` **逐字**认成 `inertiaLoc F`
  ⟹ TauCeti 的定理可直接用；
* 本件全部在 `[IsNonarchimedeanLocalField F]`（完备）下——与 `Hyp743`／`Hyp511` 同一层级。
  **Hensel-only 层级的搬运是后续轮**（`S68-GS-KUMMER-VALUATION.md` §6.3bis 的诚实边界）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

/-! ## 1 一般引理：系数等价与限制交换 -/

section Naturality

variable {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]

/-- ★★★★ **系数等价与限制交换**：`H¹(G,M) --e--> H¹(G,N) --res_S--> H¹(S,N)`
等于 `H¹(G,M) --res_S--> H¹(S,M) --e--> H¹(S,N)`。

（`explicitMap1_comp` 的直接后果；`explicitRes1 = explicitMap1 (subtype) id`、
`explicitCoeff1Equiv = explicitMap1 (id) e`。） -/
theorem explicitRes1_explicitCoeff1Equiv_comp (S : Subgroup G)
    (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
    (hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m) (x : H1 G M) :
    explicitRes1 G N S (explicitCoeff1Equiv G M e he he' hequiv x)
      = explicitCoeff1Equiv S M e he he' (fun s m => hequiv (s : G) m)
          (explicitRes1 G M S x) := by
  -- 展开两边的 `explicitMap1` 形态
  rw [explicitRes1_eq_explicitMap1, explicitRes1_eq_explicitMap1]
  rw [explicitCoeff1Equiv_apply, explicitCoeff1Equiv_apply, explicitCoeff1_eq_explicitMap1,
    explicitCoeff1_eq_explicitMap1]
  exact explicitMap1_explicitMap1_of_comp_eq G M G N
    (ContinuousMonoidHom.id G)
    ({ e.toAddMonoidHom with map_smul' := fun g m => hequiv g m } : M →+[G] N) he
    (fun g m => hequiv g m)
    ↥S N (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id N) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul N S)
    (ContinuousMonoidHom.subgroupSubtype S) (AddMonoidHom.id M) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul M S)
    (ContinuousMonoidHom.id ↥S)
    ({ e.toAddMonoidHom with map_smul' := fun s m => hequiv (s : G) m } : M →+[↥S] N) he
    (fun s m => hequiv (s : G) m)
    (ContinuousMonoidHom.ext fun s => rfl)
    (AddMonoidHom.ext fun m => rfl) x

end Naturality

/-! ## 2 战役载体上的惯性限制 `res1V` -/

section InertiaRestriction

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ **战役载体上的惯性限制**：`GaloBase.V F p = H¹(Γ, μ_p) →+ H¹(I, μ_p)`。

沿 `KummerBridge.h1ToVEquiv` 把 `GaloBase.V` 搬到显式 `H1 Γ (ZMod p)` 后取 `explicitRes1`。 -/
noncomputable def res1V :
    GaloBase.V F p →+ H1 ↥(inertiaLoc F) (ZMod p) :=
  (explicitRes1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)).comp
    (KummerBridge.h1ToVEquiv (F := F) (p := p)).symm.toAddMonoidHom

/-- `res1V` 的定义式（`h1ToVEquiv` 前像形态）。 -/
theorem res1V_apply (y : GaloBase.V F p) :
    res1V (F := F) (p := p) y
      = explicitRes1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm y) :=
  rfl

/-- `res1V` 把 `kummerClass` 送到 `explicitRes1 (kummerMap …)`（Kummer 系数比较的桥）。 -/
theorem res1V_kummerClass_eq (hp : IsUnit (p : F)) (a : Fˣ) :
    res1V (F := F) (p := p) (KummerBridge.kummerClass F p hp a)
      = explicitRes1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
          (KummerBridge.kummerH1Equiv (F := F) (p := p) hp
            (kummerMap F p hp a).toAdd) := by
  rw [res1V_apply]
  have h : (KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
      (KummerBridge.kummerClass F p hp a)
      = KummerBridge.kummerH1Equiv (F := F) (p := p) hp
          (kummerMap F p hp a).toAdd :=
    (KummerBridge.h1ToVEquiv (F := F) (p := p)).symm_apply_apply _
  rw [h]

end InertiaRestriction

end L20261018

#print axioms L20261018.explicitRes1_explicitCoeff1Equiv_comp
#print axioms L20261018.res1V
#print axioms L20261018.res1V_kummerClass_eq
