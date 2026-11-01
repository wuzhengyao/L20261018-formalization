import L20261018.Ch2.Hensel.Inertia.Step014_cd_p_inertia_instance
import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure

/-!
# S42 R13（**S1：载体对齐**）：战役 `inertiaLoc` ＝ TauCeti `inertiaSubgroup` 的像

## 本件做什么

战役的惯性群是 `Hyp380` 的 `inertiaLoc F = (KnrLoc F).fixingSubgroup`
（`KnrLoc F = TauCeti.maximalUnramifiedExtension F (SeparableClosure F)`）。
TauCeti 的惯性群是 `TauCeti.inertiaSubgroup F = (maximalUnramifiedExtension F (AlgebraicClosure F)).fixingSubgroup`
——**另一个载体**（`Gal(K^alg/K)` 而非 `Gal(Kˢ/K)`）。

本件机检二者**是同一个子群**（沿 TauCeti 的比较同构 `absoluteGaloisGroupRestrictEquiv`）：

```
TauCeti.map_inertiaSubgroup_absoluteGaloisGroupRestrictEquiv (K) :
  (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K) =
    (maximalUnramifiedExtension K (SeparableClosure K)).fixingSubgroup
```

而右端**逐字**就是 `inertiaLoc F`（`KnrLoc` 的定义）⟹ **S1 一步到位**。

## 为什么这一步重要

它把 **TauCeti 的整套驯惯性理论**接到战役载体上（R12 侦察到的 `Tame/Quotient.lean`）：

| TauCeti 件 | 内容 |
|---|---|
| `exists_topologicalClosure_zpowers_eq_tameInertia` | `I_K/P_K` **procyclic**（`∃τ`，其类拓扑生成驯惯性） |
| `tameInertiaHom`／`range_tameInertiaHom` | `I_K/P_K ≅ Ẑ^{(p')}(1) = ∏_{ℓ≠p}ℤ_ℓ` |
| `orderOf_restrictNormal_eq_ramificationIndex` | τ 在驯分歧层 `L` 上的阶 = `e(L/K)`（阶无界 ⟹ 无限） |
| `topologicalClosure_zpowers_sup_wildInertiaSubgroup` | τ ＋ 野惯性拓扑生成 `I_K` |

⟹ （★）＝「`I_K` 的 ℓ-Sylow（ℓ ≠ char κ）≅ `ℤ_ℓ`」**可在 TauCeti 载体上做，再沿本件的桥搬回战役载体**。

## 诚实边界

* 本件**只做载体对齐**，不证明（★）。
* 载体是 `IsNonarchimedeanLocalField`（完备）；论文的 `F` 是 Hensel ⟹ C2 搬运仍待做。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- ★★★★★ **S1（载体对齐）**：战役的惯性群 `inertiaLoc F` 等于 TauCeti 的 `inertiaSubgroup F`
沿比较同构 `absoluteGaloisGroupRestrictEquiv` 的像。

**⟹ TauCeti 的整套驯惯性理论（`Tame/Quotient.lean`）可直接用在战役载体上。** -/
-- @source file=scratch/lean-l20261018/serre-p67-prop7-cors.txt locator=line:8 quote="The group G_0/G_1 is cyclic, and is mapped isomorphically by theta_0 onto a subgroup of the group of roots of unity contained in L. Its order is prime to the characteristic of the residue field L."
theorem inertiaLoc_eq_map_inertiaSubgroup :
    inertiaLoc F
      = Subgroup.map (TauCeti.absoluteGaloisGroupRestrictEquiv F).toMonoidHom
          (TauCeti.inertiaSubgroup F) := by
  rw [TauCeti.map_inertiaSubgroup_absoluteGaloisGroupRestrictEquiv]

/-- 推论（**反向书写**，便于下游 `rw`）：`TauCeti.inertiaSubgroup` 的像就是战役的 `inertiaLoc`。 -/
theorem map_inertiaSubgroup_eq_inertiaLoc :
    Subgroup.map (TauCeti.absoluteGaloisGroupRestrictEquiv F).toMonoidHom
        (TauCeti.inertiaSubgroup F)
      = inertiaLoc F :=
  (inertiaLoc_eq_map_inertiaSubgroup F).symm

end L20261018

#print axioms L20261018.inertiaLoc_eq_map_inertiaSubgroup
#print axioms L20261018.map_inertiaSubgroup_eq_inertiaLoc
