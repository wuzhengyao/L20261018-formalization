import Hyp237

/-!
# R1109（**★★★ (R2)-1 第三块：`H⁰` 的共轭相容性 —— `∂₂` 最后一条技术障碍清除**）

## 目标

`Hyp237.deltaZero_conj` 给出 `conjMap A S g (δ₀ x) = δ₀ (conjMap C g x)`（`x ∈ H⁰(S,C)`）。
要把 `δ₀` 组装成 `Rep k (G ⧸ S)`-态射 `C^S ⟶ H¹(S,A)`，还差一步：把 `H⁰(S,C)`
与 `C^S`（`Rep.dimensionShiftUp A` 的不变元）认同起来，且要求该认同**与共轭作用相容**：

```
(H0Iso).inv (ρ_C g z) = conjMap C S g 0 ((H0Iso).inv z)          (z ∈ C^S)
```

这正是本轮的 `H0_conj`。**它是一条纯 `H⁰` 计算**（零次余链都是「常值于不变元」），
不含任何数学假设。

## 证明路线（照 mathlib 的显式件）

1. `H0Iso.inv` 经 `π` 表出：`(H0Iso A).inv z = π A 0 ((cocyclesIso₀ A).inv z)`（`H0Iso_inv_eq_pi`，
   由 `π_comp_H0Iso_hom` ＋ `H0Iso` 是同构）。
2. 用 `π_map` 把 `conjMap` 推到余链层（`cocyclesMap`）。
3. 在 `cocycles A 0` 层比较：`iCocycles` 是单射，故只需比 `iCocycles`-像。
   `iCocycles_cocyclesMap`（`cyclesMap_i` 的自然性）＋ `iCocycles_cocyclesIso₀_inv`
   （`cocyclesIso₀_inv_comp_iCocycles`）把两侧都化成 `cochainsIso₀`-层。
4. 余链层：`cochainsMap_apply` 给出 `(cochainsMap f φ).f i z = fun j => φ (z (f ∘ j))`；
   而 `cochainsIso₀.inv a = fun _ => a`（`Fin 0` 是空类型 ⟹ 唯一 0-余链是常值）。
   ⟹ 两侧都是「常值于 `ρ_C g z`」。

## 本轮

| 声明 | 内容 |
|---|---|
| **`cochainsMap_apply`** | 余链映射在元素上的取值公式 |
| **`H0Iso_inv_eq_pi`** | `(H0Iso A).inv z = π A 0 ((cocyclesIso₀ A).inv z)` |
| **`iCocycles_cocyclesMap`** | `iCocycles` 关于 `cocyclesMap` 的自然性 |
| **`iCocycles_cocyclesIso₀_inv`** | `iCocycles ((cocyclesIso₀ A).inv z) = (cochainsIso₀ A).inv z.1` |
| **`H0_conj`** | ★★★ `conjMap C S g 0 ((H0Iso A).inv z) = (H0Iso A).inv (ρ_C g z)` |

**下一轮**：组装 —— `δ₀bar : (Rep.dimensionShiftUp A).quotientToInvariants S ⟶ h1RepQuot A S 1 h`
（`Rep k (G⧸S)`，用 `H0_conj` ＋ `deltaZero_conj`），再作
`deltaTwo : H²(G,A) ⟶ H¹(G⧸S, H¹(S,A))`（**GS 原文是「映射」不是同构**，tex `:9499`）。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- **余链映射在元素上的取值公式**：`(cochainsMap f φ).f i z = fun j => φ (z (f ∘ j))`。 -/
theorem cochainsMap_apply (A B : Rep k G) (f : G →* G)
    (φ : Rep.res f A ⟶ B) (i : ℕ)
    (z : (groupCohomology.inhomogeneousCochains A).X i) :
    ((groupCohomology.cochainsMap f φ).f i) z = fun j => φ (z (f ∘ j)) := by
  simp only [groupCohomology.cochainsMap_f]
  funext j
  simp

/-- ★ **`H⁰` 的 `π`-表出**：`(H0Iso A).inv z = π A 0 ((cocyclesIso₀ A).inv z)`。 -/
theorem H0Iso_inv_eq_pi (C : Rep k G) (z : C.ρ.invariants) :
    (groupCohomology.H0Iso C).inv z
      = groupCohomology.π C 0 ((groupCohomology.cocyclesIso₀ C).inv z) := by
  have h1 : (groupCohomology.H0Iso C).hom ((groupCohomology.H0Iso C).inv z) = z :=
    (groupCohomology.H0Iso C).inv_hom_id_apply z
  have h2 : (groupCohomology.H0Iso C).hom
      (groupCohomology.π C 0 ((groupCohomology.cocyclesIso₀ C).inv z)) = z := by
    have key : (groupCohomology.H0Iso C).hom
        (groupCohomology.π C 0 ((groupCohomology.cocyclesIso₀ C).inv z))
        = (groupCohomology.cocyclesIso₀ C).hom ((groupCohomology.cocyclesIso₀ C).inv z) := by
      rw [← groupCohomology.π_comp_H0Iso_hom C]
      rfl
    rw [key, (groupCohomology.cocyclesIso₀ C).inv_hom_id_apply z]
  exact (ModuleCat.mono_iff_injective _).1 inferInstance (h1.trans h2.symm)

/-- **`iCocycles` 关于 `cocyclesMap` 的自然性**（`HomologicalComplex.cyclesMap_i` 的元素形式）。 -/
theorem iCocycles_cocyclesMap (A : Rep k G) (f : G →* G) (φ : Rep.res f A ⟶ A)
    (c : groupCohomology.cocycles A 0) :
    groupCohomology.iCocycles A 0 (groupCohomology.cocyclesMap f φ 0 c)
      = ((groupCohomology.cochainsMap f φ).f 0) (groupCohomology.iCocycles A 0 c) := by
  have h := HomologicalComplex.cyclesMap_i (groupCohomology.cochainsMap f φ) 0
  exact congrArg (fun t => t c) h

/-- **`iCocycles` 把 `cocyclesIso₀`-逆送到 `cochainsIso₀`-逆**（`cocyclesIso₀_inv_comp_iCocycles`）。 -/
theorem iCocycles_cocyclesIso₀_inv (A : Rep k G) (z : A.ρ.invariants) :
    groupCohomology.iCocycles A 0 ((groupCohomology.cocyclesIso₀ A).inv z)
      = (groupCohomology.cochainsIso₀ A).inv z.1 := by
  have h := congrArg (fun t => t z) (groupCohomology.cocyclesIso₀_inv_comp_iCocycles A)
  rw [ModuleCat.comp_apply] at h
  exact h.trans rfl

/-- ★★★ **`H⁰` 的共轭相容性**：`(H0Iso).inv` 把 `C^S` 上的 `G`-作用（`ρ_C g`）送到
`H⁰(S,C)` 上的共轭作用（`conjMap C S g 0`）。

有了它，`Hyp237.deltaZero_conj` 才能升级为「`δ₀` 是 `Rep k (G ⧸ S)`-态射」：
`δ₀bar (ρ_C g z) = δ₀ (conjMap C g ((H0Iso).inv z)) = conjMap A g (δ₀bar z)`。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:3580 quote="is an exact sequence of $G/H$-modules, where the groups $H^{i}(H,A)$ are equipped with the conjugation action defined above."
theorem H0_conj (C : Rep k G) (S : Subgroup G) [S.Normal] (g : G)
    (z : (Rep.res S.subtype C).ρ.invariants) :
    conjMap C S g 0 ((groupCohomology.H0Iso (Rep.res S.subtype C)).inv z)
      = (groupCohomology.H0Iso (Rep.res S.subtype C)).inv
          ((Rep.toInvariants C S).ρ g z) := by
  -- 第 2 步：`π_map` 把 `conjMap` 推到余链层
  have hpi : conjMap C S g 0
      (groupCohomology.π (Rep.res S.subtype C) 0
        ((groupCohomology.cocyclesIso₀ (Rep.res S.subtype C)).inv z))
      = groupCohomology.π (Rep.res S.subtype C) 0
        (groupCohomology.cocyclesMap (conjSubtypeHom S g) (conjCoeffHom C S g) 0
          ((groupCohomology.cocyclesIso₀ (Rep.res S.subtype C)).inv z)) := by
    have h := congrArg
      (fun t => t ((groupCohomology.cocyclesIso₀ (Rep.res S.subtype C)).inv z))
      (groupCohomology.π_map (A := Rep.res S.subtype C) (B := Rep.res S.subtype C)
        (conjSubtypeHom S g) (conjCoeffHom C S g) 0)
    simpa [conjMap, ModuleCat.comp_apply] using h
  rw [H0Iso_inv_eq_pi, H0Iso_inv_eq_pi, hpi]
  congr 1
  -- 第 3 步：`iCocycles` 是单射，降到 `cocycles A 0`
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (Rep.res S.subtype C) 0)).1 inferInstance
  rw [iCocycles_cocyclesMap, iCocycles_cocyclesIso₀_inv, iCocycles_cocyclesIso₀_inv]
  -- 第 4 步：`Fin 0` 是空类型 ⟹ 唯一 0-余链是常值
  rw [cochainsMap_apply]
  rfl

end L20261018

#print axioms L20261018.cochainsMap_apply
#print axioms L20261018.H0Iso_inv_eq_pi
#print axioms L20261018.iCocycles_cocyclesMap
#print axioms L20261018.iCocycles_cocyclesIso₀_inv
#print axioms L20261018.H0_conj
