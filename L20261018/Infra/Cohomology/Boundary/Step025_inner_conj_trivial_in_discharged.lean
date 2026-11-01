import L20261018.Infra.Cohomology.Boundary.Step024_prism_identity_on_cycles

/-!
# R1117（**★★★★★ (R2)-2 的 `n = 1` 收口完成 —— `innerConjTrivialIn` 被机检消去**）

## 里程碑

`PROMPT-S31` ② 的 **(R2)-2**（解除具名假设 `innerConjTrivialIn`）在 **`n = 1`** 处**完成**：

```
innerConjTrivialIn_one  :  innerConjTrivialIn A S 1            （无条件）
deltaTwoFree            :  H²(G,A) ⟶ H¹(G⧸S, H¹(S,A))         （唯一前提 = hcd，即 cd(S) ≤ 1）
```

⟹ **`(R2)` 不再依赖任何具名假设**：`∂₂` 的前提只剩论文自身的 `cd(S) ≤ 1`。

## 为什么 `n = 1` 就够

`deltaTwo`（`Hyp239`）里 `innerConjTrivialIn` **只出现在 `n = 1`**（`h1RepQuot A S 1 h`）。
全次数的 `innerConjTrivialIn` 仍是 `(R2)-2` 的完整目标，但 **`(R2)` 不需要它**。

## 收口链（S31 六轮，全机检）

| 步 | 内容 | 件 |
|---|---|---|
| ① | 余链层：`c_g f − f = d₀₁ (f g)`（棱柱算子 `h f = f g`） | `Hyp240.conj_one_cochain_sub` |
| ② | 余圈层：共轭后仍余圈且**同类** | `Hyp241.H1π_conjCocycle` |
| ③ | `d` 在 `Fin 1`／`Fin 2` 的取值公式 | `Hyp243` |
| a1 | `cycles 1` 的压缩函数 ∈ `cocycles₁` | `Hyp244.compressed_mem_cocycles` |
| a2 | 逐点 `(cochainsMap c_g φ).f 1 M − M = d 0 1 (M (·g))` | `Hyp245` |
| **a3** | **`cyclesMap c_g 1 w − w = toCycles 0 1 (M (·g))`** | **`cyclesMap_one_sub_eq_toCycles`** |
| **a4** | **(★) `cocyclesMap c_g 1 ≫ π = π`** | **`cyclesMap_one_comp_homologyπ`** |
| **a5** | **`conjMap A S g 1 = 𝟙` ⟹ `innerConjTrivialIn A S 1`** | **`innerConjTrivialIn_one`** |
| **a6** | **无具名假设的 `∂₂`** | **`deltaTwoFree`** |

## 与本轮相关的手法

a3 的三段：`(ModuleCat.mono_iff_injective (iCycles 1)).1 inferInstance` 降到 `X 1` 层 →
`map_sub` → `cyclesMap_i`（**对任意链映射**，非仅 `MonoidHom.id`）与 `toCycles_i` 把两端换成
`c_g.f 1 M − M` 与 `d 0 1 u` → **`Hyp245` 的逐点恒等式**（`funext`）。
a4：`ModuleCat.comp_apply` ＋ `sub_add_cancel`／`map_add` 的 `calc`，配 `toCycles_comp_homologyπ`。
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★★ **a3**：在 `cycles 1` 层，共轭链映射与恒等之差 = 一个 `toCycles` 像
（棱柱算子 `h w = M (·g)`，`M := iCycles 1 w`）。 -/
theorem cyclesMap_one_sub_eq_toCycles (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S)
    (w : (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).cycles 1) :
    HomologicalComplex.cyclesMap
        (groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom A S g)) 1 w - w
      = (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).toCycles 0 1
          (fun _ => ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)
            (fun _ => g)) := by
  apply (ModuleCat.mono_iff_injective
    (HomologicalComplex.iCycles (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)) 1)).1
    inferInstance
  rw [map_sub]
  rw [show (HomologicalComplex.iCycles
        (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)) 1)
        (HomologicalComplex.cyclesMap
          (groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom A S g)) 1 w)
      = ((groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom A S g)).f 1)
          ((HomologicalComplex.iCycles
            (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)) 1) w)
      from congrArg (fun m => m w)
        (HomologicalComplex.cyclesMap_i
          (groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom A S g)) 1)]
  have h2 := congrArg
    (fun m => m (fun _ => ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)
      (fun _ => g)))
    (HomologicalComplex.toCycles_i
      (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)) 0 1)
  rw [ModuleCat.comp_apply] at h2
  rw [h2]
  funext j
  exact cochainsMap_one_sub_apply A S g w j

/-- ★★★ **a4 ＝ (★)**：共轭余链映射在 `H¹` 上平凡，即 `cocyclesMap c_g 1 ≫ π = π`。

证明：对 `w : cycles 1`，`calc` 把 `π (cocyclesMap w)` 拆成
`π (cocyclesMap w − w) + π w`（`sub_add_cancel` ＋ `map_add`），再用 a3 与
`toCycles_comp_homologyπ`。 -/
theorem cyclesMap_one_comp_homologyπ (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S) :
    groupCohomology.cocyclesMap (conjSubtypeHom S g) (conjCoeffHom A S g) 1
      ≫ groupCohomology.π (Rep.res S.subtype A) 1
    = groupCohomology.π (Rep.res S.subtype A) 1 := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun w => ?_
  rw [ModuleCat.comp_apply]
  have h3 := cyclesMap_one_sub_eq_toCycles A S g w
  have hz : (groupCohomology.π (Rep.res S.subtype A) 1)
      ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).toCycles 0 1
        (fun _ => ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)
          (fun _ => g))) = 0 := by
    have h := congrArg
      (fun m => m (fun _ => ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)
        (fun _ => g)))
      (HomologicalComplex.toCycles_comp_homologyπ
        (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)) 0 1)
    rw [ModuleCat.comp_apply] at h
    exact h
  calc (groupCohomology.π (Rep.res S.subtype A) 1)
          ((groupCohomology.cocyclesMap (conjSubtypeHom S g) (conjCoeffHom A S g) 1) w)
      = (groupCohomology.π (Rep.res S.subtype A) 1)
          ((groupCohomology.cocyclesMap (conjSubtypeHom S g) (conjCoeffHom A S g) 1) w - w + w) := by
        rw [sub_add_cancel]
    _ = (groupCohomology.π (Rep.res S.subtype A) 1)
          ((groupCohomology.cocyclesMap (conjSubtypeHom S g) (conjCoeffHom A S g) 1) w - w)
        + (groupCohomology.π (Rep.res S.subtype A) 1) w := by rw [map_add]
    _ = (groupCohomology.π (Rep.res S.subtype A) 1)
          ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).toCycles 0 1
            (fun _ => ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)
              (fun _ => g)))
        + (groupCohomology.π (Rep.res S.subtype A) 1) w := by rw [h3]
    _ = 0 + (groupCohomology.π (Rep.res S.subtype A) 1) w := by rw [hz]
    _ = (groupCohomology.π (Rep.res S.subtype A) 1) w := zero_add _

/-- ★★★★ **(R2)-2 的 `n = 1` 收口**：`innerConjTrivialIn A S 1` **无条件成立**。

即：`S` 的内自同构在 `H¹(S,A)` 上作用平凡 —— **NSW I §5 的 `g_* = id`，`n = 1` 情形，已机检**。 -/
theorem innerConjTrivialIn_one (A : Rep k G) (S : Subgroup G) [S.Normal] :
    innerConjTrivialIn A S 1 :=
  fun g => conjMap_one_eq_one_of A S g (cyclesMap_one_comp_homologyπ A S g)

/-- ★★★★★ **无具名假设的 `∂₂`**：唯一前提是 `hcd`（`cd(S) ≤ 1` 的抽象形式），
即论文自身的假设。**`(R2)` 不再依赖任何具名假设。** -/
noncomputable def deltaTwoFree (A : Rep k G) (S : Subgroup G) [S.Normal]
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    groupCohomology A 2
      ⟶ groupCohomology (h1RepQuot A S 1 (innerConjTrivialIn_one A S)) 1 :=
  deltaTwo A S hcd (innerConjTrivialIn_one A S)

/-- `deltaTwoFree` 的源/靶类型锁定。 -/
noncomputable def deltaTwoFree_type_lock (A : Rep k G) (S : Subgroup G) [S.Normal]
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    (↥(groupCohomology A 2)
      → ↥(groupCohomology (h1RepQuot A S 1 (innerConjTrivialIn_one A S)) 1)) :=
  deltaTwoFree A S hcd

end L20261018

#print axioms L20261018.cyclesMap_one_sub_eq_toCycles
#print axioms L20261018.cyclesMap_one_comp_homologyπ
#print axioms L20261018.innerConjTrivialIn_one
#print axioms L20261018.deltaTwoFree
#print axioms L20261018.deltaTwoFree_type_lock
