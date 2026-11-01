import L20261018.Hyp242

/-!
# R1114（**(R2)-2 的 (★)：`d` 在 `Fin 1`／`Fin 2` 处的显式取值公式**）

## 目标

`Hyp242.conjMap_one_eq_one_of` 把 `(R2)-2` 的 `n = 1` 归结为
`(★) : cocyclesMap c_g 1 ≫ π A 1 = π A 1`，其证明（`PLAN-R2` §H-20.3 步 a）需要
把非齐次余链复形 `inhomogeneousCochains` 的**低次微分**展开成 `S → A` 的形状。

本轮把这两个展开机检（`Fin 1`／`Fin 2` 处的 `contractNth` 求值与 `Finset` 单/双项和）：

```
(d 0 1 u) j            = ρ (j 0) (u _) - u _                    （j : Fin 1 → S，u 常值）
(d 1 2 z) ![a, b]      = ρ a (z (·b)) - z (·(a*b)) + z (·a)
```

第二式正是教科书非齐次余链微分 `(dz)(a,b) = ρ_a (z b) - z (ab) + z a` 的 `Fin`-层形态。

## 本轮

| 声明 | 内容 |
|---|---|
| **`d_zero_one_apply`** | `(d 0 1 u) j = ρ (j 0) (u _) - u _` |
| **`d_one_two_apply`** | `(d 1 2 z) ![a,b] = ρ a (z (·b)) - z (·(a*b)) + z (·a)` |

**下一轮**：用这两式 ＋ `Hyp240.conj_one_cochain` 完成 `PLAN-R2` §H-20.3 的步 a
（`cocyclesMap c_g 1 w - w = toCycles 0 1 u`），再经 `toCycles_comp_homologyπ` 得 (★)。

## 🔧 工艺（三条，本轮实测）

1. **`Fin.contractNth` 的求值**：`simp [Fin.contractNth]` **不够**（留下 `![a,b] k.castSucc = a`），
   `rfl` 也不行；**`funext k; fin_cases k; rfl` 是通解**（`Fin 1` 的唯一性由 `fin_cases` 拆开）。
2. **`Finset.univ.sum` over `Fin 1`／`Fin 2`**：`Fin.sum_univ_one`／`Fin.sum_univ_two` 直接展开。
3. **`(-1 : k)^(j+1) • x` 的化简**：`norm_num` 处理系数，剩下的是**加法结合律**——
   `abel` 收尾（`norm_num` 之后**不要**用 `rw [sub_eq_add_neg]`，那会改变目标形状）。
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- **`d 0 1` 的取值公式**：`(d 0 1 u) j = ρ (j 0) (u _) - u _`（`u : (Fin 0 → S) → A` 常值）。 -/
theorem d_zero_one_apply (A : Rep k G) (a : A) (j : Fin 1 → G) :
    ((groupCohomology.inhomogeneousCochains A).d 0 1 (fun _ => a)) j = A.ρ (j 0) a - a := by
  rw [groupCohomology.inhomogeneousCochains.d_def A]
  rw [inhomogeneousCochains.d_hom_apply]
  rw [Fin.sum_univ_one, sub_eq_add_neg]
  norm_num

/-- **`d 1 2` 的取值公式**（教科书非齐次余链微分）：
`(d 1 2 z) ![a,b] = ρ a (z (·b)) - z (·(a*b)) + z (·a)`。 -/
theorem d_one_two_apply (A : Rep k G) (z : (Fin 1 → G) → A) (a b : G) :
    ((groupCohomology.inhomogeneousCochains A).d 1 2 z) ![a, b]
      = A.ρ a (z (fun _ => b)) - z (fun _ => a * b) + z (fun _ => a) := by
  rw [groupCohomology.inhomogeneousCochains.d_def A]
  rw [inhomogeneousCochains.d_hom_apply]
  rw [Fin.sum_univ_two]
  have h0 : Fin.contractNth 0 (· * ·) ![a, b] = (fun _ => a * b) := by
    funext k; fin_cases k; rfl
  have h1 : Fin.contractNth 1 (· * ·) ![a, b] = (fun _ => a) := by
    funext k; fin_cases k; rfl
  rw [h0, h1]
  norm_num
  abel

end L20261018

#print axioms L20261018.d_zero_one_apply
#print axioms L20261018.d_one_two_apply
