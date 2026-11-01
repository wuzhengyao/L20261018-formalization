import L20261018.Hyp243

/-!
# R1115（**(R2)-2 装配 a1：由 `cycles 1` 的元素榨出「压缩余圈」**）

## 背景

`PLAN-R2` §H-21.2 把 `(R2)-2` 的 `n = 1` 收口拆成 a1–a4。**a1 是唯一的「硬」子步**：
把 `w : (inhomogeneousCochains A).cycles 1`（`ShortComplex`／`HomologicalComplex` 层的余圈）
的**余圈条件**翻译成**函数层**的 `cocycles₁` 成员关系，即

```
w 的「压缩函数」 f (t) := (iCycles 1 w) (· ↦ t)     满足   f ∈ cocycles₁ A
```

只有拿到 `f ∈ cocycles₁`，才能把 `Hyp240.conj_one_cochain`（它要 `hf : f ∈ cocycles₁`）
用到 `w` 上。

## 本轮的关键

`w : K.cycles 1` 的余圈条件在 mathlib 里**不是** `Submodule` 成员，而是通过
`ShortComplex`／`LeftHomologyData` 表达的；直接「展开成 `d 1 2 = 0`」需要 `iCycles` 是包含映射
这一事实。**本轮的破法**：用

```
HomologicalComplex.iCycles_d : K.iCycles i ≫ K.d i j = 0
```

在 `w` 处取值，得 `K.d 1 2 (K.iCycles 1 w) = 0` —— **完全绕开**「`iCycles` 是子类型包含」这条
（mathlib 里没有以 `apply` 形式暴露的）事实。

再用 `Hyp243.d_one_two_apply` 把它展开成教科书非齐次余链微分，`abel` 收尾。

## 本轮

| 声明 | 内容 |
|---|---|
| **`compressed_mem_cocycles`** | ★★★ **a1**：`(fun t => (iCycles 1 w) (·t)) ∈ cocycles₁ A` |

**下一轮**：a2（逐点恒等式 `(cochainsMap c_g φ).f 1 M − M = d 0 1 u`，用 `Hyp240` ＋ 本轮的 `hf`）／
a3（`cancel_mono (iCycles 1)` 升到 `cycles 1`）／a4（`toCycles_comp_homologyπ` ⟹ (★) ⟹ `conjMap = 𝟙`）。

## 🔧 工艺

1. **`iCycles_d` 的取值形式**：`congrArg (fun m => m w) (iCycles_d K i j)` 之后
   **`rw [ModuleCat.comp_apply] at h'`**（`simp only` 在此**不推进**，与 R1109 同一现象），
   再 `simpa` 收尾。
2. **`d 1 2 M = 0` 是函数等式时的取值**：先证 `h0fun : d 1 2 M = 0`，再
   `have h0 : (d 1 2 M) ![s,t] = 0 := by rw [h0fun]; rfl`（`0` 在函数类型上是 `fun _ => 0`，`rfl` 可）。
3. **`a - b + c = 0` ⟹ `b = a + c`**：`rw [sub_add_eq_add_sub] at h0` 后 `(sub_eq_zero.mp h0).symm`
   （**不要**指望 `abel`／`linarith`：`A` 只是 `AddCommGroup`，无序）。
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★★★ **(R2)-2 装配 a1**：`cycles 1` 的元素 `w` 的「压缩函数」
`f t := (iCycles 1 w) (fun _ => t)` 属于 `cocycles₁ A`。

即：`w` 的余圈条件（`HomologicalComplex` 层）等价于 `f` 的 1-余圈关系（函数层）。 -/
theorem compressed_mem_cocycles (A : Rep k G) (S : Subgroup G) [S.Normal]
    (w : (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).cycles 1) :
    (fun t : S => ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)
        (fun _ => t)) ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A) := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro s t
  -- `w` 的余圈条件：`d 1 2 (iCycles 1 w) = 0`（由 `iCycles_d` 取值，**绕开**「包含映射」）
  have h0fun : ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).d 1 2
      ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)) = 0 := by
    have h' := congrArg (fun m => m w) (HomologicalComplex.iCycles_d
      (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)) (i := 1) (j := 2))
    rw [ModuleCat.comp_apply] at h'
    simpa using h'
  have h0 : ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).d 1 2
      ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)) ![s, t] = 0 := by
    rw [h0fun]
    rfl
  rw [d_one_two_apply] at h0
  rw [sub_add_eq_add_sub] at h0
  exact (sub_eq_zero.mp h0).symm

end L20261018

#print axioms L20261018.compressed_mem_cocycles
