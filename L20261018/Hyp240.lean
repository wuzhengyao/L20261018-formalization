import Hyp239

/-!
# R1111（**(R2)-2 开局：解除 `innerConjTrivialIn` —— `n = 1` 的棱柱恒等式**）

## 为什么先做 `n = 1`

`deltaTwo`（`Hyp239`）里 `innerConjTrivialIn` **只用在 `n = 1`**（`h1RepQuot A S 1 h`）。
故 `(R2)` 只需要 `conjMap A S g 1 = 𝟙`。**全次数的移植是 `(R2)-2` 的完整目标，但 `n = 1` 即已足够关闭 (R2)。**

## 原文路线（照抄，不另起）

`TauCeti/RepresentationTheory/Homological/ContCohomology/InnerConjugation.lean` 的 docstring 逐字给出：

> `Hⁿ(G, X)` 由余诱导分解计算，`d` 是递归 `(d F) x = F - d (F x)`；齐次 `n`-余链是 `Xₙ₊₁` 的
> `G`-不变元。在不变元上，兼容对的余链映射是**每个变元右移 `g`**：
> `F (x₀, …, xₙ) ↦ F (x₀ * g, …, xₙ * g)`；右平移是链映射 `resolutionTranslate`，
> 且与恒等**链同伦**，同伦是**棱柱算子**
> `(h F) (x₀, …, xₙ₋₁) = ∑ᵢ (-1)ⁱ F (x₀, …, xᵢ, xᵢ * a, …, xₙ₋₁ * a)`。

## 本轮把棱柱算子**逐字搬到非齐次余链**（`inhomogeneousCochains`）

非齐次坐标下（`f : Sⁿ → A`，`s_j` 为「比值」参数），棱柱算子读作

```
(h f)(s₁, …, sₙ₋₁) = ∑_{i=0}^{n-1} (-1)^i f(s₁, …, sᵢ, g, g⁻¹ s_{i+1} g, …, g⁻¹ s_{n-1} g)
```

（第 `i` 项里第 `i+1` 个变元是 `g`——因为 `xᵢ⁻¹ (xᵢ g) = g`——其后的变元都多夹一对 `g, g⁻¹`。）

**`n = 1` 时** `h f = f g`（`C⁰` 上一个元素），于是棱柱恒等式 `d(hf) + h(df) = c_g f - f` 读作

```
ρ_g (f (g⁻¹ s g)) = ρ_s (f g) + f s - f g          （当 f ∈ Z¹）
```

**⚠ 关键点（本轮的定量结论）**：该恒等式**只在 `Z¹` 上成立**，不是全复形上的 `Homotopy`——
因为 `d(hf) + h(df) - (c_g f - f) = (df)(s, g)`，而 `(df)(s,g) = 0` 正是 1-余链条件。
故**(R2)-2 在 `n = 1` 不能走 `HomologicalComplex.Homotopy`**，必须走「`Z¹/B¹`」：
`c_g z - z = d₀₁ (z g) ∈ B¹` ⟹ 同类 ⟹ `conjMap = 𝟙`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`conj_one_cochain`** | ★ **(R2)-2 的数学核心（`n = 1`）**：`ρ_g (f (g⁻¹ s g)) = ρ_s (f g) + f s - f g`（`f ∈ Z¹`） |

**下一轮（单入口）**：把 `conj_one_cochain` 变成同调层的结论 ——
`(cocyclesMap c_g 1 - 𝟙) ≫ π = 0`（因 `ker π = B¹`），再用 `π` 的 `Epi` 性消去，
得 `conjMap A S g 1 = 𝟙`，最后 `deltaTwo` 的 `h` 前提由 `innerConjTrivialIn_of_one` 关闭。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **(R2)-2 的数学核心（`n = 1` 的棱柱恒等式）**。

设 `f : S → A` 是 `Rep.res S.subtype A` 的 **1-余链**（`f ∈ Z¹`，即
`f (s*t) = ρ_s (f t) + f s`），`g : S`。则

```
ρ_g (f (g⁻¹ * s * g)) = ρ_s (f g) + f s - f g ,
```

即「共轭每条变元 ＋ 乘 `ρ_g`」与恒等之差恰是 `f g` 的上边缘（棱柱算子 `h f = f g`）。

证明只用两次 1-余链关系：
`f (s*g) = ρ_s (f g) + f s`（取 `(s,g)`）与 `f (s*g) = ρ_g (f (g⁻¹*s*g)) + f g`（取 `(g, g⁻¹*s*g)`）。 -/
theorem conj_one_cochain (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S) (f : S → A)
    (hf : f ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A)) (s : S) :
    A.ρ (g : G) (f ((g : S)⁻¹ * s * g)) = A.ρ (s : G) (f g) + f s - f g := by
  have h1 : f (s * g) = A.ρ (s : G) (f g) + f s :=
    (groupCohomology.mem_cocycles₁_iff (A := Rep.res S.subtype A) f).1 hf s g
  have h2 : f (s * g) = A.ρ (g : G) (f ((g : S)⁻¹ * s * g)) + f g := by
    have h := (groupCohomology.mem_cocycles₁_iff (A := Rep.res S.subtype A) f).1 hf g
      ((g : S)⁻¹ * s * g)
    rw [show (g : S) * ((g : S)⁻¹ * s * g) = s * g from by group] at h
    exact h
  rw [h1] at h2
  rw [eq_sub_iff_add_eq]
  exact h2.symm

/-- **上边缘形式**：`c_g f - f` 就是 `d₀₁ (f g)`（`d₀₁ x = fun s => ρ_s x - x`）。
这是「`c_g` 与恒等之差落在 `B¹` 里」的逐点形式。 -/
theorem conj_one_cochain_sub (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S) (f : S → A)
    (hf : f ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A)) (s : S) :
    A.ρ (g : G) (f ((g : S)⁻¹ * s * g)) - f s = A.ρ (s : G) (f g) - f g := by
  have h := conj_one_cochain A S g f hf s
  rw [h]
  abel

end L20261018

#print axioms L20261018.conj_one_cochain
#print axioms L20261018.conj_one_cochain_sub
