import L20261018.Infra.Cohomology.Boundary.Step009_delta_two_third_segment

/-!
# R1101（**(R2)：`G ⧸ S`-模结构的第一块 —— 抽象侧共轭作用 `conjMap`**）

## 背景（R1100 定位的单条基建缺口）

`∂₂` 的第 (3) 段还差「`H¹(S,A)` 上的 `G ⧸ S`-模结构」（＝内自同构在 `H¹` 上作用平凡）。
库内该事实**只在连续侧**（`ContCohomology/InnerConjugation.map_eq_id_of_inner`）。
本轮把**共轭作用本身**在抽象侧造出来（库内抽象侧缺）：对 `S ◁ G`、`g : G`，

```
conjMap A g n : H^n(S, A) ⟶ H^n(S, A)
```

由 `groupCohomology.map` 沿（`s ↦ g⁻¹ s g`，系数 `A.ρ g`）得到 —— 这一对是兼容的：
`A.ρ g ∘ A.ρ (g⁻¹ s g) = A.ρ (s g) = A.ρ s ∘ A.ρ g`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`conjSubtypeHom`** | `s ↦ g⁻¹ s g`（`S ◁ G` 保证落在 `S` 内） |
| **`conjSubtypeHom_coe`** | 取值公式 `↑(conjSubtypeHom S g s) = g⁻¹ * s * g` |
| （本轮未落）**`conjCoeffHom`** | 系数侧兼容态射（底层 `A.ρ g`）—— **卡在 `Rep.Hom` 构造**，见下 |
| （下一轮）**因子性** | `conjMap (g * g') = conjMap g' ≫ conjMap g` 型（经 `groupCohomology.map` 的复合律） |

## ⚠ 本轮精确卡点（下一轮单入口）

`conjCoeffHom`（`Rep.Hom`，底层 `A.ρ g`）的**等变性**证明
`A.ρ g ∘ A.ρ (g⁻¹ s g) = A.ρ s ∘ A.ρ g` 在 Lean 里必须把两端都归约到 `A.ρ (s * g) a`，而
`rw [map_mul]` 会**先命中内层** `A.ρ (g⁻¹ * s * g)`（右侧第一个匹配），导致两端归约顺序不一致。
**已定位的解法**：改用 `simp only [map_mul, Module.End.mul_apply]` 把两端**同时规范化成嵌套应用形**
（`A.ρ g (A.ρ (g⁻¹*s) (A.ρ g a))`），而非用有向重的 `rw`。
另两处（`#print axioms` 已在下方）：`conjCoeffHom` 的 `hom'` 需**显式给出两个表示**
（`LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ f _`；隐式 `ρ` 无法从期望类型推断）。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- 共轭 `s ↦ g⁻¹ * s * g`（`S ◁ G` 保证落在 `S` 内）。 -/
def conjSubtypeHom (S : Subgroup G) [S.Normal] (g : G) : S →* S where
  toFun s := ⟨(MulAut.conj g⁻¹) (s : G), by
    have h := Subgroup.Normal.conj_mem (H := S) ‹S.Normal› (s : G) s.2 g⁻¹
    simpa [MulAut.conj_apply] using h⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp only [MulAut.conj_apply, inv_inv, Subgroup.coe_mul]
    group

/-- `conjSubtypeHom` 在底层群上的取值公式。 -/
@[simp]
theorem conjSubtypeHom_coe (S : Subgroup G) [S.Normal] (g : G) (s : S) :
    ((conjSubtypeHom S g s : S) : G) = g⁻¹ * (s : G) * g := by
  show (MulAut.conj g⁻¹) (s : G) = g⁻¹ * (s : G) * g
  rw [MulAut.conj_apply, inv_inv]

end L20261018

#print axioms L20261018.conjSubtypeHom
