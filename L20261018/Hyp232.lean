import Hyp231

/-!
# R1102（**(R2)：共轭作用 `conjMap` —— 补上 `conjCoeffHom` ＋ `conjMap`**）

接 `Hyp231`（`conjSubtypeHom` ＋ 卡点定位）。本轮按 `Hyp231` 记录的两条解法落码：

1. `Rep.Hom` 的 `hom'` **显式给两个表示**：`LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ f _`；
2. 等变性等式用 `simp only [map_mul, Module.End.mul_apply]` **双向规范化**后再 `← Module.End.mul_apply, ← map_mul`。

## 数学

`S ◁ G`、`g : G`。对 `A : Rep k G`，共轭对
`(s ↦ g⁻¹ s g, A.ρ g)` 兼容：
`A.ρ g ∘ A.ρ (g⁻¹ s g) = A.ρ ((g)(g⁻¹ s g)) = A.ρ (s g) = A.ρ s ∘ A.ρ g`。
于是 `groupCohomology.map` 给出**共轭作用** `conjMap A S g n : H^n(S,A) → H^n(S,A)`。

| 声明 | 内容 |
|---|---|
| **`conjCoeffHom`** | ★ 系数侧兼容态射（底层 `A.ρ g`） |
| **`conjMap`** | ★★ **共轭作用** `H^n(S,A) → H^n(S,A)`（`S ◁ G`、`g : G`） |

**下一轮**：把「内自同构平凡」写成**单条具名假设**
`hconj : ∀ g : G, conjMap A S g n = 𝟙 _`（`hyp-inner-conj-trivial.md`，类型锁定 ＋ 非空性审计 ＋
解除路径＝移植连续侧 `InnerConjugation`），并由此导出 `G ⧸ S`-模结构 ⟹ `∂₂` 全长（`PLAN-R2` §H-10）。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **系数侧的兼容态射**：底层为 `A.ρ g`，兼容性
`A.ρ g ∘ A.ρ (g⁻¹ s g) = A.ρ s ∘ A.ρ g`。 -/
noncomputable def conjCoeffHom (A : Rep k G) (S : Subgroup G) [S.Normal] (g : G) :
    Rep.res (conjSubtypeHom S g) (Rep.res S.subtype A) ⟶ Rep.res S.subtype A where
  hom' := LinearMap.intertwiningMap_of_isIntertwiningMap
    (Rep.res (conjSubtypeHom S g) (Rep.res S.subtype A)).ρ
    (Rep.res S.subtype A).ρ (A.ρ g) (fun s a => by
      show A.ρ g (A.ρ ((conjSubtypeHom S g s : S) : G) a) = A.ρ ((s : S) : G) (A.ρ g a)
      rw [conjSubtypeHom_coe]
      -- 关键：在 `Module.End` 的**乘法层**做群归一（此处 `map_mul` 与 `group` 都稳定）
      have key : (A.ρ g) * (A.ρ (g⁻¹ * (s : G) * g)) = A.ρ (((s : S) : G) * g) := by
        rw [← map_mul]
        congr 1
        group
      have key2 : (A.ρ ((s : S) : G)) * (A.ρ g) = A.ρ (((s : S) : G) * g) := by
        rw [← map_mul]
      calc A.ρ g (A.ρ (g⁻¹ * (s : G) * g) a)
          = ((A.ρ g) * (A.ρ (g⁻¹ * (s : G) * g))) a := (rfl)
        _ = A.ρ (((s : S) : G) * g) a := by rw [key]
        _ = ((A.ρ ((s : S) : G)) * (A.ρ g)) a := by rw [key2]
        _ = A.ρ ((s : S) : G) (A.ρ g a) := (rfl))

/-- ★★ **共轭作用** `H^n(S,A) → H^n(S,A)`（`S ◁ G`，`g : G`）。 -/
noncomputable def conjMap (A : Rep k G) (S : Subgroup G) [S.Normal] (g : G) (n : ℕ) :
    groupCohomology (Rep.res S.subtype A) n ⟶ groupCohomology (Rep.res S.subtype A) n :=
  groupCohomology.map (conjSubtypeHom S g) (conjCoeffHom A S g) n

end L20261018

#print axioms L20261018.conjCoeffHom
#print axioms L20261018.conjMap
