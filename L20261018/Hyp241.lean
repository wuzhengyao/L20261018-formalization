import Hyp240

/-!
# R1112（**(R2)-2：共轭 1-余圈与「同类」定理**）

## 目标

`(R2)-2` 的 `n = 1` 收口需要 `conjMap A S g 1 = 𝟙`（`g ∈ S`）。路线的三块：

| # | 内容 | 状态 |
|---|---|---|
| ① | 余链层：`c_g f - f = d₀₁ (f g)` | ✅ `Hyp240.conj_one_cochain_sub` |
| ② | **余圈层**：共轭后仍是余圈，且与原来**同类** | ✅ **本轮** |
| ③ | 同调层：把 ② 转成 `conjMap = 𝟙`（需 `isoCocycles₁` 与共轭的相容性） | ⬜ 下一轮 |

## 为什么 ② 不是显然的

`c_g f(s) = ρ_g (f (g⁻¹ s g))`（共轭每条变元 ＋ 乘 `ρ_g`）。要证它把 1-余圈送到 1-余圈，
需要基底等式

```
ρ_g ∘ ρ_{g⁻¹ s g} = ρ_s ∘ ρ_g          （conj_ρ_comm）
```

（这正是 `Hyp232.conjCoeffHom` 的 `Rep.Hom` 兼容性在元素层的形态：`g(g⁻¹sg) = (sg) = sg`。）

## 本轮

| 声明 | 内容 |
|---|---|
| **`conj_ρ_comm`** | ★ 基底等式 `ρ_g (ρ_{g⁻¹sg} x) = ρ_s (ρ_g x)` |
| **`conj_isCocycle`** | ★ 共轭后仍是 1-余圈 |
| **`conjCocycle`** | ★ 共轭 1-余圈（`cocycles₁` 的元素） |
| **`conjCocycle_sub_mem`** | ★★ `⇑(conjCocycle g z) - ⇑z ∈ B¹`（用 `Hyp240.conj_one_cochain_sub`） |
| **`H1π_conjCocycle`** | ★★★ **`H1π (conjCocycle g z) = H1π z`**（`H1π_eq_iff`） |

**下一轮（单入口）**：③ 的相容性 —— `H1π ≫ conjMap = H1π ∘ conjCocycle`（经 `isoCocycles₁` 与
`π_map`），配合本轮的 `H1π_conjCocycle` 与 **`H1π` 是 `Epi`** 得 `conjMap A S g 1 = 𝟙`，
再 `innerConjTrivialIn_of_one` ⟹ **`deltaTwo` 的 `h` 前提关闭，(R2) 不再依赖任何具名假设**。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **基底等式**：`ρ_g ∘ ρ_{g⁻¹ s g} = ρ_s ∘ ρ_g`（元素层）。

来自 `(ρ g) * (ρ (g⁻¹ s g)) = ρ (s * g) = (ρ s) * (ρ g)`。这是 `Hyp232.conjCoeffHom`
的 `Rep.Hom` 兼容性的元素层形态。 -/
theorem conj_ρ_comm (A : Rep k G) (S : Subgroup G) [S.Normal] (g s : S) (x : A) :
    A.ρ (g : G) (A.ρ (((g : S)⁻¹ * s * g : S) : G) x) = A.ρ (s : G) (A.ρ (g : G) x) := by
  have key1 : (A.ρ (g : G)) * (A.ρ (((g : S)⁻¹ * s * g : S) : G)) = A.ρ ((s : G) * g) := by
    rw [← map_mul]
    congr 1
    simp
    group
  have key2 : (A.ρ (s : G)) * (A.ρ (g : G)) = A.ρ ((s : G) * g) := by rw [← map_mul]
  calc A.ρ (g : G) (A.ρ (((g : S)⁻¹ * s * g : S) : G) x)
      = ((A.ρ (g : G)) * (A.ρ (((g : S)⁻¹ * s * g : S) : G))) x := rfl
    _ = A.ρ ((s : G) * g) x := by rw [key1]
    _ = ((A.ρ (s : G)) * (A.ρ (g : G))) x := by rw [key2]
    _ = A.ρ (s : G) (A.ρ (g : G) x) := rfl

/-- ★ **共轭后仍是 1-余圈**：若 `z` 满足 `z (s*t) = ρ_s (z t) + z s`，则
`w s = ρ_g (z (g⁻¹ s g))` 也满足。

关键：`g⁻¹(st)g = (g⁻¹sg)(g⁻¹tg)`，再用 `z` 的余圈关系与 `conj_ρ_comm`。 -/
theorem conj_isCocycle (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S) (z : S → A)
    (hz : z ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A)) :
    (fun s => A.ρ (g : G) (z ((g : S)⁻¹ * s * g)))
      ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A) := by
  rw [groupCohomology.mem_cocycles₁_iff] at hz ⊢
  intro s t
  have hz' := hz ((g : S)⁻¹ * s * g) ((g : S)⁻¹ * t * g)
  rw [show (g : S)⁻¹ * (s * t) * g
      = ((g : S)⁻¹ * s * g) * ((g : S)⁻¹ * t * g) from by group, hz', map_add]
  rw [add_left_inj]
  exact conj_ρ_comm A S g s (z ((g : S)⁻¹ * t * g))

/-- ★ **共轭 1-余圈**（`cocycles₁` 的元素）。 -/
noncomputable def conjCocycle (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S)
    (z : groupCohomology.cocycles₁ (Rep.res S.subtype A)) :
    groupCohomology.cocycles₁ (Rep.res S.subtype A) :=
  ⟨fun s => A.ρ (g : G) (z ((g : S)⁻¹ * s * g)), conj_isCocycle A S g ⇑z z.2⟩

/-- ★★ **共轭余圈与原来的差落在 `B¹` 里**（即同一个上同调类）。
直接由 `Hyp240.conj_one_cochain_sub` 与 `B¹ = range (d₀₁)`。 -/
theorem conjCocycle_sub_mem (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S)
    (z : groupCohomology.cocycles₁ (Rep.res S.subtype A)) :
    ⇑(conjCocycle A S g z) - ⇑z
      ∈ groupCohomology.coboundaries₁ (Rep.res S.subtype A) := by
  rw [groupCohomology.coboundaries₁, LinearMap.mem_range]
  refine ⟨z g, ?_⟩
  funext s
  exact (conj_one_cochain_sub A S g ⇑z z.2 s).symm

/-- ★★★ **`H¹` 中同类**：`H1π (conjCocycle g z) = H1π z`。
这是「内自同构在 `H¹` 上作用平凡」在**余圈层**的形态（`H1π_eq_iff`）。 -/
theorem H1π_conjCocycle (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S)
    (z : groupCohomology.cocycles₁ (Rep.res S.subtype A)) :
    groupCohomology.H1π (Rep.res S.subtype A) (conjCocycle A S g z)
      = groupCohomology.H1π (Rep.res S.subtype A) z :=
  (groupCohomology.H1π_eq_iff _ _).2 (conjCocycle_sub_mem A S g z)

end L20261018

#print axioms L20261018.conj_ρ_comm
#print axioms L20261018.conj_isCocycle
#print axioms L20261018.conjCocycle
#print axioms L20261018.conjCocycle_sub_mem
#print axioms L20261018.H1π_conjCocycle
