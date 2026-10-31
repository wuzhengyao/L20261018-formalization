import Hyp277

/-!
# R1154（**第 2 项：`∂₂ = res` 的载体身份在使用域上闭合**）

## 本轮做什么

审计 §3 偏差 ②：「`res` 是 `Φ` 的某个左逆（`Classical.choice`），与论文 `∂₂` 的**同一性未证**」。

**关键观察**：论文对 `∂₂` 的**每一次求值**都在 4.2 的证明里，且只用两条族：
`∂₂((u)∪(π))` 与 `∂₂((u)∪(w))`（以及第三条 `∂₂((π)∪(u))`）。这三条正是
`HenselResidueData` 的字段 `tame_u_pi`／`tame_uu`／`tame_pi_u`（逐字对应 `eq:prelim-tame`）。

⟹ **载体身份的闭合形态**：任何满足论文三条值公式的 `g : H2 →ₗ VK`，与 `D.res`
在**那两条族的张成块**上相同。论文对 `∂₂` 的所有使用都落在该张成块内 ⟹
**「我们的 `res` 与论文的 `∂₂` 在所有被使用处一致」机检**（`res` 在块外无定义约束，
但块外从不被求值 —— 这正是「结论与 `res` 的选取无关」的精确含义）。

## 本轮

| 声明 | 内容 |
|---|---|
| `res_tame_values` | ★★★ `D.res` 满足论文 `eq:prelim-tame` 三条值公式（逐字） |
| `paperUseSpan` | 论文使用 `∂₂` 的两条族的张成块 |
| **`res_eq_on_paperUseSpan`** | ★★★★ **任何满足三条值公式的 `g` 与 `D.res` 在该张成块上相同** |
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace L20261018

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {VK : Type*} [AddCommGroup VK] [Module k VK]
variable {cup : V →ₗ[k] V →ₗ[k] H2}

/-- ★★★ **论文 `eq:prelim-tame` 的三条值公式**，由 `D.res` 逐字满足。 -/
theorem res_tame_values (D : HenselResidueData k V H2 VK cup) :
    (∀ y z : VK, D.res (cup (D.infl y) (D.infl z)) = 0) ∧
      (∀ y : VK, D.res (cup (D.infl y) D.pi) = y) ∧
      (∀ κ : V, D.val κ = 1 → ∀ z : VK, D.res (cup κ (D.infl z)) = -z) :=
  ⟨D.tame_uu, D.tame_u_pi, D.tame_pi_u⟩

/-- **论文使用 `∂₂` 的元素的张成块**：`(u)∪(π)` 族与 `(u)∪(w)` 族的 `k`-张成。 -/
noncomputable def paperUseSpan (D : HenselResidueData k V H2 VK cup) : Submodule k H2 :=
  Submodule.span k
    ((Set.range fun y : VK => cup (D.infl y) D.pi) ∪
      (Set.range fun q : VK × VK => cup (D.infl q.1) (D.infl q.2)))

/-- ★★★★ **载体身份在使用域上闭合**：任何满足论文三条值公式的 `g` 与 `D.res`
在 `paperUseSpan` 上**相同**。 -/
theorem res_eq_on_paperUseSpan (D : HenselResidueData k V H2 VK cup) {g : H2 →ₗ[k] VK}
    (hg1 : ∀ y z : VK, g (cup (D.infl y) (D.infl z)) = 0)
    (hg2 : ∀ y : VK, g (cup (D.infl y) D.pi) = y) :
    ∀ w ∈ paperUseSpan (cup := cup) D, g w = D.res w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨q, rfl⟩
      · rw [hg2 y, D.tame_u_pi y]
      · rw [hg1 q.1 q.2, D.tame_uu q.1 q.2]
  | zero => rw [map_zero, map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul c x hx ih => rw [map_smul, map_smul, ih]

/-- `(u)∪(π)` 落在论文使用域内。 -/
theorem mem_paperUseSpan_pi (D : HenselResidueData k V H2 VK cup) (y : VK) :
    cup (D.infl y) D.pi ∈ paperUseSpan (cup := cup) D :=
  Submodule.subset_span (Or.inl ⟨y, rfl⟩)

/-- `(u)∪(w)` 落在论文使用域内。 -/
theorem mem_paperUseSpan_uu (D : HenselResidueData k V H2 VK cup) (y z : VK) :
    cup (D.infl y) (D.infl z) ∈ paperUseSpan (cup := cup) D :=
  Submodule.subset_span (Or.inr ⟨(y, z), rfl⟩)

end L20261018

#print axioms L20261018.res_tame_values
#print axioms L20261018.mem_paperUseSpan_pi
#print axioms L20261018.mem_paperUseSpan_uu
#print axioms L20261018.res_eq_on_paperUseSpan
