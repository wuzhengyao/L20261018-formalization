import L20261018.Ch2.Hensel.Valuation.Step015_norm_s_eq_zero

/-!
# R1039（**自我审查 · 非空性审计**）：`ValFiltrationCompat` 的假设类是**空的**

写 S28 第 2 步时发现：`Hyp168` 的假设结构 `ValFiltrationCompat` 同时包含

* `exists_integerUnit`：非负赋值元素是 `𝒪_F` 的**单位**的像；
* `mem_maximalIdeal`：`b ∈ 𝔪 ⟺ 0 < v(b)`（`b : 𝒪_Fˣ`）。

取 `a = π`（`v π = 1 ≥ 0`）：第一字段给一个**单位** `b : 𝒪_Fˣ` 且 `↑b = π`；
第二字段随即把该单位送进 `𝔪` —— 而局部环里**单位不在极大理想中**。⟹ **假设类为空**，
凡以它为条件的定理都是**空真**（本仓 L1／L10① 明令禁止）。

本文件把这一矛盾**机检**成 `False`，并登记修复方向（见 `ASSUMPTIONS.md` 第 237 轮）。

| 声明 | 内容 |
|---|---|
| **`valFiltrationCompat_false`** | `ValFiltrationCompat v → v π = 1 → False` |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section Nonemptiness

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **空性**：`ValFiltrationCompat` 与「`π` 的赋值是 `1`」不相容。 -/
theorem valFiltrationCompat_false (hvf : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) : False := by
  -- 第一字段：`π` 是 `𝒪_F` 的单位的像
  obtain ⟨b, hb⟩ := hvf.exists_integerUnit π ⟨(1 : ℤ), by norm_num, hπ⟩
  -- 第二字段：该单位落在 `𝔪` 中
  have hmem : (b : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
    rw [hvf.mem_maximalIdeal b]
    exact ⟨1, one_pos, by rw [hb, hπ]⟩
  -- 但单位不在极大理想中
  have hunit : IsUnit (b : ↥𝒪[F]) := Units.isUnit b
  exact (IsLocalRing.notMem_maximalIdeal (R := ↥𝒪[F])).mpr hunit hmem

end Nonemptiness

end L20261018

#print axioms L20261018.valFiltrationCompat_false
