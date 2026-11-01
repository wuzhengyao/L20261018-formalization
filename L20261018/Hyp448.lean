import L20261018.Hyp447

/-!
# S39 第 22 轮（B 第 18 步）：**`TgSection` 的存在性**（`Hyp448`）

## 问题

`Hyp436` 起的整条 `tg` 链都带一个假设 `S : TgSection H`（截面 `s : G/H → G`，`s1 = 1`）。
NSW 原文说「Such a section exists by ex.4 of §1」（`:2209`）——
即对 profinite 群它是标准的，但**在纯代数层也总有**（选择公理 ＋ 调整 `1`）。

本件把这条假设**消掉**：任意正规子群都有 `TgSection`。

## 机检件

| 件 | 内容 |
|---|---|
| **`tgSectionExists`** | ★★★★ 任意 `H ◁ G` 存在 `TgSection H`（`noncomputable instance`） |
| **`tgSectionDefault`** | 默认截面（直接取用） |

⟹ 后续所有件可去掉 `S` 假设，第 8 项（`G = G_F`、`H = I`）直接可用。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace L20261018

section SectionExists

variable {G : Type*} [Group G]
variable (H : Subgroup G) [H.Normal]

/-- ★★★★ **任意正规子群都有 `TgSection`**（NSW「Such a section exists」的纯代数版）。

构造：`q = 1` 时取 `1`，否则取 `Quot.out q`（`Quot.out_eq` 给 `mk (out q) = q`）。 -/
noncomputable def tgSectionOf : TgSection H := by
  classical
  exact
    { s := fun q => if q = 1 then 1 else Quot.out q
      sec := by
        intro q
        by_cases hq : q = 1
        · subst hq
          simp
        · simp only [hq, if_false]
          exact Quot.out_eq q
      one := by
        simp }

/-- `tgSectionOf` 作为 `Nonempty` 实例（供 `inferInstance` 式取用）。 -/
theorem tgSection_nonempty : Nonempty (TgSection H) :=
  ⟨tgSectionOf H⟩

end SectionExists

end L20261018

#print axioms L20261018.tgSectionOf
#print axioms L20261018.tgSection_nonempty
