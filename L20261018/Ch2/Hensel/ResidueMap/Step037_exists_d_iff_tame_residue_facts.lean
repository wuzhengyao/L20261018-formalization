import L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface
import L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined
import L20261018.Ch2.Hensel.ResidueMap.Step034_delta_two_replaces_finite_residue

/-!
# R1252（S35 入口 A 的第 0 步）：**`∃ d` ⟺ `TameResidueFacts`**

`PROMPT-S35` 把入口 A 压成「造一个 `d`，满足论文 `prop:prelim-residue` (1) 的两条」。
本轮先把这个目标**精确化**：在抽象层（`cup : V →ₗ V →ₗ H2`、`val : V →ₗ k`、`val π = 1`、斜对称）
这两条性质与 `TameResidueFacts`（`(R1) ∧ (R2)`）**等价**：

* `⟸`：`Hyp161.henselResidueDataOfFacts` 的 `D.res` 就是 `d`（其两条性质即 `tame_uu`／`tame_u_pi`）；
* `⟹`：`Hyp338.tameResidueFacts_of_residueMap`（`infl` 取 `ker val` 的子类型包含）。

⟹ **入口 A 不多不少就是 `(R1) ∧ (R2)` 的无条件证明**（论文由 GS 6.8.5 的驯剩余给出；
本战役在有限剩余域下由 `Hyp302.unitsCupVanish` 给出，一般情形仍开）。
这既否定了"`d` 比 `TameResidueFacts` 更容易"的设想（`d` 的存在性要求 `cup(·,π)` 在 `ker v̄` 上单射），
也说明 `Hyp339`／`Hyp341` 的 `∃D` 口径已是最小口径。

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_residueMap_iff_tameResidueFacts`** | ★★★★★ **`∃ d`（两条性质）⟺ `(R1) ∧ (R2)`** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace L20261018

open TauCeti

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- ★★★★★ **`∃ d`（`∂₂` 的两条性质）与 `TameResidueFacts` 等价**。

`d : H² → ker v̄` 满足 `d (cup (infl y) (infl z)) = 0`、`d (cup (infl y) π) = y`
（`infl` = `ker v̄ ↪ V` 的子类型包含）当且仅当 `(R1) ∧ (R2)` 成立。 -/
theorem exists_residueMap_iff_tameResidueFacts
    (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)
    (hπ : val π = 1) (hskew : ∀ x y, cup x y = - cup y x) :
    (∃ d : H2 →ₗ[k] ↥(LinearMap.ker val),
        (∀ y z : ↥(LinearMap.ker val), d (cup (y : V) (z : V)) = 0) ∧
        (∀ y : ↥(LinearMap.ker val), d (cup (y : V) π) = y))
      ↔ TameResidueFacts cup val π := by
  constructor
  · rintro ⟨d, hd_infl, hd_cup_pi⟩
    exact tameResidueFacts_of_residueMap cup val π
      (LinearMap.ker val).subtype (fun y => y.2) (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
      d hd_infl hd_cup_pi
  · intro h
    let D : HenselResidueData k V H2 ↥(LinearMap.ker val) cup :=
      henselResidueDataOfFacts cup val π hπ hskew h
    exact ⟨D.res, D.tame_uu, D.tame_u_pi⟩

end L20261018

#print axioms L20261018.exists_residueMap_iff_tameResidueFacts
