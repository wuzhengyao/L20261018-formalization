import Hyp338
import Hyp161

/-!
# R1247（S34 第 18 轮）：**无 `[Finite (ResidueField)]` 的 `∃D`**

把 `Hyp338.tameResidueFacts_of_residueMap`（`(R1)∧(R2)` 由论文 `prop:prelim-residue` (1) 推出）
接进 `Hyp161.henselResidueDataOfFacts`（由 `TameResidueFacts` 造 `HenselResidueData`），
得到**摘掉 `[Finite (IsLocalRing.ResidueField ↥𝒪[F])]`** 的 `∃D`：

* 唯一额外输入是 **`∂₂` 的两条性质**（论文 (1)）：
  `∂₂(inf ξ) = 0`、`∂₂(inf η ∪ (π)) = η`；
* 加上 `prop:prelim-kummer-valuation` 的 `ker v̄ ⊆ range inf`。

⟹ `[Finite (ResidueField)]`（论文没有的假设）在这条链上被**论文自己的假设**取代。

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_henselResidueData_of_residueMap`** | ★★★★★★ **`∃D`（无有限剩余域假设）** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace L20261018

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]
  {VK : Type*} [AddCommGroup VK] [Module k VK]

/-- ★★★★★★ **`∃D`：`HenselResidueData` 存在，只需 `∂₂` 的两条性质（无 `[Finite (ResidueField)]`）**。 -/
theorem exists_henselResidueData_of_residueMap
    (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    (hskew : ∀ x y, cup x y = - cup y x)
    (infl : VK →ₗ[k] V) (hval_infl : ∀ y : VK, val (infl y) = 0)
    (hsurj : ∀ x : V, val x = 0 → ∃ y : VK, infl y = x)
    (d : H2 →ₗ[k] VK)
    (hd_infl : ∀ y z : VK, d (cup (infl y) (infl z)) = 0)
    (hd_cup_pi : ∀ y : VK, d (cup (infl y) π) = y) :
    ∃ D : HenselResidueData k V H2 ↥(LinearMap.ker val) cup, D.val = val :=
  ⟨henselResidueDataOfFacts cup val π hπ hskew
    (tameResidueFacts_of_residueMap cup val π infl hval_infl hsurj d hd_infl hd_cup_pi),
   rfl⟩

end L20261018

#print axioms L20261018.exists_henselResidueData_of_residueMap
