import L20261018.Ch2.Kummer.Step049_two_cup_formulas_remaining

/-!
# S40 R20：★ **论文 `prop:prelim-residue`(2) 的逐字读法** ＋ 缺口 (ii) 登记

## 本轮最重要的事：**更正 `∂₂` 的值域读法**

论文 `raw/L20261018.tex:1033–1036`（`prop:prelim-residue`(2)）逐字：

> 若进一步 $F=K((\pi))$，则对 $q,j\ge1$ 有分裂正合列
> $$0\longrightarrow H^q(K,\mu_p^{\otimes j})\xrightarrow{\mathrm{inf}}
> H^q(F,\mu_p^{\otimes j})\xrightarrow{\partial_q}
> H^{q-1}(K,\mu_p^{\otimes(j-1)})\longrightarrow0.$$

⟹ **`∂₂` 的值域是 `H^{q-1}(K, μ_p)`**（`K` = 剩余域，**不分歧部分**），
`q = 2, j = 1` 时即 `H¹(K, μ_p)`。
**这与 `Hyp449`／`Hyp342` 的 `VKG = ker v̄ ⊆ H¹(F, μ_p)` 一致**（`VKG` 就是 `inf` 的像）。

⟹ **`Hyp479.KnrResidueObligation` 的目标形状是对的**；
R19 §97.3 记的「`d` 的值域是 `VKG ⊆ H¹(G,ℤ/p)`」与论文读法一致。

## 缺口 (ii) 的精确形状（本轮登记，未解）

GS `prop-units-cohomology`（`raw/GilleSzamuely2017.tex:8186`）给的 `r_v^i` 值域是
`H^{i-1}(G, ℚ/ℤ)`；论文的 `∂_q` 值域是 `H^{q-1}(K, μ_p)`。二者的桥：

* `H^{i-1}(G,ℚ/ℤ)` 的 **`p`-挠** ≅ `H^{i-1}(G, ℤ/p)`（由 `0 → ℤ/p → ℚ/ℤ --p--> ℚ/ℤ → 0`
  与 `H⁰(G,ℚ/ℤ) = ℚ/ℤ`（`μ_p ⊂ F` ⟹ 系数平凡）的长正合列）；
* `H^{i-1}(G,ℤ/p) = H^{i-1}(K, μ_p)`（`G = Gal(K_s|K)`）。

⟹ **缺口 (ii) = `H¹(G,ℚ/ℤ)[p] ≅ H¹(G,ℤ/p)`**（论文/GS 的 `ℚ/ℤ` ↔ `μ_p` 对齐）。

## 本机检件

论文 `prop:prelim-residue`(2) 的三条显式公式（`raw/L20261018.tex:1052` 逐字）在本仓
`Hyp449`／`Hyp342` 里就是义务的两条 ＋ 反称性推论。本件把**三条公式**作为一个
`Prop` 记下来，并机器核对**它与 `KnrResidueObligation` 等价**（文档化用）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable (F : Type) [Field F] (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
  (v : Fˣ →* Multiplicative ℤ) (π : Fˣ)

/-- ★★★★★ **论文 `prop:prelim-residue`(2) 的三条显式公式**（`raw/L20261018.tex:1052` 逐字）：
`∂₂((u)∪(π)) = (ū)`、`∂₂((π)∪(u)) = -(ū)`、`∂₂((u)∪(w)) = 0`（`u, w` 为单位）。

本件里「单位」= `ker v̄`（`VKG`），`(ū)` = `KummerBridge.kummerClass`。 -/
def PaperTameResidueFormulas (hpF : IsUnit (p : F)) : Prop :=
  ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
    (∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y) ∧
    (∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p)
        (KummerBridge.kummerClass F p hpF π) (y : GaloBase.V F p)) = - y) ∧
    (∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)

/-- ★★★★★ **论文三条公式的第三、二条由第一、三条推出**（反称性），故
`PaperTameResidueFormulas` 与 `KnrResidueObligation` 等价。 -/
-- @source file=raw/L20261018.tex locator=line:1052 quote="\partial_2((u)\cup(\pi))=(\bar u)"
theorem paperFormulas_iff_obligation (hpF : IsUnit (p : F))
    (hskew : ∀ x y : GaloBase.V F p,
      GaloBase.cup (K := F) (p := p) x y = - GaloBase.cup (K := F) (p := p) y x) :
    PaperTameResidueFormulas F p v π hpF ↔ KnrResidueObligation F p v π hpF := by
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    exact ⟨d, h3, h1⟩
  · rintro ⟨d, h3, h1⟩
    refine ⟨d, h1, ?_, h3⟩
    intro y
    rw [hskew, map_neg, h1]

end L20261018

#print axioms L20261018.paperFormulas_iff_obligation
