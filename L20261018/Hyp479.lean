import Hyp478
import Hyp342
import Hyp449

/-!
# S40 R19：★★ **目标钉死** —— 本战役剩下的**唯一**义务是两个杯积公式

## 侦察结论（`RECON-R3` §97）

按 R17 纪律先做内容式 grep，发现本仓**早已有**整条归约链：

| 件 | 内容 | 出处 |
|---|---|---|
| `Hyp338.tameResidueFacts_of_residueMap` | `(R1)∧(R2)` 由 `d` ＋ `hd_infl` ＋ `hd_cup_pi` | `Hyp338:51` |
| **`Hyp342.tameResidueFacts_Galo_of_residueMap`** | ★★★★★★ **Galo 载体版**（`d : H2 →ₗ VKG`，无 `[Finite (ResidueField)]`） | `Hyp342:52` |
| `Hyp342.orth_eq_bot_noFinite` | 4.2（**条件于** `d` ＋ 两条公式） | `Hyp342:73` |
| `Hyp342` 后续 | 4.3(1) 等（同条件） | — |
| `Hyp432.disjoint_of_exists_residueMap`／`disjoint_iff_exists_residueMap` | `∃d ⟺ Disjoint` | `Hyp432:60,127` |
| `Hyp161.TameResidueFacts` | `⟨phi_injective, disjoint⟩` | `Hyp161:92` |

**⟹ `Hyp449.Ch4TameSymbolHyp` 的定义就是**（逐字对照）
```lean
∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
  (∀ y z, d (GaloBase.cup y z) = 0) ∧ (∀ y, d (GaloBase.cup y π) = y)
```
—— 与 `Hyp338`／`Hyp342` 的入参**同一个形状**。

⟹ **本战役剩下的唯一义务**：
1. **造 `d`**：把 `Hyp473.kummerResidueMap`（GS 的 `∂₂`）经 R18 桥链运到 `GaloBase.H2 → GaloBase.V`，
   再落到 `VKG`（需 **`H¹(G, ℚ/ℤ) → VK` 的识别** —— 本轮新识别的缺口 (ii)，见 §97.3）；
2. **③b** `hd_infl`；
3. **③c** `hd_cup_pi`。

## 本机检件

| 声明 | 内容 |
|---|---|
| **`KnrResidueObligation`** | 本战役剩下的**唯一**义务（`Prop`，逐字即 `Ch4TameSymbolHyp` 的展开） |
| **`ch4TameSymbolHyp_of_obligation`** | ★★★★★ **义务 ⟹ `Ch4TameSymbolHyp`**（`rfl` 级，确认两者是同一命题） |
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

/-- ★★★★★★ **本战役剩下的唯一义务**：存在 `d : H²(G_F, μ_p) → ker v̄`，满足论文
`prop:prelim-residue`(2) 的两条杯积公式（`raw/L20261018.tex:1050`）。 -/
def KnrResidueObligation (hpF : IsUnit (p : F)) : Prop :=
  ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
    (∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0) ∧
    (∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y)

/-- ★★★★★ **义务 ⟹ `Ch4TameSymbolHyp`**（两者是**同一个命题**，`rfl` 级）。 -/
theorem ch4TameSymbolHyp_of_obligation (hpF : IsUnit (p : F))
    (h : KnrResidueObligation F p v π hpF) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  h

/-! ## 注

`KnrResidueObligation ⟹ TameResidueFacts` 由 **`Hyp342.tameResidueFacts_Galo_of_residueMap`**
直接给出（那一件的上下文带齐 `[ValuativeRel F] [TopologicalSpace F]` 等实例）；
本文件不重复它，以免为实例细节耗轮。 -/

end L20261018

#print axioms L20261018.ch4TameSymbolHyp_of_obligation
