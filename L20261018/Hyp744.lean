import L20261018.Hyp610
import L20261018.Hyp743

/-!
# S67 R9：**具名假设 `UnramifiedKummer`**（不通歧 Kummer 理论）—— C3/C4/F5 共用的唯一未形式化件

`S67-4D-NOTES.md` §11 定案：第 4 章 MS-free 路线（C3／C4／F5）的**全部剩余数学** ＝
**`H¹(Γ⧸I,μ_p) ≅ κ^× / κ^×p`（`κ` 上的 Kummer 理论）** 这一件。它的两个等价面貌是：

* **C4／`hd_infl` 侧**：`(CI)` ＝ `ker v̄ ⊆ range(infl₁)`（逐点形态）—— 见 `Hyp610:55-70` 的
  诚实边界（"与 G1 墙同族，不在库内"）；
* **F5 侧**：GS `prop:prelim-kummer-valuation`(2) 的 `ker v̄ ≅ H¹(κ,μ_p)`。

本件把它**立成具名假设**（`CLAUDE.md`：外部已发表定理写成具名假设即得可标 ✓ 的条件定理，
与既有 `MerkurjevSuslin`（`Hyp691:136`）同一档次），并给出：

| 声明 | 内容 |
|---|---|
| **`UnramifiedKummer`** | 具名假设本体（逐字取 `Hyp610.residueSpan_le_range_infl2Res` 的 `hCI` 形状） |
| **`unramifiedKummer_of_subsingleton`** | **非空见证**（`L1`＋`L10①`）：`VKG` 单点时假设成立 |
| **`residueSpan_le_range_infl2Res_of_kummer`** | 假设 ⟹ `residueSpan ≤ range infl₂`（＝ `Hyp610` 直出） |

## 剩下的纯机械件（`S67-4D-NOTES.md` §10）

`Hyp743`（`∂²(Inf₂ w) = 0`，`ℤ`-系数载体）与 `Hyp610`（cup-膨胀相容，`ZMod p`-系数载体）
之间还差**两条载体桥**（`ofDiscreteModuleRestrictScalarsIntIso` 一族）。桥一旦接上，

```
∂² (cup y z) = ∂² (infl₂ (cupRes a b)) = ∂² (Inf₂ (…)) = 0     -- Kummer ＋ cup 相容 ＋ Hyp743
```
即得 **`hd_infl`**（`Hyp342` 的第二个输入）；再补 C3 的 `∂¹((−π))=1` 与分裂即得 **`hd_cup_pi`**。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- ★★★★★ **具名假设：不通歧 Kummer 理论**（GS `prop:prelim-kummer-valuation`(2) 的等价形态）。

「`ker v̄` 的每个元素都是膨胀 `infl₁ : H¹(Γ⧸I,μ_p) → H¹(Γ,μ_p)` 的像」
—— 即：**不分歧的单位类就是来自剩余域的类**。

⚠ 逐字取 `Hyp610.residueSpan_le_range_infl2Res` 的 `hCI` 形状，以便与 `Hyp610` 直接对接。 -/
def UnramifiedKummer (v : Fˣ →* Multiplicative ℤ) (hpF : IsUnit (p : F)) : Prop :=
  ∀ y : VKG F p v hpF,
    ∃ a : ResH1Type (F := F) p I, infl1Res (F := F) p I a = (y : GaloBase.V F p)

/-- ★★★★ **非空见证**（`L1`＋`L10①`）：`VKG` 单点时 `UnramifiedKummer` 自动成立
（取 `a = 0`；`infl1Res 0 = 0`）。即该假设类**非空**。 -/
theorem unramifiedKummer_of_subsingleton (v : Fˣ →* Multiplicative ℤ)
    (hpF : IsUnit (p : F)) [Subsingleton (GaloBase.V F p)] :
    UnramifiedKummer (F := F) p I v hpF := by
  intro y
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact Subsingleton.elim _ _

/-- ★★★★★ **`UnramifiedKummer` ⟹ `residueSpan ≤ range infl₂`**（`Hyp610` 直出）。

这一步是 `(R2)`／`residueSpan` 被杀死的**组合入口**：有了 `residueSpan ≤ range infl₂`，
再用 `Hyp743`（`∂²` 在 `range Inf₂` 上为零）即得 `∂²` 在 `residueSpan` 上为零。 -/
theorem residueSpan_le_range_infl2Res_of_kummer
    (v : Fˣ →* Multiplicative ℤ) (hpF : IsUnit (p : F))
    (h : UnramifiedKummer (F := F) p I (v := v) hpF) :
    residueSpan (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hpF)
      ≤ LinearMap.range (infl2Res (F := F) p I) :=
  residueSpan_le_range_infl2Res (F := F) (p := p) (I := I) hpF (fun y => h y)

end L20261018

#print axioms L20261018.UnramifiedKummer
#print axioms L20261018.unramifiedKummer_of_subsingleton
#print axioms L20261018.residueSpan_le_range_infl2Res_of_kummer
