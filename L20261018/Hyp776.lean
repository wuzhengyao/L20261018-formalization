import Hyp775
import Hyp148
import Hyp334

/-!
# S74 R2：(甲1) 归约为**一条非零杯积**——`finrank VKG = 1` 只差 `∃ a₁ a₂, cup a₁ a₂ ≠ 0`

## 改道后的清单里，(甲1) 原写作"`Nat.card VKG = p` ／ `Nat.card (Hom_cont(Ẑ,ℤ/p)) = p`"（S73 `GAP3-PLAN` §1.2 甲）。
**本轮实测不必从零造**：`Hyp148.finrank_ker_valLin_eq_one` 已经给出

```
hp : IsUnit (p : F)  hp2 : NeZero (2 : ZMod p)  hpu : IsUnit (p : 𝒪[F])
hne : GaloBase.cup a₁ a₂ ≠ 0        ← 唯一的数学输入
[FiniteDimensional (ZMod p) (GaloBase.V F p)]
⟹ finrank (ker v̄) = 1
```

把 `v` 换成 `TauCeti.normalizedValuation F`（`valLin_eq_valLinOf_normalizedValuation`，本战役
`Hyp747` 文件头已论证这只是归约），即成本件的 `finrank_VKG_eq_one`。

⚠ **S73 §1.2 的 (甲) 原写作「`Nat.card VKG = p`，须自建 `Hom_cont(Ẑ,ℤ/p) ≅ ℤ/p`」——该判决作废**：
`finrank` 版够用（下游只需要"1 维"，不需要基数），而 `finrank` 版**在库内**（`Hyp148`）。
`Nat.card` 版另需 `Finite (GaloBase.V F p)` 实例，本轮未做。

## 为什么这条有用（(甲1) 的真实形状）

改道后的路线（`GAP3-PLAN.md` §0.1ter）要 `VKG` **一维**，理由是
`Ψ := d ∘ Φ : VKG → VKG` 必须是**标量**。本轮把"造 `Nat.card VKG = p`"（S73 判为需自建 `Hom_cont(Ẑ,ℤ/p)`）
换成"**喂一条非零杯积给 `Hyp148`**"——输入从"一条基数计算"变成"一次非退化性"，而后者
TauCeti 已有 `ClassFieldTheory.separatingRight_localSymbol`（Hilbert 配对右分离）与
`tateDualityPairing_perfect`（局部 Tate 对偶）。

## 诚实边界

* `[FiniteDimensional (ZMod p) (GaloBase.V F p)]`、`IsUnit (p : 𝒪[F])`、`hp2` 都是**论文层/技术**前提，
  与 `Hyp342`／`Hyp385`／`Hyp148` 的既有口径**一致**（不是本件新增的假设）。
* `hne` **未兑现**：它的兑现需要 `muP ↔ trivialFp ↔ muNRep` 的 `H^d` 桥（`GAP3-PLAN.md` §7.2 第 1 条）。
* 本件**不**触及 `∂² ≠ 0`、齐次性、装配。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **(甲1) 归约**：`finrank VKG = 1` 只需**一条非零杯积**。

`Hyp148.finrank_ker_valLin_eq_one`（一般 `F`）＋ `valLin = valLinOf normalizedValuation`
（`Hyp333` 的 `rfl`-级桥）＋ `VKG` 的 `abbrev` 展开（`Hyp342`）。 -/
theorem finrank_VKG_eq_one (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hpu : IsUnit (p : ↥𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) (VKG F p (TauCeti.normalizedValuation F) hp) = 1 := by
  have h := finrank_ker_valLin_eq_one (F := F) (p := p) hp hp2 hpu hne
  rw [← valLin_eq_valLinOf_normalizedValuation] at h
  exact h

end L20261018

#print axioms L20261018.finrank_VKG_eq_one
