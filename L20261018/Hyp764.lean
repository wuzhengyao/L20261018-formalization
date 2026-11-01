import L20261018.Hyp763

/-!
# S72 R4：第 4 章**假设去膨胀审计** —— 把 `D` 换成第 2 章 `prop:prelim-residue`

## 审计结论（先给判定，再给证据）

对 §4 的 4 条陈述逐条核其 Lean 假设与论文假设的对应关系。**结论：无数学膨胀**，
但两种**编码**需要显式化；本件把其中最重的一种**机检去抽象**。

| 论文假设（`raw/L20261018.tex` §4） | Lean 对应 | 分类 |
|---|---|---|
| `p` 为奇素数 | `[Fact p.Prime]` ＋ `p ≠ 2` | (a) 逐字 ✅ |
| `F` 特征 `0` | `[CharZero F]`（本件）／`hp : IsUnit (p:F)`（原版） | (a) ✅（原版**更弱**：不要求 char 0） |
| `μ_p ⊂ F` | `[HasEnoughRootsOfUnity F p]` | (a) 逐字 ✅ |
| `(F,v)` Hensel 离散赋值域、剩余域 `K`、`char K ≠ p` | **`D : HenselResidueData`（原版）** → 本件换成**第 2 章 `prop:prelim-residue` 的两条值** | (b) **本件消除** |
| `(a_1)∪(a_2) ≠ 0` | `hne : cupLin (kummerExplicit a1) (kummerExplicit a2) ≠ 0` | (a) 逐字 ✅ |
| `v̄\|_U ≠ 0` | `∃ u ∈ plane …, val u ≠ 0` | (a) 逐字 ✅ |
| `D` 指数 `p²`（仅 `thm:ramified`(2) 用） | `h : indOfH2 … = p^2` | (a) 逐字 ✅；且 `thm_ramified_1` **不用**它（比论文更强） |
| `E = F(a_1^{1/p},a_2^{1/p})` 有限 | `[FiniteDimensional F (Efield Δ)]`、`[IsGalois F (Efield Δ)]`、`hroots`、`hU : IsOpen …`、`IsFiniteRelIndex Δ` | (b) **Kummer 构造的载体编码**——论文里由 `E` 的定义自动成立 |

**唯一未消的编码 = 表中最后一行**（`thm_ramified_1` 的 5 条 Kummer 载体实例）。它在论文里
是 `E := F(a_1^{1/p},a_2^{1/p})` 的**定义后果**，属第 2／3 章的 Kummer 理论。
**登记为 `∅-unchecked` 的影响面**：若将来把 `Δ` 固定成 `⟨a_1,a_2⟩`，这 5 条应可导出。

## 本件的机检增量（两件）

1. **`isUnit_natCast_of_charZero`**：论文的「`F` 特征 `0`」⟹ `IsUnit (p:F)`
   —— 把原版里那条**比论文更强**的假设接回论文的假设。
2. **`ramified_vanishing_paper`** ★★★★：`lem:ramified-vanishing` 的**去抽象版**——
   不再要求不透明的 `D : HenselResidueData`，只要求**第 2 章 `prop:prelim-residue`** 的内容：
   * `hsurj`／`hval_infl` ＝ `prop:prelim-kummer-valuation`（`ker v̄ = im Inf`）；
   * `d` 的两条值 `hd_infl`／`hd_cup_pi` ＝ `prop:prelim-residue`(1) 的
     `∂₂(inf ξ) = 0`／`∂₂(inf η ∪ (π)) = η`。
   装配链全是**已机检件**：`Hyp338.tameResidueFacts_of_residueMap` ⟹ `Hyp161.henselResidueDataOfFacts`
   ⟹ `Hyp110.ramified_vanishing_explicit`。
   **⟹ 第 4 章对第 2 章的依赖恰是论文写的那两条，不多不少**（`L48` 照原文）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

section CharZero

variable {F : Type} [Field F] [CharZero F] (p : ℕ) [Fact p.Prime]

/-- ★★★ **论文的「`F` 特征 `0`」⟹ `IsUnit (p : F)`**。

原版 `Hyp108`／`Hyp110`／`Hyp111` 直接假设 `IsUnit (p:F)`——那比论文**更强**（不要求 char 0）。
本件把它接回论文的假设（`char 0 ⟹ p ≠ 0 ⟹ p` 是单位）。 -/
theorem isUnit_natCast_of_charZero : IsUnit (p : F) :=
  (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero).isUnit

end CharZero

section PaperLevel

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ **`lem:ramified-vanishing` 的去抽象版**：只依赖第 2 章 `prop:prelim-residue`。

**与 `Hyp110.ramified_vanishing_explicit` 的差别**：那条要求一个**不透明的**
`D : HenselResidueData …`；本件把它**构造**出来（`Hyp161.henselResidueDataOfFacts`），
只要求第 2 章的两组内容：

* `hval_infl`／`hsurj` ＝ `prop:prelim-kummer-valuation`：`ker v̄ = im(Inf)`；
* `d` 的 `hd_infl`／`hd_cup_pi` ＝ `prop:prelim-residue`(1)：`∂₂(inf ξ)=0`、`∂₂(inf η ∪ (π))=η`。

注意 `v̄` 的目标是 `ZMod p`，故 `VK = ker v̄`（这正是论文里 `ker \bar v` 的角色，
`Hyp338` 的 `hsurj`／`hval_infl` 恰好就是它的两条性质）。 -/
theorem ramified_vanishing_paper
    (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (val : H1 (AbsoluteGaloisGroup F) (ZMod p) →ₗ[ZMod p] (ZMod p))
    (π : H1 (AbsoluteGaloisGroup F) (ZMod p)) (hπ : val π = 1)
    (hskew : ∀ x y : H1 (AbsoluteGaloisGroup F) (ZMod p),
      (Theo352.cupLin x) y = - (Theo352.cupLin y) x)
    (infl : ↥(LinearMap.ker val) →ₗ[ZMod p] H1 (AbsoluteGaloisGroup F) (ZMod p))
    (hval_infl : ∀ y : ↥(LinearMap.ker val), val (infl y) = 0)
    (hsurj : ∀ x : H1 (AbsoluteGaloisGroup F) (ZMod p), val x = 0 →
      ∃ y : ↥(LinearMap.ker val), infl y = x)
    (d : H2 (AbsoluteGaloisGroup F) (ZMod p) →ₗ[ZMod p] ↥(LinearMap.ker val))
    (hd_infl : ∀ y z : ↥(LinearMap.ker val),
      d ((Theo352.cupLin (infl y)) (infl z)) = 0)
    (hd_cup_pi : ∀ y : ↥(LinearMap.ker val), d ((Theo352.cupLin (infl y)) π) = y)
    (a1 a2 : Fˣ)
    (hne : (Theo352.cupLin (GaloCup.kummerExplicit (p := p) hp a1))
      (GaloCup.kummerExplicit (p := p) hp a2) ≠ 0)
    (hv : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (p := p) hp a1)
      (GaloCup.kummerExplicit (p := p) hp a2), val u ≠ 0) :
    (Theo352.Bex (p := p) hp hne).Uperp = ⊥ :=
  ramified_vanishing_explicit (F := F) (p := p) hp hp2 ↥(LinearMap.ker val)
    (henselResidueDataOfFacts (k := ZMod p)
      (V := H1 (AbsoluteGaloisGroup F) (ZMod p))
      (H2 := H2 (AbsoluteGaloisGroup F) (ZMod p))
      (Theo352.cupLin) val π hπ hskew
      (tameResidueFacts_of_residueMap (k := ZMod p)
        (V := H1 (AbsoluteGaloisGroup F) (ZMod p))
        (H2 := H2 (AbsoluteGaloisGroup F) (ZMod p))
        (VK := ↥(LinearMap.ker val))
        (Theo352.cupLin) val π infl hval_infl hsurj d hd_infl hd_cup_pi))
    a1 a2 hne hv

end PaperLevel

end L20261018

#print axioms L20261018.isUnit_natCast_of_charZero
#print axioms L20261018.ramified_vanishing_paper
