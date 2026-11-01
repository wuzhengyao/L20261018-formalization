import L20261018.Hyp614
import L20261018.Hyp613

/-!
# S51 R6：`μ_p ⊆ F ⟹ μ_p ⊆ κ`（`isPrimitiveRoot_residue`）＋ 档 ⑦ ＋ 七档索引

## 0 本件的定位

S51 R1–R5 已把档 ⑥ 收口为 `Hyp614.ch4TameSymbolHyp_of_subsingleton_H2_residueField`，
它的三条假设全部具名（`φ`／`(CI)`／`H²(κ,μ_p)=0`）。**本轮先做一件能立刻机检的论文前提**：

> 论文设定 `μ_p ⊆ F`。但**剩余侧**的 Kummer 类 `(ū)`、`u ∈ κ^×` 需要 `μ_p ⊆ κ`。
> 这一步由 `Hyp613`（`μ_n ↪ κ^×` 单射）**推出**：**`p` 次本原单位根的剩余仍是 `p` 次本原单位根**。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`isPrimitiveRoot_residue`** | ★★★★★ **`IsPrimitiveRoot ζ p ⟹ IsPrimitiveRoot (ρ ζ) p`**（＝「`μ_p ⊆ F ⟹ μ_p ⊆ κ`」） |
| **`ch4TameSymbolHyp_of_subsingleton_H2_domain`** | ★★★ **档 ⑦**：`H²(F, μ_p) = 0 ⟹ `Ch4TameSymbolHyp`（与六档不重叠的退化档） |
| `#check` 七档索引 | 见 §3（每一格都是机检声明） |

## 2 `isPrimitiveRoot_residue` 的证明（两行 + 一处复用）

* `(ρ ζ)^p = ρ(ζ^p) = 1`（`map_pow` ＋ `IsPrimitiveRoot.pow_eq_one`）；
* `ρ ζ ≠ 1`：若 `ρ ζ = 1`，则 `ρ (ζ - 1) = 0`；而 `Hyp613.isUnit_sub_one_of_pow_eq_one`
  给 `IsUnit (ζ - 1)` ⟹ `0` 是单位，矛盾。

⟹ `orderOf (ρ ζ) = p`（`orderOf_eq_prime`），即 `IsPrimitiveRoot (ρ ζ) p`。

**注意本件没有新数学**：它把 `Hyp613` 的「单射」翻译成「本原性保持」，而后者才是论文真正引用的形态。

## 3 七档索引（`#check` 机检）

见文件末 `section Index`。七档分别是：
① 有限剩余 `Hyp302`／② `κ^×` `p`-可除 `Hyp430`／③ `κ^×` 循环 `Hyp430`／④ 完备 `Hyp290`／
⑤ `dim ker v̄ ≤ 1` `Hyp607`／**⑥ `(CI)` ＋ `H²(κ,μ_p)=0`（`Hyp614`，规范载体）**／
⑦ `H²(F,μ_p)=0`（本件，退化档）。

## 4 诚实边界

* 档 ⑦ 是**退化**档：`F` 的 `H²` 为零时第 4 章的 Kummer 配对理论本身退化（无 Brauer 类），
  故它只作**结构完整性**与「假设类不空」的补充，**不增覆盖率**。
* `isPrimitiveRoot_residue` 的**前提**是 `IsPrimitiveRoot ζ p` 在 `↥𝒪[F]` 里（不是 `F` 里）；
  从 `μ_p ⊆ F` 到 `ζ ∈ 𝒪[F]` 还需「单位根是单位」（`v(ζ)=0` 由 `ζ^p=1` 得），本件**未形式化**该步。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section ResidueRoots

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  (p : ℕ) [NeZero p] [Fact p.Prime]

/-- ★★★★★ **`μ_p ⊆ F ⟹ μ_p ⊆ κ`**：`p` 次本原单位根的剩余仍是 `p` 次本原单位根。 -/
theorem isPrimitiveRoot_residue (hp : IsUnit (p : ↥𝒪[F])) {ζ : ↥𝒪[F]}
    (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (IsLocalRing.residue ↥𝒪[F] ζ) p := by
  rw [IsPrimitiveRoot.iff_orderOf]
  haveI : Nontrivial ↥𝒪[F] := inferInstance
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, hζ.pow_eq_one, map_one]
  · intro hcon
    have hne : ζ ≠ 1 := by
      intro h1
      rw [IsPrimitiveRoot.iff_orderOf, h1, orderOf_one] at hζ
      exact (Fact.out : p.Prime).ne_one hζ.symm
    have hunit : IsUnit (ζ - 1) :=
      isUnit_sub_one_of_pow_eq_one ↥𝒪[F] p hp hζ.pow_eq_one hne
    have h0 : IsLocalRing.residue ↥𝒪[F] (ζ - 1) = 0 := by
      rw [map_sub, hcon, map_one, sub_self]
    have : IsUnit (IsLocalRing.residue ↥𝒪[F] (ζ - 1)) := hunit.map (IsLocalRing.residue ↥𝒪[F])
    rw [h0] at this
    exact not_isUnit_zero this

end ResidueRoots

/-! ## 档 ⑦：`H²(F, μ_p) = 0`（退化档） -/

section DomainVanishing

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★ **档 ⑦（退化）**：若 `F` **自身**的 `H²(F, μ_p)` 为零，则 `Ch4TameSymbolHyp` 成立。

⚠ 这是**退化**档：`H²(F,μ_p)=0` 时第 4 章的 Kummer 配对理论本身退化（无 Brauer 类），
故只作结构完整性与「假设类不空」的补充，**不增覆盖率**。 -/
theorem ch4TameSymbolHyp_of_subsingleton_H2_domain
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (h : Subsingleton (GaloBase.H2 F p)) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF := by
  refine (ch4TameSymbolHyp_iff_disjoint (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2).mpr ?_
  rw [Submodule.disjoint_def]
  intro x _ _
  exact @Subsingleton.elim (GaloBase.H2 F p) h x 0

end DomainVanishing

/-! ## 七档索引（`#check` 机检；`PROOF-MAP.md` §1 的每一格都取自本节读数） -/

section Index

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

-- 唯一下游装配（`residueSpan = ⊥` 正规形）
#check @ch4TameSymbolHyp_of_residueSpan_eq_bot

-- 档 ①–⑤：各给 `residueSpan = ⊥`
#check @unitsCupVanish_of_finite
#check @unitsCupVanish_of_divisible
#check @unitsCupVanish_of_cyclicUnits
#check @unitsCupVanish_complete
#check @residueSpan_eq_bot_of_finrank_le_one

-- 档 ⑥（**最终形态**，规范载体：`hκ` 就是字面的 `H²(κ, μ_p) = 0`）
#check @ch4TameSymbolHyp_of_subsingleton_H2_residueField
#check @residueSpan_eq_bot_of_subsingleton_H2

-- 档 ⑦（退化）
#check @ch4TameSymbolHyp_of_subsingleton_H2_domain

-- 论文前提：`μ_p ⊆ κ`
#check @isPrimitiveRoot_residue

end Index

end L20261018

#print axioms L20261018.isPrimitiveRoot_residue
#print axioms L20261018.ch4TameSymbolHyp_of_subsingleton_H2_domain
