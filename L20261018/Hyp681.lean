import L20261018.Hyp302
import L20261018.Hyp120

/-!
# S59 R2：**`κ` 的两条平凡性** —— `(K1)`（Hensel）＋ `(K2)`（`p` 奇）—— `(R2)` 的 Steinberg 路线的基建

## 动机（`PROMPT-S60` §①-2 的两条输入）

`Hyp680` 把 `(R2)` 压成**一条等式** `res ∘ ∪ = tame`（`tame a b = ⟨v̄(b)·a − v̄(a)·b⟩ ∈ ker v̄`）。
该等式的内容是「`tame` 是 `∪` 的函数」，而 `tame` 是 **Steinberg 符号**，故只需在**关系**上验。
其中唯一需要**算术输入**的是 Steinberg 关系 `tame (a) (1−a) = 0`：它的四情形证明
（`PROMPT-S60` §①-2 的表）**只用两条**关于 Kummer 类 `κ := KummerBridge.kummerClass` 的事实：

> **(K1)** `κ(u) = 0` 对 `u ≡ 1 (mod π)`（即 `residue ↑u = 1`）—— **Hensel**
> **(K2)** `κ(−1) = 0` —— **`p` 奇**（`(−1)^p = −1`）

本件机检这两条。

## 关键侦察读数（`L46`；`grep` ＋ `#check` 实测）

| 引理 | 签名里的假设 | 能否用于（K1） |
|---|---|---|
| `Hyp302.exists_pow_of_rho_eq_one` | **含 `[Finite 𝓀[F]]`** | ✗ **不能**（会把 `[Finite (ResidueField)]` 重新引入，等于退回档 1–5） |
| **`Hyp301.exists_pow_of_residue_eq_one`** | `HenselianRing`＋`p ≠ 0`＋`IsUnit ↑p`＋`residue ↑a = 1` | ✅ **用它**（**不带**残域有限） |

⟹ （K1）**不需要** `[Finite (ResidueField)]`——这正是「无限残域」情形所要求的
（`Hyp302.unitsCupVanish` 的引擎 `exists_pow_mul_pow_of_isCyclic` 则是**需要**的，
故六档路线止步于有限残域；本件给的是**另一条路**的入口）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`kummerClass_neg_one`** | ★ `κ(−1) = 0`（`p ≠ 2`） |
| **`kummerClass_eq_zero_of_residue_eq_one`** | ★★ `residue ↑u = 1 ⟹ κ(u) = 0`（**Hensel，无残域有限假设**） |

## 诚实边界

* 本件**不**证 `TameSymbolFactors`（`(R2)` 仍 `∅-open`）；只补它的 Steinberg 路线的**算术输入**。
* 不增 CH4 覆盖率（陈述层 9/9 已闭）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section KappaTrivial

variable {F : Type} [Field F] [ValuativeRel F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★ **(K2)**：`(−1)` 的 Kummer 类为零（`p` 奇 ⟹ `(−1)^p = −1`）。

论文 `raw/L20261018.tex:1044`：「因为 `p` 为奇数，`-1=(-1)^p` 在右侧的 Kummer 商中为零类」
—— 这正是本引理。 -/
-- @source file=raw/L20261018.tex locator=label:eq:prelim-tame quote="(-1)^{v(a)v(b)}"
theorem kummerClass_neg_one (hpF : IsUnit (p : F)) (hp2 : p ≠ 2) :
    KummerBridge.kummerClass F p hpF (-1) = 0 := by
  obtain hp2' | hodd := (Fact.out : p.Prime).eq_two_or_odd
  · exact absurd hp2' hp2
  have h : ((-1 : Fˣ)) ^ p = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hodd)
  rw [← h]
  exact kummerClass_pow_prime (F := F) (p := p) hpF (-1)

/-- ★★ **(K1)**：`u ≡ 1 (mod π)` ⟹ `κ(u) = 0`（**Hensel**；**不带** `[Finite (ResidueField)]`）。

用 `Hyp301.exists_pow_of_residue_eq_one`（**不是** `Hyp302.exists_pow_of_rho_eq_one`，
后者带 `[Finite 𝓀[F]]`）＋ `Hyp120.kummerClass_pow_prime`。 -/
theorem kummerClass_eq_zero_of_residue_eq_one (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (a : (↥𝒪[F])ˣ) (ha : IsLocalRing.residue ↥𝒪[F] ((a : ↥𝒪[F])) = 1) :
    KummerBridge.kummerClass F p hpF (Units.map (algebraMap ↥𝒪[F] F).toMonoidHom a) = 0 := by
  obtain ⟨c, hc⟩ := exists_pow_of_residue_eq_one (F := F) p (NeZero.ne p) hp ha
  have h1 : Units.map (algebraMap ↥𝒪[F] F).toMonoidHom a
      = (Units.map (algebraMap ↥𝒪[F] F).toMonoidHom c) ^ p := by
    rw [← hc, map_pow]
  rw [h1, kummerClass_pow_prime (F := F) (p := p) hpF]

end KappaTrivial

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.kummerClass_neg_one
#print axioms L20261018.kummerClass_eq_zero_of_residue_eq_one
