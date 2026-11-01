import L20261018.Ch4.Step030_unramified_decomposition_algebraic

/-!
# R1175（**路线更正后的第一块：把 `UnitsCupVanish` 归约到两条显式范数计算 ＋ 一条 `𝒪^×` 有限性**）

## 背景（`L48`：读 `raw/Neukirch1999`）

`PLAN-R2` §H-37–§H-39 曾判「唯一缺口 = 一般 Hensel 的不分歧性，须自建赋值延拓（周级）」。
用户提示 `Neukirch1999` 有 henselian valuation —— `raw/Neukirch1999.pdf` ＋ `.tex` **都在库**。
读出 Thm 2.6（`:4795` henselian ⟹ 赋值唯一延拓）、Def 2.7（`:5069` 不分歧定义）、
`:4535`（**Teichmüller 分解 `𝒪^× = μ_{q-1} × U^{(1)}`**）。

**但更关键的是**：`normGroup K L` 的定义（`raw/TauCeti/TauCeti/RingTheory/Norm/Units.lean:87`）是

```lean
noncomputable def normGroup [_hfin : Module.Finite K L] : Subgroup Kˣ :=
  (Algebra.normUnits K : Lˣ →* Kˣ).range
```

⟹ `u ∈ normGroup F L` ⟺ **存在显式 `y : Lˣ` 使 `Algebra.norm F ↑y = ↑u`**。**纯代数，不用赋值。**

而 `Hyp288.cup_kummerClass_unit_eq_zero_of_norm` 已机检 `u ∈ normGroup F L ⟹ (u)∪(w) = 0`。
⟹ **`UnitsCupVanish` 完全不需要赋值延拓**，只需：

| # | 要证 | 取哪个 `y` | 状态 |
|---|---|---|---|
| **(N1)** | `(x)^p ∈ normGroup F L` | `Units.map (algebraMap F L) x` | ★ **本轮机检** |
| **(N2)** | `w ∈ normGroup F L`（`s^p = w`） | `s`（`minpoly = X^p − C w` ⟹ `N(s) = (−1)^{p+1}w = w`） | 残余（`aroots`／resultant 路） |
| **(P)** | `∀ 单位 u, ∃ k z, u·w^(−k) = z^p` | —— | 残余（Neukirch `:4535` Teichmüller，**只涉 `𝒪_F`，不涉 `L`**） |

(N1) ＋ (N2) ＋ (P) ⟹ `u ∈ normGroup F L` ⟹ `(u)∪(w) = 0`（本文件 §3 组装，机检）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`pow_mem_normGroup`** | ★★★★★ **(N1)**：`finrank F L = p ⟹ (x)^p ∈ normGroup F L` |
| **`mem_normGroup_of_powClassGen`** | ★★★★★ **(N2) ＋ (P) ⟹ `u ∈ normGroup F L`** |
| **`cup_kummerClass_unit_eq_zero_of_norm_pow`** | ★★★★★ **合成：`(u)∪(w) = 0`，且假设**只有 `w ∈ normGroup` 与 (P) —— **`s^p = w` 与 `adjoin = ⊤` 之外零赋值输入** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ValuativeRel

namespace L20261018

section NormPow

variable {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ## 1. **(N1)** `p` 次幂属于范数群 -/

/-- ★★★★★ **(N1)：`x^p ∈ normGroup F L`**（当 `[L : F] = p`）。

取 `y = Units.map (algebraMap F L) x`：`Algebra.norm F (algebraMap x) = x ^ [L:F] = x^p`
（`Algebra.norm_algebraMap`）。**纯代数，无赋值。** -/
theorem pow_mem_normGroup {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L]
    (hfr : Module.finrank F L = p) (x : Fˣ) :
    x ^ p ∈ normGroup F L := by
  rw [mem_normGroup_iff]
  refine ⟨Units.map (algebraMap F L).toMonoidHom x, ?_⟩
  show Algebra.norm F (algebraMap F L (x : F)) = ((x ^ p : Fˣ) : F)
  rw [Algebra.norm_algebraMap, hfr]
  simp

/-! ## 2. **(N2) ＋ (P) ⟹ `u ∈ normGroup`** -/

/-- **(P)**：每个单位都是 `w^k · (p 次幂)` —— 即 `𝒪^×/(𝒪^×)^p` 由 `w` 的类生成。 -/
def PowClassGen (v : Fˣ →* Multiplicative ℤ) (w : Fˣ) : Prop :=
  ∀ u : Fˣ, v u = 1 → ∃ (k : ℤ) (z : Fˣ), u * w ^ (-k) = z ^ p

/-- ★★★★★ **(N2) ＋ (P) ⟹ `u ∈ normGroup F L`**：`w ∈ normGroup` 且 (P) 且 `[L:F] = p`
⟹ 每个单位 `u` 都在范数群内。 -/
theorem mem_normGroup_of_powClassGen {L : Type*} [Field L] [Algebra F L]
    [FiniteDimensional F L] {v : Fˣ →* Multiplicative ℤ} {w : Fˣ}
    (hfr : Module.finrank F L = p) (hwnorm : w ∈ normGroup F L)
    (hP : PowClassGen (p := p) v w) {u : Fˣ} (hu : v u = 1) :
    u ∈ normGroup F L := by
  obtain ⟨k, z, hz⟩ := hP u hu
  have hzp : z ^ p ∈ normGroup F L := pow_mem_normGroup (p := p) hfr z
  have hwk : w ^ k ∈ normGroup F L := (normGroup F L).zpow_mem hwnorm k
  have hEq : u = z ^ p * w ^ k := by
    rw [← hz]
    group
  rw [hEq]
  exact mul_mem hzp hwk

/-! ## 3. 组装：`(u)∪(w) = 0` -/

/-- ★★★★★ **单位 × 单位杯积为零 —— 假设只有 `(N2)` 与 `(P)`**。

与 `Hyp288.cup_kummer_class_unit_eq_zero_of_norm` 相比，`u ∈ normGroup` 已由
(N1)＋(N2)＋(P) 推出；**除 `s^p = w` 与 `F⟮s⟯ = ⊤` 外没有任何赋值／不分歧输入**。 -/
theorem cup_kummerClass_unit_eq_zero_of_norm_pow {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) {v : Fˣ →* Multiplicative ℤ} {w : Fˣ}
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] {s : L}
    (hfr : Module.finrank F L = p)
    (hs : s ^ p = algebraMap F L ((w : Fˣ) : F))
    (hgen : IntermediateField.adjoin F ({s} : Set L) = ⊤)
    (hwnorm : w ∈ normGroup F L)
    (hP : PowClassGen (p := p) v w)
    {u : Fˣ} (hu : v u = 1) :
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 :=
  cup_kummerClass_unit_eq_zero_of_norm (p := p) hζ hp hs hgen
    (mem_normGroup_of_powClassGen (p := p) hfr hwnorm hP hu)

end NormPow

end L20261018

#print axioms L20261018.pow_mem_normGroup
#print axioms L20261018.mem_normGroup_of_powClassGen
#print axioms L20261018.cup_kummerClass_unit_eq_zero_of_norm_pow
