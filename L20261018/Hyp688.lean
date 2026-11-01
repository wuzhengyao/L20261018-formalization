import Hyp682
import Hyp681
import Hyp301
import Hyp638
import Hyp163

/-!
# S61 R1：**A3 ＝ `tame(a, 1−a) = 0`**（具体载体，四情形）—— `(G2)` 的义务格 A3

## 动机（`G2-PLAN.md` §2 的 A3 格）

`(R2)` 已压成 `TameSymbolFactors cup val`（`∃ res, res ∘ ∪ = tame`，`Hyp680`），其内容 ＝
`ker ∪ ⊆ ker tame`。`tame` 是 **Steinberg 符号**，论文逐字（`raw/L20261018.tex:739–740`）：

> 其分次环由乘法群 $F^\times$ 的张量代数模去 Steinberg 关系
> $\{a,1-a\}=0$ 得到。

故「在**关系**上验 `ker ∪ ⊆ ker tame`」的第一条就是本件：`tame(a, 1−a) = 0`。

## 归约链（全部机检，无一处新假设）

```
Hyp682.tameExpr_eq_zero_iff      tame a b = 0 ⟺ v̄(b)·a = v̄(a)·b
Hyp162.valLinOf_kummerClass      v̄(κ x) = v(x) mod p
Hyp36.kummerClass_mul            κ(xy) = κx + κy
Hyp681.kummerClass_neg_one       κ(−1) = 0                        （(K2)，p 奇）
Hyp681.kummerClass_eq_zero_of_residue_eq_one  residue u = 1 ⟹ κ(u) = 0   （(K1)，Hensel）
```

⟹ 目标化归为**整数等式** `(v(1−a) mod p) • κ a = (v a mod p) • κ(1−a)`，再按 `v a` 的符号分四情形。

## 四情形（与 `PROMPT-S61` §①-2 的表逐条对应）

| 情形 | 需要的事实 | 来源 |
|---|---|---|
| `v a > 0` | `1−a` 是**主单位**：`κ(1−a)=0` 且 `v(1−a)=0` | `kummerClass_oneSub_eq_zero_of_val_pos` |
| `v a = 0`、`v(a−1) > 0` | `a ∈ 1+𝔪` ⟹ `κ(a)=0` | (K1) |
| `v a = 0`、`v(a−1) = 0` | 两侧 `v̄` 全为 `0` ⟹ 平凡 | — |
| `v a < 0` | `1−a = −a(1−a⁻¹)`、`a⁻¹ ∈ 𝔪` ⟹ `v(1−a)=v a`、`κ(1−a)=κ a` | 情形 1 ＋ (K1)(K2) |

## ★ 本轮真正的**缺口发现**（不是重述，是 Prompt 表里被当作「显然」的一步）

`PROMPT-S61` 表把第三情形写成「`v̄a = 0` 且**两者皆单位**」。这不是额外假设——
它必须从 `v̄a = 0` 与 `a ≢ 1 (mod 𝔪)` **推**出来，而 Prompt 表没写怎么推。本件发现：

> `ValCompat` 只给 `0 ≤ v a ⟹ a ∈ 𝒪[F]`（`mem_integer`，**单向**）。
> 而第三情形要的恰恰是**逆方向** `a ∈ 𝒪[F] ⟹ 0 ≤ v a`。

**没有它，第三情形打不开**：`v a = 0` 只给 `a ∈ 𝒪^×`，从而 `a−1 ∈ 𝒪`；
要从「非情形 2（`¬0 < v(a−1)`）」得到 `v(a−1) = 0`，必须排除 `v(a−1) < 0`。
本件补上这条逆方向（`not_neg_val_of_mem_integer`，一行理想论论证：
`v x < 0 ⟹ v x⁻¹ > 0 ⟹ x⁻¹ ∈ 𝔪`，而 `x ∈ 𝒪`，故 `1 = x·x⁻¹ ∈ 𝔪`，矛盾）。

## 本件新增的基建（全部机检；都是 `ValCompat` 的**逆方向**族）

| 声明 | 内容 |
|---|---|
| **`not_neg_val_of_mem_integer`** | ★★★★ `a ∈ 𝒪[F] ⟹ ¬(v a < 0)`（**不需要** `a` 是 `𝒪[F]` 的单位——比「单位 ⟹ `v = 0`」更强） |
| `not_pos_val_of_isUnit` | `a ∈ 𝒪[F]^×` ⟹ `¬(0 < v a)` |
| **`toAdd_val_nonneg_of_mem_integer`** | ★★★★ `a ∈ 𝒪[F] ⟹ 0 ≤ v a`（`ValCompat` 的逆方向，第三情形的钥匙） |
| **`toAdd_val_eq_zero_of_isUnit`** | ★★★ `a ∈ 𝒪[F]^×` ⟹ `v a = 0` |
| `toAdd_val_neg_one` | `v(−1) = 0` |
| `oneSub`／`subOne` | `1−a`／`a−1` 作为 `Fˣ`（顶层 `def`，`LESSONS` B49） |
| `toAdd_val_oneSub` | `v(1−a) = v(a−1)` |

## 诚实边界

* 本件**不**证 `TameSymbolFactors`（`(R2)` 仍 `∅-open`）：A3 只是 `ker ∪ ⊆ ker tame` 需要的**一条**关系；
  `ker ∪` 的**生成性**（Steinberg／Matsumoto 层）仍是 `G2-PLAN` §2 的 A4 硬核。
* **不需要** `[Finite (ResidueField)]`：(K1) 走 `Hyp301.exists_pow_of_residue_eq_one`，不走 `Hyp302`。
* 携带 `[TopologicalSpace F]`：与第 4 章**全部**陈述的上下文一致（见 `FRONTIER.md` 的签名表）；
  它只经 `Hyp638.unitBase` 进入（`unitBase` 的定义所在的 section 带该变量），**不是**数学需要。
* 携带 `hp : IsUnit (p : ↥𝒪[F])`：这是 (K1) 的固有前提（`1+𝔪` 的 `p`-可除性需要 `p` 在 `𝒪[F]` 中可逆），
  与 `Hyp449.ch4TameSymbolHyp_of_dependent` 等既有陈述取同一组假设，**不是**本件引入的新缺口。

## 本轮工艺（`LESSONS` B53–B55，全为实弹）

* **B53**：`simp`／`simpa` 会把 `(1 : ↥𝒪[F]) ∈ 𝔪[F]` **直接化成 `False`**（`𝔪 = nonunits`，`simp` 会证掉它），
  故 `simpa using (Ideal.add_mem …)` 报出**看不懂的** `¬IsUnit ⟨1,⋯⟩ vs False`。
  改用 `rw [h3] at h2`（`h3 : … + … = 1`，`abel` 证）＋ 显式 `exact`。
* **B54**：`rw [map_one]` 在目标里出现 `Multiplicative.toAdd` 时会命中 **`toAdd` 自己的** `MulEquiv` 实例，
  把 `toAdd 1` 改写成 `1`（目标变成 `1 = 0`，报 `OneHomClass (Multiplicative ℤ ≃ ℤ)` 合成失败）。
  修法：**不写 `map_one`**，停在 `toAdd (1 : Multiplicative ℤ) = 0` 用 `rfl`；`map_mul` 写成 `map_mul v`。
* **B55**：`(↑(x⁻¹) : F) = (↑x)⁻¹` **不是** `rfl`（要 `Units.val_inv_eq_inv_val`），
  故 `rw [mul_inv_cancel₀]` 匹配不到目标里的 `↑a * ↑a⁻¹`（那是 `↑(a⁻¹)`）。先 `rw [Units.val_inv_eq_inv_val]`。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section TameSteinberg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ}

/-! ## 0. 局部环三件套（`IsLocalRing` API 的稳定包装） -/

theorem mem_maximalIdeal_iff_not_isUnit (x : ↥𝒪[F]) :
    x ∈ IsLocalRing.maximalIdeal ↥𝒪[F] ↔ ¬ IsUnit x :=
  IsLocalRing.mem_maximalIdeal x

theorem isUnit_of_notMem_maximalIdeal (x : ↥𝒪[F])
    (h : x ∉ IsLocalRing.maximalIdeal ↥𝒪[F]) : IsUnit x := by
  by_contra h'
  exact h ((IsLocalRing.mem_maximalIdeal x).mpr h')

theorem notMem_maximalIdeal_of_isUnit (x : ↥𝒪[F]) (h : IsUnit x) :
    x ∉ IsLocalRing.maximalIdeal ↥𝒪[F] := by
  intro hm
  exact ((IsLocalRing.mem_maximalIdeal x).mp hm) h

/-! ## 1. `v` 在 `𝒪[F]` 的**单位**上为 `0`（`ValCompat` 的逆方向） -/

/-- `v(−1) = 0`（纯乘性论证，不需要 `𝒪[F]`）。 -/
theorem toAdd_val_neg_one :
    Multiplicative.toAdd (v (-1)) = 0 := by
  have hmul : v (-1) * v (-1) = 1 := by
    rw [← map_mul]
    norm_num
  have h2 : Multiplicative.toAdd (v (-1)) + Multiplicative.toAdd (v (-1)) = 0 := by
    rw [← toAdd_mul', hmul]
    rfl
  omega

/-- **单位不在 `𝔪` 里** ⟹ `v ≤ 0`（`ValCompat` 的正向 `mem_maximalIdeal` 的逆否）。 -/
theorem not_pos_val_of_isUnit (hv : ValCompat (F := F) v) {x : Fˣ}
    (hint : (x : F) ∈ 𝒪[F]) (hunit : IsUnit (⟨(x : F), hint⟩ : ↥𝒪[F])) :
    ¬ (0 < Multiplicative.toAdd (v x)) := by
  intro h
  have hmem := (hv.mem_maximalIdeal x hint).mpr h
  exact notMem_maximalIdeal_of_isUnit _ hunit hmem

/-- ★★★★ **`𝒪[F]` 里没有负赋值的元素**（`ValCompat` 的**逆方向**，关键基建）。

反证：`v x < 0` ⟹ `v x⁻¹ > 0` ⟹ `x⁻¹ ∈ 𝔪`；而 `x ∈ 𝒪[F]`，故 `1 = x·x⁻¹ ∈ 𝔪`，矛盾。
（**不需要** `x` 是 `𝒪[F]` 的单位 —— 这正是本引理比「单位 ⟹ `v = 0`」更强的地方。） -/
theorem not_neg_val_of_mem_integer (hv : ValCompat (F := F) v) {x : Fˣ}
    (hint : (x : F) ∈ 𝒪[F]) :
    ¬ (Multiplicative.toAdd (v x) < 0) := by
  intro hneg
  have hsum : Multiplicative.toAdd (v x) + Multiplicative.toAdd (v x⁻¹) = 0 := by
    rw [← toAdd_mul', map_inv, mul_inv_cancel]
    rfl
  have hpos' : 0 < Multiplicative.toAdd (v x⁻¹) := by omega
  have hint' : ((x⁻¹ : Fˣ) : F) ∈ 𝒪[F] := hv.mem_integer x⁻¹ (by omega)
  have hmem : (⟨((x⁻¹ : Fˣ) : F), hint'⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
    (hv.mem_maximalIdeal x⁻¹ hint').mpr hpos'
  have h1 : (⟨(x : F), hint⟩ : ↥𝒪[F]) * (⟨((x⁻¹ : Fˣ) : F), hint'⟩ : ↥𝒪[F])
      ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
    Ideal.mul_mem_left _ _ hmem
  have hone : ((⟨(x : F), hint⟩ : ↥𝒪[F]) * (⟨((x⁻¹ : Fˣ) : F), hint'⟩ : ↥𝒪[F])) = 1 := by
    apply Subtype.ext
    show (x : F) * ((x⁻¹ : Fˣ) : F) = 1
    simp
  rw [hone] at h1
  exact notMem_maximalIdeal_of_isUnit _ isUnit_one h1

/-- ★★★ `u ∈ 𝒪[F]^×`（作为 `𝒪[F]` 的单位）⟹ `v u = 0`。 -/
theorem toAdd_val_eq_zero_of_isUnit (hv : ValCompat (F := F) v) {x : Fˣ}
    (hint : (x : F) ∈ 𝒪[F]) (hunit : IsUnit (⟨(x : F), hint⟩ : ↥𝒪[F])) :
    Multiplicative.toAdd (v x) = 0 := by
  have h1 := not_pos_val_of_isUnit hv hint hunit
  have h2 := not_neg_val_of_mem_integer hv hint
  omega

/-- ★★★★ **`ValCompat` 的逆方向**：`a ∈ 𝒪[F]` ⟹ `0 ≤ v a`。

`ValCompat.mem_integer` 只给正向；四情形的第三种（`v a = 0` 且 `a` 是单位）必须用本引理
把 `a − 1 ∈ 𝒪` 变成 `v(a−1) ≥ 0`，否则 `v(a−1) > 0` 之外还剩 `v(a−1) < 0` 这个**不可能**
但**打不开**的分支。 -/
theorem toAdd_val_nonneg_of_mem_integer (hv : ValCompat (F := F) v) {x : Fˣ}
    (hint : (x : F) ∈ 𝒪[F]) :
    0 ≤ Multiplicative.toAdd (v x) := by
  by_cases hun : IsUnit (⟨(x : F), hint⟩ : ↥𝒪[F])
  · rw [toAdd_val_eq_zero_of_isUnit hv hint hun]
  · have hmem := (IsLocalRing.mem_maximalIdeal (⟨(x : F), hint⟩ : ↥𝒪[F])).mpr hun
    have hpos := (hv.mem_maximalIdeal x hint).mp hmem
    omega

/-! ## 2. `1 − a`／`a − 1` 作为 `Fˣ` 的元素（顶层 `def`，`LESSONS` B49） -/

/-- `1 − a` 作为 `Fˣ` 的元素（`a ≠ 1`）。 -/
noncomputable def oneSub (a : Fˣ) (ha : a ≠ 1) : Fˣ :=
  Units.mk0 ((1 : F) - (a : F)) (by
    rw [sub_ne_zero]
    intro h
    exact ha (Units.ext h.symm))

/-- `a − 1` 作为 `Fˣ` 的元素（`a ≠ 1`）。 -/
noncomputable def subOne (a : Fˣ) (ha : a ≠ 1) : Fˣ :=
  Units.mk0 ((a : F) - 1) (by
    rw [sub_ne_zero]
    intro h
    exact ha (Units.ext h))

@[simp] theorem oneSub_coe (a : Fˣ) (ha : a ≠ 1) :
    ((oneSub a ha : Fˣ) : F) = 1 - (a : F) := rfl

@[simp] theorem subOne_coe (a : Fˣ) (ha : a ≠ 1) :
    ((subOne a ha : Fˣ) : F) = (a : F) - 1 := rfl

theorem oneSub_eq_neg_subOne (a : Fˣ) (ha : a ≠ 1) :
    oneSub a ha = -(subOne a ha) := by
  refine Units.ext ?_
  rw [oneSub_coe, Units.val_neg, subOne_coe]
  ring

/-- `v(1−a) = v(a−1)`（差一个 `(−1)`，而 `v(−1) = 0`）。 -/
theorem toAdd_val_oneSub (a : Fˣ) (ha : a ≠ 1) :
    Multiplicative.toAdd (v (oneSub a ha))
      = Multiplicative.toAdd (v (subOne a ha)) := by
  rw [oneSub_eq_neg_subOne]
  have hneg : (-(subOne a ha) : Fˣ) = (-1) * subOne a ha := by rw [neg_one_mul]
  rw [hneg, map_mul, toAdd_mul', toAdd_val_neg_one, zero_add]

/-! ## 3. (K1) 的 `Fˣ` 形态：(K1) 原本只对 `𝒪[F]ˣ` 说；本件把它搬到 `Fˣ` 的元素上 -/

/-- ★★ **(K1) 的 `Fˣ` 形态**：`x ∈ 𝒪[F]` 且 `residue x = 1` ⟹ `κ(x) = 0`。 -/
theorem kummerClass_eq_zero_of_residue_eq_one_unit (hp : IsUnit (p : ↥𝒪[F]))
    (hpF : IsUnit (p : F)) {x : Fˣ} (hint : (x : F) ∈ 𝒪[F])
    (hres : IsLocalRing.residue ↥𝒪[F] (⟨(x : F), hint⟩ : ↥𝒪[F]) = 1) :
    KummerBridge.kummerClass F p hpF x = 0 := by
  have hne : (⟨(x : F), hint⟩ : ↥𝒪[F]) ∉ IsLocalRing.maximalIdeal ↥𝒪[F] := by
    intro hmem
    have h0 : IsLocalRing.residue ↥𝒪[F] (⟨(x : F), hint⟩ : ↥𝒪[F]) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hres] at h0
    exact one_ne_zero h0
  have hunit : IsUnit (⟨(x : F), hint⟩ : ↥𝒪[F]) :=
    isUnit_of_notMem_maximalIdeal _ hne
  obtain ⟨uu, huu⟩ := hunit
  have hres' : IsLocalRing.residue ↥𝒪[F] ((uu : ↥𝒪[F])) = 1 := by
    rw [huu]
    exact hres
  have h1 : KummerBridge.kummerClass F p hpF (unitBase uu) = 0 :=
    kummerClass_eq_zero_of_residue_eq_one (F := F) (p := p) hp hpF uu hres'
  have hxb : unitBase uu = x := by
    refine Units.ext ?_
    rw [unitBase_coe]
    show (((uu : ↥𝒪[F]) : ↥𝒪[F])) = (x : F)
    rw [huu]
  simpa only [hxb] using h1

/-! ## 4. 情形 1／4 的核心：`v a > 0 ⟹ κ(1−a) = 0` 且 `v(1−a) = 0` -/

/-- ★★★★ **主单位**：`v a > 0`（`a ∈ 𝔪`）⟹ `1 − a` 是主单位，
故 `κ(1−a) = 0`（(K1)）且 `v(1−a) = 0`。 -/
theorem kummerClass_oneSub_eq_zero_of_val_pos (hp : IsUnit (p : ↥𝒪[F]))
    (hpF : IsUnit (p : F)) (hv : ValCompat (F := F) v) {a : Fˣ} (ha : a ≠ 1)
    (hpos : 0 < Multiplicative.toAdd (v a)) :
    KummerBridge.kummerClass F p hpF (oneSub a ha) = 0 ∧
      Multiplicative.toAdd (v (oneSub a ha)) = 0 := by
  have hinta : (a : F) ∈ 𝒪[F] := hv.mem_integer a (by omega)
  have hmem : (⟨(a : F), hinta⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
    (hv.mem_maximalIdeal a hinta).mpr hpos
  have hint1 : ((1 : F) - (a : F)) ∈ 𝒪[F] :=
    Subring.sub_mem 𝒪[F] (Subring.one_mem 𝒪[F]) hinta
  have heq1 : (⟨(1 : F) - (a : F), hint1⟩ : ↥𝒪[F])
      = 1 - (⟨(a : F), hinta⟩ : ↥𝒪[F]) := by
    apply Subtype.ext
    show (1 : F) - (a : F) = (1 : F) - ((⟨(a : F), hinta⟩ : ↥𝒪[F]) : F)
    rfl
  have hne1 : (⟨(1 : F) - (a : F), hint1⟩ : ↥𝒪[F]) ∉ IsLocalRing.maximalIdeal ↥𝒪[F] := by
    intro hmem1
    rw [heq1] at hmem1
    have h2 := Ideal.add_mem (IsLocalRing.maximalIdeal ↥𝒪[F]) hmem1 hmem
    have h3 : (1 - (⟨(a : F), hinta⟩ : ↥𝒪[F])) + (⟨(a : F), hinta⟩ : ↥𝒪[F])
        = (1 : ↥𝒪[F]) := by abel
    rw [h3] at h2
    exact notMem_maximalIdeal_of_isUnit _ isUnit_one h2
  have hunit1 : IsUnit (⟨(1 : F) - (a : F), hint1⟩ : ↥𝒪[F]) :=
    isUnit_of_notMem_maximalIdeal _ hne1
  have hres1 : IsLocalRing.residue ↥𝒪[F] (⟨(1 : F) - (a : F), hint1⟩ : ↥𝒪[F]) = 1 := by
    rw [heq1, map_sub, map_one, (IsLocalRing.residue_eq_zero_iff _).mpr hmem, sub_zero]
  refine ⟨?_, ?_⟩
  · exact kummerClass_eq_zero_of_residue_eq_one_unit (F := F) (p := p) hp hpF hint1 hres1
  · exact toAdd_val_eq_zero_of_isUnit hv hint1 hunit1

/-! ## 5. 主定理：四情形 -/

/-- ★★★★★ **A3（Steinberg 关系，具体载体）**：`tame(a, 1−a) = 0`。

`κ := KummerBridge.kummerClass`、`v̄ := valLinOf v hpF`、`tame := Hyp680.tameExpr`。
四情形见文件头表；`p ≠ 2` 只在第四情形（(K2)）用到。 -/
-- @source file=raw/L20261018.tex locator=line:739 quote="其分次环由乘法群 $F^\times$ 的张量代数模去 Steinberg 关系"
theorem tameExpr_kummerClass_oneSub (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2) {a : Fˣ} (ha : a ≠ 1) :
    tameExpr (valLinOf (F := F) (p := p) v hpF)
      (KummerBridge.kummerClass F p hpF a)
      (KummerBridge.kummerClass F p hpF (oneSub a ha)) = 0 := by
  rw [tameExpr_eq_zero_iff]
  have hva : valLinOf (F := F) (p := p) v hpF (KummerBridge.kummerClass F p hpF a)
      = ((Multiplicative.toAdd (v a) : ℤ) : ZMod p) := by
    rw [valLinOf_kummerClass]
    rfl
  have hvo : valLinOf (F := F) (p := p) v hpF (KummerBridge.kummerClass F p hpF (oneSub a ha))
      = ((Multiplicative.toAdd (v (oneSub a ha)) : ℤ) : ZMod p) := by
    rw [valLinOf_kummerClass]
    rfl
  rw [hva, hvo]
  rcases lt_trichotomy (Multiplicative.toAdd (v a)) 0 with hneg | hzero | hpos
  · -- 情形 4：`v a < 0` ⟹ `a⁻¹ ∈ 𝔪`，`1 − a = −a(1 − a⁻¹)`
    have hainv_ne : a⁻¹ ≠ 1 := by
      intro h
      exact ha (by rw [← inv_inv a, h, inv_one])
    have hsum : Multiplicative.toAdd (v a) + Multiplicative.toAdd (v a⁻¹) = 0 := by
      rw [← toAdd_mul', map_inv, mul_inv_cancel]
      rfl
    have hpos' : 0 < Multiplicative.toAdd (v a⁻¹) := by omega
    obtain ⟨hκ', hval'⟩ :=
      kummerClass_oneSub_eq_zero_of_val_pos (F := F) (p := p) (v := v) hp hpF hv
        hainv_ne hpos'
    have hdec : oneSub a ha = -(a * oneSub a⁻¹ hainv_ne) := by
      refine Units.ext ?_
      rw [oneSub_coe, Units.val_neg, Units.val_mul, oneSub_coe, Units.val_inv_eq_inv_val]
      have ha0 : (a : F) ≠ 0 := a.ne_zero
      rw [mul_sub, mul_one, mul_inv_cancel₀ ha0]
      ring
    have hneg' : (-(a * oneSub a⁻¹ hainv_ne) : Fˣ) = (-1) * (a * oneSub a⁻¹ hainv_ne) := by
      rw [neg_one_mul]
    have hvo4 : Multiplicative.toAdd (v (oneSub a ha))
        = Multiplicative.toAdd (v a) := by
      have h1 : v (oneSub a ha) = v (-1) * (v a * v (oneSub a⁻¹ hainv_ne)) := by
        rw [hdec, hneg', map_mul v, map_mul v]
      rw [h1, toAdd_mul', toAdd_mul', toAdd_val_neg_one, hval']
      ring
    have hκ4 : KummerBridge.kummerClass F p hpF (oneSub a ha)
        = KummerBridge.kummerClass F p hpF a := by
      rw [hdec, hneg', KummerV.kummerClass_mul, KummerV.kummerClass_mul,
        kummerClass_neg_one (F := F) (p := p) hpF hp2, hκ']
      abel
    rw [hvo4, hκ4]
  · -- 情形 2／3：`v a = 0`，按 `v(a−1)` 的符号细分
    have hinta : (a : F) ∈ 𝒪[F] := hv.mem_integer a (by omega)
    have hint2 : ((a : F) - 1) ∈ 𝒪[F] :=
      Subring.sub_mem 𝒪[F] hinta (Subring.one_mem 𝒪[F])
    by_cases hsub : 0 < Multiplicative.toAdd (v (subOne a ha))
    · -- 情形 2：`a ≡ 1 (mod 𝔪)` ⟹ `κ(a) = 0`（(K1)）
      have hmem2 : (⟨(a : F) - 1, hint2⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
        (hv.mem_maximalIdeal (subOne a ha) hint2).mpr hsub
      have heq2 : (⟨(a : F), hinta⟩ : ↥𝒪[F]) = 1 + (⟨(a : F) - 1, hint2⟩ : ↥𝒪[F]) := by
        apply Subtype.ext
        show (a : F) = (1 : F) + ((a : F) - 1)
        ring
      have hres2 : IsLocalRing.residue ↥𝒪[F] (⟨(a : F), hinta⟩ : ↥𝒪[F]) = 1 := by
        rw [heq2, map_add, map_one, (IsLocalRing.residue_eq_zero_iff _).mpr hmem2, add_zero]
      have hκa : KummerBridge.kummerClass F p hpF a = 0 :=
        kummerClass_eq_zero_of_residue_eq_one_unit (F := F) (p := p) hp hpF hinta hres2
      rw [hzero, hκa]
      simp
    · -- 情形 3：`v a = 0` 且 `v(a−1) = 0`（皆单位）
      have hsub0 : Multiplicative.toAdd (v (subOne a ha)) = 0 := by
        have hnonneg := toAdd_val_nonneg_of_mem_integer (x := subOne a ha) hv hint2
        omega
      have hvo0 : Multiplicative.toAdd (v (oneSub a ha)) = 0 := by
        rw [toAdd_val_oneSub, hsub0]
      rw [hzero, hvo0]
      simp
  · -- 情形 1：`v a > 0` ⟹ `1 − a` 是主单位
    obtain ⟨hκ, hval⟩ :=
      kummerClass_oneSub_eq_zero_of_val_pos (F := F) (p := p) (v := v) hp hpF hv ha hpos
    rw [hκ, hval]
    simp

/-! ## 6. 两条**推论**（把 `tameExpr` 的 `Subtype` 去掉，供 `ker ∪ ⊆ ker tame` 直接用） -/

/-- A3 的**零化形态**：`tame(a,1−a)` 在 `V` 里就是 `0`。 -/
theorem tameExpr_kummerClass_oneSub_coe (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2) {a : Fˣ} (ha : a ≠ 1) :
    valLinOf (F := F) (p := p) v hpF (KummerBridge.kummerClass F p hpF (oneSub a ha))
        • KummerBridge.kummerClass F p hpF a
      = valLinOf (F := F) (p := p) v hpF (KummerBridge.kummerClass F p hpF a)
        • KummerBridge.kummerClass F p hpF (oneSub a ha) :=
  (tameExpr_eq_zero_iff (valLinOf (F := F) (p := p) v hpF)
    (KummerBridge.kummerClass F p hpF a)
    (KummerBridge.kummerClass F p hpF (oneSub a ha))).mp
    (tameExpr_kummerClass_oneSub (F := F) (p := p) (v := v) hp hpF hv hp2 ha)

/-- 对称形态：`tame(1−a, a) = 0`（由 `tameExpr_skew`）。 -/
theorem tameExpr_kummerClass_subOne (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2) {a : Fˣ} (ha : a ≠ 1) :
    tameExpr (valLinOf (F := F) (p := p) v hpF)
      (KummerBridge.kummerClass F p hpF (oneSub a ha))
      (KummerBridge.kummerClass F p hpF a) = 0 := by
  rw [tameExpr_skew, tameExpr_kummerClass_oneSub (F := F) (p := p) (v := v) hp hpF hv hp2 ha]
  simp

end TameSteinberg

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.toAdd_val_neg_one
#print axioms L20261018.not_pos_val_of_isUnit
#print axioms L20261018.not_neg_val_of_mem_integer
#print axioms L20261018.toAdd_val_eq_zero_of_isUnit
#print axioms L20261018.toAdd_val_nonneg_of_mem_integer
#print axioms L20261018.toAdd_val_oneSub
#print axioms L20261018.kummerClass_eq_zero_of_residue_eq_one_unit
#print axioms L20261018.kummerClass_oneSub_eq_zero_of_val_pos
#print axioms L20261018.tameExpr_kummerClass_oneSub
#print axioms L20261018.tameExpr_kummerClass_oneSub_coe
#print axioms L20261018.tameExpr_kummerClass_subOne
