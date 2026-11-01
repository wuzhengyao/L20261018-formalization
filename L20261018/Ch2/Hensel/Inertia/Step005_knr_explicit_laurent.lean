import L20261018.Ch2.Hensel.ResidueMap.Step043_units_mod_pth_powers_paper_level

/-!
# S40 R2：`F = K((π))` 的**显式 `K_nr` ＝ `K_s((π))`** —— GS (6.1) 的赋值层（G2 的第一块砖）


## ⚠⚠ 载体更正（S40 R4，**推翻本文件 R2 的识别**）

R2 曾写「`F = K((π))` 时 `K_nr = K_s((π)) = LaurentSeries (SeparableClosure K)`」。**该识别是错的。**

* GS 的 `K_nr` = **有限**不分歧扩张之并。`F = K((π))` 时有限不分歧 `L/F` 恰为 `L = K'((π))`
  （`K'/K` 有限可分），故
  ```
  K_nr = ⋃_{K'/K 有限可分} K'((π))   ⊊   K_s((π))
  ```
* **严格包含的理由**：`⋃ K'((π))` 里每个元素都落在**某个** `K'((π))`（`K'` 有限）；
  而 `K_s((π))` 含 `Σ a_n π^n`（`a_n ∈ K_s` 且 `[K(a_0,…,a_n):K] → ∞`），
  它不在任何 `K'((π))` 里。更强：`K_s((π))/K((π))` **不是代数扩张**（上述元素是超越的），
  故它连「不分歧**代数**扩张」都不是，**不能**是 `K_nr`。两者残域都是 `K_s`，这是混淆的来源。

**两条后果**：

1. `Hyp463`／`Hyp464`／`Hyp465` 的陈述是关于 **`K_s((π))`**（`K_nr` 的**真超集**）的
   ⟹ 它们**不是** GS (6.1) 在 `K_nr` 上的形式化。数学内容仍成立，但**载体标错**。
2. ★ **`ContinuousSMul` 在 `K_s((π))^×` 上不成立**（`Hyp386.residueMap` 正好要它）：
   `G` 在离散模上的作用连续 ⟺ 每个元素的开稳定子。`u = Σ a_n π^n`（系数度数无界）的稳定子是
   `⋂_n Stab(a_n)` —— 开子群的**无限交**，一般不开。
   而在**正确的** `K_nr = ⋃ K'((π))` 上它**成立**（每个元素落在某个 `K'((π))`，
   故稳定子 ⊇ `Gal(K_s/K')`，开）。

⟹ **`Hyp386` 只能喂在 `K_nr`（并）上，不能喂在 `K_s((π))` 上。**
   下一轮须把载体改成 `⋃_{K'} K'((π))`（`LaurentSeries (SepCl K)` 的一个 `IntermediateField` 式的并），
   `v` 与 `G`-作用由限制得到 —— 本轮已机检的 `v`／作用／正合／分裂**逐条可移植**。

## 0. 为什么换载体（R2 的口径更正，**其识别见上方更正**）

`PROMPT-S40` §③.2 与 `GS68-LEDGER` §A 都假设 `K_nr` 可由 TauCeti 的
`TauCeti.maximalUnramifiedExtension` 取到（`Hyp380.KnrLoc`）。**本轮实测：不可用于论文情形。**

```lean
#check @TauCeti.maximalUnramifiedExtension
-- maximalUnramifiedExtension : (K) → [Field K] → [ValuativeRel K] → [TopologicalSpace K]
--   → [IsNonarchimedeanLocalField K] → (Ω) → [Field Ω] → [Algebra K Ω] → IntermediateField K Ω
```

TauCeti 的定义用 `Nat.card 𝓀[K]`（`maximalUnramifiedExtension_eq_adjoin`：
`X ^ Nat.card 𝓀[K] ^ f - X` 的根），**只对有限剩余域有意义**。
`IsNonarchimedeanLocalField`（局部紧）⟹ 有限剩余域。

而论文的主例 `ex:explicit-ramified`（`raw/L20261018.tex:2784`）是
`L = ℂ(t)`、`K = L((x₁))`、`F = K((x₂))` —— **无限剩余域**。
⟹ `Hyp380` 的 A1–A6 虽在 `[IsNonarchimedeanLocalField F]` 下零假设机检，
但**对论文情形不可用**；`GS68-LEDGER` §A 的「在论文设定下零假设」一句须更正为
「**在局部域设定下零假设**」。

## 1. 本轮换的载体：`F = K((π))` ⟹ `K_nr = K_s((π))` 是**显式**的

GS 要求 `K_nr` = 「有限不分歧扩张之并」。当 `F = K((π))` 时，有限不分歧 `L/F`
恰好是 `L = K'((π))`（`K'/K` 有限可分），故

```
K_nr = K_s((π)) = LaurentSeries (SeparableClosure K),      Gal(K_nr/F) = Gal(K_s/K)
```

**⟹ 不需要 `unramifiedExtension` 的任何机器**：`K_s((π))` 直接是 `LaurentSeries`，
而 mathlib **已有** `LaurentSeries K` 的 `Valued` 实例（值群 `WithZero (Multiplicative ℤ)`）：

```lean
LaurentSeries.valued : (K) → [Field K] → Valued (LaurentSeries K) (WithZero (Multiplicative ℤ))
LaurentSeries.valuation_single_zpow : Valued.v (single s 1) = exp (-(s : ℤ))
```

⟹ `v_{K_nr}` ＝ `π`-adic 赋值，**显式可得**；`U_nr := ker v`。

## 2. 本轮机检

| 声明 | 内容 |
|---|---|
| `knrVal` | ★★★★ `v_{K_nr} : (K_s((π)))ˣ →* Multiplicative ℤ` |
| `knrVal_single` | `v (single s 1) = ofAdd (-s)` |
| `knrVal_pi` | ★★★★ `v π = ofAdd 1`（`π := single (-1) 1`，即 `X⁻¹`；mathlib 的约定是 `v X = exp(-1)`） |
| `knrProj` | `K_nr^× →+ ULift ℤ`（加性形态） |
| `knrProj_surjective` | ★★★★ 满射（`n ↦ π^n`） |
| `knrIncl` | `U_nr →+ K_nr^×`（`U_nr := ker v`） |
| `knrIncl_injective`／`knrProj_exact` | ★★★★ GS (6.1) 的正合性 |
| `knrSplit` | ★★★★ **分裂**：`knrProj (π^n) = n`（`1 ↦ π`） |

**残余（下一步，已精确定位）**：`G := AbsoluteGaloisGroup K` 在 `K_s((π))` 上的
系数作用，使其成为 `DistribMulAction` ⟹ 才可装成 `DiscreteShortExact` 喂 `Hyp386.residueMap`。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

/-- `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` 是 mathlib 给 `LaurentSeries` 的值群。 -/
abbrev ZMod0 := WithZero (Multiplicative ℤ)

/-- `single s 1` 作为 `K_s((π))` 的单位（`= X^s`）。 -/
noncomputable def knrUnit (K : Type) [Field K] (s : ℤ) :
    (LaurentSeries (SeparableClosure K))ˣ :=
  Units.mk0 (HahnSeries.single s (1 : SeparableClosure K))
    (HahnSeries.single_ne_zero (by norm_num))

/-- ★★★★ **`K_s((π))` 上的 `π`-adic 赋值**（取单位群，故值在 `Multiplicative ℤ`）。

`K_s((π))` 即 `F = K((π))` 的 `K_nr`（见文件头的说明）。 -/
noncomputable def knrVal (K : Type) [Field K] :
    (LaurentSeries (SeparableClosure K))ˣ →* Multiplicative ℤ :=
  (WithZero.unitsWithZeroEquiv).toMonoidHom.comp
    (Units.map (Valuation.toMonoidWithZeroHom
      (Valued.v : Valuation (LaurentSeries (SeparableClosure K)) ZMod0)).toMonoidHom)

variable {K : Type} [Field K]

theorem knrUnit_coe (s : ℤ) :
    ((knrUnit K s : (LaurentSeries (SeparableClosure K))ˣ) : LaurentSeries (SeparableClosure K))
      = HahnSeries.single s (1 : SeparableClosure K) := rfl

/-- `v (single s 1) = -s`（mathlib 的约定：`valued` 给 `v X = exp (-1)`）。 -/
theorem knrVal_single (s : ℤ) :
    knrVal K (knrUnit K s) = Multiplicative.ofAdd (-s) := by
  apply WithZero.coe_injective
  rw [knrVal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    WithZero.coe_unitsWithZeroEquiv_eq_units_val, Units.coe_map]
  show (Valued.v : Valuation (LaurentSeries (SeparableClosure K)) ZMod0)
      (((knrUnit K s : (LaurentSeries (SeparableClosure K))ˣ) : LaurentSeries (SeparableClosure K)))
      = ↑(Multiplicative.ofAdd (-s))
  rw [knrUnit_coe, LaurentSeries.valuation_single_zpow]
  rfl

/-- ★★★★ **一致化元**：`π := single (-1) 1`（即 `X⁻¹`）。`v π = 1`。 -/
noncomputable def knrPi (K : Type) [Field K] : (LaurentSeries (SeparableClosure K))ˣ :=
  knrUnit K (-1)

theorem knrVal_pi : knrVal K (knrPi K) = Multiplicative.ofAdd 1 := by
  rw [knrPi, knrVal_single]
  norm_num


/-! ## 3. GS (6.1)：`1 → U_nr → K_nr^× →^v ℤ → 0` 正合 ＋ 分裂 -/

/-- `K_nr^×` 的加性形态（`Additive`），供 `DiscShortExact` 一层使用。 -/
abbrev KnrUnits (K : Type) [Field K] := Additive (LaurentSeries (SeparableClosure K))ˣ

/-- `v : K_nr^× →+ ℤ`（加性形态）。 -/
noncomputable def knrProj (K : Type) [Field K] : KnrUnits K →+ ULift ℤ where
  toFun x := ULift.up (Multiplicative.toAdd (knrVal K (Additive.toMul x)))
  map_zero' := by
    show ULift.up (Multiplicative.toAdd (knrVal K (Additive.toMul (0 : KnrUnits K)))) = ULift.up (0 : ℤ)
    rw [show Additive.toMul (0 : KnrUnits K) = 1 from rfl, map_one]
    rfl
  map_add' a b := by
    show ULift.up (Multiplicative.toAdd (knrVal K (Additive.toMul (a + b))))
      = ULift.up (Multiplicative.toAdd (knrVal K (Additive.toMul a)))
        + ULift.up (Multiplicative.toAdd (knrVal K (Additive.toMul b)))
    rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl, map_mul]
    rfl

/-- `U_nr := ker v` 到 `K_nr^×` 的包含。 -/
noncomputable def knrIncl (K : Type) [Field K] :
    Additive ↥(knrVal K).ker →+ KnrUnits K where
  toFun y := Additive.ofMul ((((Additive.toMul y : ↥(knrVal K).ker)) :
    (LaurentSeries (SeparableClosure K))ˣ))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem knrIncl_injective (K : Type) [Field K] : Function.Injective (knrIncl K) := by
  intro a b h
  have h' : ((Additive.toMul a : ↥(knrVal K).ker) :
      (LaurentSeries (SeparableClosure K))ˣ) = ((Additive.toMul b : ↥(knrVal K).ker) :
        (LaurentSeries (SeparableClosure K))ˣ) := h
  exact Additive.toMul.injective (Subtype.ext h')

/-- ★★★★ **GS (6.1) 的正合性**：`ker v = im(U_nr → K_nr^×)`。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8162 quote="1\to U_{nr}\to K_{nr}^{\times}\xrightarrow{v}\mathbf{Z}\to0"
theorem knrProj_exact (K : Type) [Field K] :
    Function.Exact (knrIncl K) (knrProj K) := by
  intro y
  constructor
  · intro hy
    have hval : knrVal K (Additive.toMul y) = 1 := by
      have : Multiplicative.toAdd (knrVal K (Additive.toMul y)) = 0 := by
        have := congrArg ULift.down hy
        simpa [knrProj] using this
      exact Multiplicative.toAdd.injective (by simpa using this)
    refine ⟨Additive.ofMul ⟨Additive.toMul y, ?_⟩, rfl⟩
    show knrVal K (Additive.toMul y) = 1
    exact hval
  · rintro ⟨x, rfl⟩
    simp only [knrProj]
    show ULift.up (Multiplicative.toAdd (knrVal K (Additive.toMul (knrIncl K x)))) = ULift.up (0 : ℤ)
    have hx : Additive.toMul (knrIncl K x) = ((Additive.toMul x : ↥(knrVal K).ker) :
        (LaurentSeries (SeparableClosure K))ˣ) := rfl
    rw [hx]
    exact congrArg (fun z => ULift.up (Multiplicative.toAdd z)) (Additive.toMul x).2

/-- ★★★★ **GS (6.1) 的右端满射**（`1 ↦ π` 的分裂给出）。 -/
theorem knrProj_surjective (K : Type) [Field K] : Function.Surjective (knrProj K) := by
  intro n
  refine ⟨Additive.ofMul (knrUnit K (-(ULift.down n))), ?_⟩
  simp only [knrProj]
  show ULift.up (Multiplicative.toAdd (knrVal K (knrUnit K (-(ULift.down n))))) = n
  rw [knrVal_single]
  simp

/-- ★★★★ **分裂**：截面 `n ↦ π^n`，即 `1 ↦ π`（GS 的「split by `1 ↦ π`」）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8165 quote="which is split by the map $\mathbf{Z}\to K_{nr}^{\times}$ sending $1$ to a local"
theorem knrProj_split :
    knrProj K (Additive.ofMul (knrPi K)) = ULift.up 1 := by
  simp only [knrProj]
  show ULift.up (Multiplicative.toAdd (knrVal K (knrPi K))) = ULift.up (1 : ℤ)
  rw [knrVal_pi]
  rfl

end L20261018

#print axioms L20261018.knrVal_single
#print axioms L20261018.knrVal_pi
#print axioms L20261018.knrIncl_injective
#print axioms L20261018.knrProj_exact
#print axioms L20261018.knrProj_surjective
#print axioms L20261018.knrProj_split
