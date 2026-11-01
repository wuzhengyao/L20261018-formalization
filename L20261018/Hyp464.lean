import L20261018.Hyp463

/-!
# S40 R3：`G = Gal(K_s/K)` 在 `K_s((π))` 上的**系数作用**（G2 的最后一块模层）

## ⚠ 载体更正

本文件（与 `Hyp463`／`Hyp465`）的载体是 `K_s((π))`，它是 GS 的 `K_nr` 的**真超集**、
且其上 `ContinuousSMul` **不成立** ⟹ `Hyp386` 不能喂。详见 `Hyp463` 文件头的「载体更正」块
与 `RECON-R3` §82。

## 本轮在补什么

`Hyp463` 已把 GS (6.1) 的**模层**无条件机检出来（`v_{K_nr}`／正合／分裂 `1 ↦ π`），
载体是 `K_nr = K_s((π)) = LaurentSeries (SeparableClosure K)`（`F = K((π))` 的情形）。
要把 `S : DiscreteShortExact G U_nr (Additive K_nr^×) (ULift ℤ)` 装出来喂 `Hyp386.residueMap`，
还缺 **`G = Gal(K_s/K)` 的作用**。GS 的作用是**系数作用**（`π` 不动）：
`σ • Σ a_n π^n = Σ (σ a_n) π^n`。

## 上一轮登记为"卡"的那一步，其实件都在

mathlib **没有** `LaurentSeries.map`，只有 `HahnSeries.map`（`Basic.lean:142`）。
但 `HahnSeries` 的乘法性**是有的**，分散在三处：

| 引理 | 位置 | 假设 |
|---|---|---|
| `HahnSeries.map_zero` | `Basic.lean:147` | `ZeroHom` |
| `HahnSeries.map_add` | `Addition.lean:124` | `R →+ S` |
| `HahnSeries.map_one` | `Multiplication.lean:103` | `R →*₀ S` |
| `HahnSeries.map_mul` | `Multiplication.lean:406` | `R →ₙ+* S` |

而 `LaurentSeries R` **按定义**就是 `R⟦ℤ⟧`（`LaurentSeries.lean:101` 的 `abbrev`）
⟹ 上面的引理直接可用，**不需要**支撑条件（`map` 不改支撑集，`Γ = ℤ` 已是
`IsOrderedCancelAddMonoid`）。

⚠ **工艺**：这些引理的 `f` 各自在不同 coercion 位置（`→+`／`→*₀`／`→ₙ+*`），
而 `HahnSeries.map` 的隐式参数 `F` 由 `f` 的类型决定 ⟹ 直接 `exact` 会**类型不匹配**。
可靠写法是 `convert … using 2 <;> rfl`（本轮实测；`simpa`／`exact` 都不过）。

## 本轮机检

| 声明 | 内容 |
|---|---|
| `knrMap` | ★★★★ **系数作用** `K_s((π)) →+* K_s((π))` |
| `knrMap_coeff`／`knrMap_id`／`knrMap_mul` | 逐系数作用；`knrMap 1 = id`；`knrMap (στ) = knrMap σ ∘ knrMap τ` |
| `knrUnitsMulAction` | ★★★★ `G` 在 `K_nr^×` 上的 `MulAction` |
| **`knrVal_map_eq`** | ★★★★ 系数作用不改 `Valued.v` |
| **`knrVal_smul`** | ★★★★ **`v` 是 `G`-不变的** ⟹ `U_nr` 是 `G`-子模 |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-- ★★★★ **系数作用**：`σ ∈ Gal(K_s/K)` 逐系数作用在 `K_s((π))` 上（`π` 不动）。 -/
noncomputable def knrMap (σ : TauCeti.AbsoluteGaloisGroup K) :
    LaurentSeries (SeparableClosure K) →+* LaurentSeries (SeparableClosure K) where
  toFun x := HahnSeries.map x (σ.toRingEquiv.toRingHom)
  map_zero' := by
    ext n
    rw [HahnSeries.map_coeff]
    simp
  map_one' := by
    convert HahnSeries.map_one (f := (σ.toRingEquiv.toRingHom : SeparableClosure K →*₀
      SeparableClosure K)) using 2
    all_goals (ext n; rfl)
  map_add' x y := by
    convert HahnSeries.map_add (f := (σ.toRingEquiv.toRingHom : SeparableClosure K →+
      SeparableClosure K)) (x := x) (y := y) using 2
    all_goals (ext n; rfl)
  map_mul' x y := by
    convert HahnSeries.map_mul (f := (σ.toRingEquiv.toRingHom : SeparableClosure K →ₙ+*
      SeparableClosure K)) (x := x) (y := y) using 2
    all_goals (ext n; rfl)

theorem knrMap_apply (σ : TauCeti.AbsoluteGaloisGroup K)
    (x : LaurentSeries (SeparableClosure K)) :
    knrMap σ x = HahnSeries.map x (σ.toRingEquiv.toRingHom) := rfl

theorem knrMap_coeff (σ : TauCeti.AbsoluteGaloisGroup K)
    (x : LaurentSeries (SeparableClosure K)) (n : ℤ) :
    (knrMap σ x).coeff n = σ (x.coeff n) :=
  HahnSeries.map_coeff x σ.toRingEquiv.toRingHom n

/-- `knrMap 1 = id`。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8156 quote="G:=\operatorname{Gal}(K_{nr}|K)$ is canonically isomorphic to"
theorem knrMap_id : knrMap (1 : TauCeti.AbsoluteGaloisGroup K) =
    RingHom.id (LaurentSeries (SeparableClosure K)) := by
  ext x n
  rw [knrMap_coeff, RingHom.id_apply]
  rfl

/-- `knrMap (σ * τ) = knrMap σ ∘ knrMap τ`。 -/
theorem knrMap_mul (σ τ : TauCeti.AbsoluteGaloisGroup K) :
    knrMap (σ * τ) = (knrMap σ).comp (knrMap τ) := by
  ext x n
  rw [knrMap_coeff, RingHom.comp_apply, knrMap_coeff, knrMap_coeff]
  rfl

/-! ## 2. `G` 在 `K_nr^×` 上的作用 -/

/-- ★★★★ **`G` 在 `K_nr^×` 上的 `MulAction`**（系数作用）。 -/
noncomputable instance knrUnitsMulAction :
    MulAction (TauCeti.AbsoluteGaloisGroup K) (LaurentSeries (SeparableClosure K))ˣ where
  smul σ u := Units.map (knrMap σ).toMonoidHom u
  one_smul u := by
    show Units.map (knrMap 1).toMonoidHom u = u
    rw [knrMap_id]
    rfl
  mul_smul σ τ u := by
    show Units.map (knrMap (σ * τ)).toMonoidHom u
      = Units.map (knrMap σ).toMonoidHom (Units.map (knrMap τ).toMonoidHom u)
    rw [knrMap_mul]
    ext
    rfl

/-! ## 3. ★ `v` 是 `G`-不变的 ⟹ `U_nr` 是 `G`-子模 -/

/-- 系数作用不改 `Valued.v`：`v` 由「系数在 `n < D` 处是否全为零」逐层确定
（`LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`），而 `σ` 单射且逐系数作用，
故两个判据等价；再用 `WithZero.exp_log` 把 `≤` 的层级判据拼回等号。 -/
theorem knrVal_map_eq (σ : TauCeti.AbsoluteGaloisGroup K)
    {x : LaurentSeries (SeparableClosure K)} (hx : x ≠ 0) :
    (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom) : ZMod0) = Valued.v x := by
  have hkey : ∀ D : ℤ,
      (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom) : ZMod0) ≤ WithZero.exp (-D) ↔
        (Valued.v x : ZMod0) ≤ WithZero.exp (-D) := by
    intro D
    rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero,
      LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
    constructor
    · intro h n hn
      have h2 := h n hn
      rw [HahnSeries.map_coeff] at h2
      exact σ.toRingEquiv.injective (by simpa using h2)
    · intro h n hn
      rw [HahnSeries.map_coeff, h n hn, map_zero]
  have hx' : (Valued.v x : ZMod0) ≠ 0 := by
    intro h
    exact hx ((Valuation.zero_iff (Valued.v : Valuation (LaurentSeries (SeparableClosure K))
      ZMod0)).mp h)
  have hmap0 : HahnSeries.map x σ.toRingEquiv.toRingHom ≠ 0 := by
    intro h
    apply hx
    ext n
    have h1 := congrArg (fun z : LaurentSeries (SeparableClosure K) => z.coeff n) h
    simp only [HahnSeries.map_coeff, HahnSeries.coeff_zero] at h1
    have h3 : x.coeff n = 0 := σ.toRingEquiv.injective (by simpa using h1)
    simpa using h3
  have hmap' : (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom) : ZMod0) ≠ 0 := by
    intro h
    exact hmap0 ((Valuation.zero_iff (Valued.v : Valuation (LaurentSeries (SeparableClosure K))
      ZMod0)).mp h)
  set Dx : ℤ := -(WithZero.log (Valued.v x)) with hDx
  have hxlog : (Valued.v x : ZMod0) = WithZero.exp (-Dx) := by
    rw [hDx, neg_neg]
    conv_lhs => rw [← WithZero.exp_log hx']
  set Dm : ℤ := -(WithZero.log
    (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom))) with hDm
  have hmlog : (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom) : ZMod0) =
      WithZero.exp (-Dm) := by
    rw [hDm, neg_neg]
    conv_lhs => rw [← WithZero.exp_log hmap']
  have h1 : (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom) : ZMod0) ≤
      WithZero.exp (-Dx) := (hkey Dx).mpr (le_of_eq hxlog)
  have h2 : (Valued.v x : ZMod0) ≤ WithZero.exp (-Dm) := (hkey Dm).mp (le_of_eq hmlog)
  refine le_antisymm ?_ ?_
  · calc (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom) : ZMod0)
        ≤ WithZero.exp (-Dx) := h1
      _ = (Valued.v x : ZMod0) := hxlog.symm
  · calc (Valued.v x : ZMod0)
        ≤ WithZero.exp (-Dm) := h2
      _ = (Valued.v (HahnSeries.map x σ.toRingEquiv.toRingHom) : ZMod0) := hmlog.symm

/-- ★★★★ **`v` 是 `G`-不变的**：`v (σ • u) = v u`（GS (6.1) 是 `G`-模的正合列）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8160 quote="Denoting by $U_{nr}$ the multiplicative group of units in $K_{nr}$, we get an"
theorem knrVal_smul (σ : TauCeti.AbsoluteGaloisGroup K)
    (u : (LaurentSeries (SeparableClosure K))ˣ) :
    knrVal K (σ • u) = knrVal K u := by
  apply WithZero.coe_injective
  simp only [knrVal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    WithZero.coe_unitsWithZeroEquiv_eq_units_val, Units.coe_map]
  show (Valued.v : Valuation (LaurentSeries (SeparableClosure K)) ZMod0)
    (((σ • u : (LaurentSeries (SeparableClosure K))ˣ) : LaurentSeries (SeparableClosure K)))
    = (Valued.v : Valuation (LaurentSeries (SeparableClosure K)) ZMod0)
      ((u : (LaurentSeries (SeparableClosure K))ˣ) : LaurentSeries (SeparableClosure K))
  rw [show (((σ • u : (LaurentSeries (SeparableClosure K))ˣ) :
      LaurentSeries (SeparableClosure K)))
      = HahnSeries.map ((u : (LaurentSeries (SeparableClosure K))ˣ) :
        LaurentSeries (SeparableClosure K)) σ.toRingEquiv.toRingHom from rfl]
  exact knrVal_map_eq (K := K) σ (Units.ne_zero u)

end L20261018

#print axioms L20261018.knrMap_id
#print axioms L20261018.knrMap_mul
#print axioms L20261018.knrVal_map_eq
#print axioms L20261018.knrVal_smul
