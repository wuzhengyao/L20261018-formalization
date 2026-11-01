import L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier

/-!
# S40 R6：把 GS (6.1) 搬到**正确的** `K_nr` 载体（`Hyp466.KnrSubfield`）上

## 本轮做什么

R5 建成了正确的载体

```lean
KnrSubfield (K) : Subfield (LaurentSeries (SeparableClosure K))   -- = ⋃_{K' 有限} K'((π))
mem_KnrSubfield : x ∈ KnrSubfield K ↔ ∃ K' : FinInt K, x ∈ (coeffIncl K'.1).fieldRange
```

本轮把 `Hyp463` 的模层（`v`／`U_nr`／正合／分裂）**搬到它上面**。手段全是复合：
`Knr^× ↪ K_s((π))^× --v--> ℤ`。

## 本轮机检

| 声明 | 内容 |
|---|---|
| `knrUnit_mem` | `single s 1 ∈ K_nr`（系数在 `K` 里 ⟹ 在 `K((π))` 里） |
| `knrUnitOn` | `single s 1` 作为 `K_nr^×` 的元素 |
| `knrUnitIncl`／`knrUnitIncl_unit` | `K_nr^× →* K_s((π))^×`；`knrUnitOn s ↦ knrUnit s` |
| **`knrValOn`** | ★★★★ `v_{K_nr} : K_nr^× →* Multiplicative ℤ` |
| **`knrPiOn`**／**`knrValOn_pi`** | 一致化元 `π ∈ K_nr^×`；`v π = 1` |
| `KnrUnits'`／`knrProjOn` | `v : K_nr^× →+ ULift ℤ` |
| **`knrProjOn_exact`** | ★★★★ **GS (6.1) 正合** |
| **`knrProjOn_surjective`** | ★★★★ 满射 |
| **`knrProjOn_split`** | ★★★★ **分裂 `1 ↦ π`** |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-! ## 1. `single s 1` 落在 `K_nr` 里 -/

/-- `single s 1`（`= X^s`）在 `K_nr` 里：系数在 `K` 里 ⟹ 在 `K((π))` 里。 -/
theorem knrUnit_mem (s : ℤ) :
    (HahnSeries.single s (1 : SeparableClosure K) : LaurentSeries (SeparableClosure K)) ∈
      KnrSubfield K := by
  rw [mem_KnrSubfield]
  refine ⟨⟨⊥, inferInstance⟩, ⟨HahnSeries.single s (1 : ↥(⊥ : IntermediateField K
    (SeparableClosure K))), ?_⟩⟩
  show HahnSeries.map (HahnSeries.single s (1 : ↥(⊥ : IntermediateField K
    (SeparableClosure K)))) (algebraMap ↥(⊥ : IntermediateField K (SeparableClosure K))
      (SeparableClosure K)) = HahnSeries.single s (1 : SeparableClosure K)
  ext n
  rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  rcases eq_or_ne n s with h | h
  · subst h; simp
  · simp [h]

/-- `single s 1` 作为 `K_nr^×` 的元素。 -/
noncomputable def knrUnitOn (K : Type) [Field K] (s : ℤ) : (↥(KnrSubfield K))ˣ :=
  Units.mk0 ⟨HahnSeries.single s (1 : SeparableClosure K), knrUnit_mem (K := K) s⟩
    (by
      intro h
      have h' : (HahnSeries.single s (1 : SeparableClosure K) :
        LaurentSeries (SeparableClosure K)) = 0 := congrArg Subtype.val h
      exact HahnSeries.single_ne_zero (by norm_num) h')

theorem knrUnitOn_coe (s : ℤ) :
    ((knrUnitOn (K := K) s : (↥(KnrSubfield K))ˣ) : ↥(KnrSubfield K)) =
      ⟨HahnSeries.single s (1 : SeparableClosure K), knrUnit_mem (K := K) s⟩ := rfl

/-! ## 2. `K_nr^× →* K_s((π))^×` 与 `v_{K_nr}` -/

/-- `K_nr^× →* K_s((π))^×`（`Subfield.subtype` 在单位群上）。 -/
noncomputable def knrUnitIncl (K : Type) [Field K] :
    (↥(KnrSubfield K))ˣ →* (LaurentSeries (SeparableClosure K))ˣ :=
  Units.map (Subfield.subtype (KnrSubfield K)).toMonoidHom

theorem knrUnitIncl_unit (s : ℤ) :
    knrUnitIncl K (knrUnitOn (K := K) s) = knrUnit K s := by
  apply Units.ext
  show (Subfield.subtype (KnrSubfield K)) ((knrUnitOn (K := K) s : (↥(KnrSubfield K))ˣ) :
    ↥(KnrSubfield K)) = (HahnSeries.single s (1 : SeparableClosure K) :
      LaurentSeries (SeparableClosure K))
  rw [knrUnitOn_coe]
  rfl

/-- ★★★★ **`K_nr` 上的 `π`-adic 赋值**：`K_nr^× ↪ K_s((π))^×` 再复合 `knrVal`。 -/
noncomputable def knrValOn (K : Type) [Field K] :
    (↥(KnrSubfield K))ˣ →* Multiplicative ℤ :=
  (knrVal K).comp (knrUnitIncl K)

theorem knrValOn_apply (u : (↥(KnrSubfield K))ˣ) :
    knrValOn K u = knrVal K (knrUnitIncl K u) := rfl

theorem knrValOn_unit (s : ℤ) :
    knrValOn K (knrUnitOn (K := K) s) = Multiplicative.ofAdd (-s) := by
  rw [knrValOn_apply, knrUnitIncl_unit, knrVal_single]

/-- ★★★★ **一致化元**（在 `K_nr` 上）：`π := single (-1) 1`。 -/
noncomputable def knrPiOn (K : Type) [Field K] : (↥(KnrSubfield K))ˣ :=
  knrUnitOn K (-1)

/-- ★★★★ **`v π = 1`**（在 `K_nr` 上）。 -/
theorem knrValOn_pi : knrValOn K (knrPiOn K) = Multiplicative.ofAdd 1 := by
  rw [knrPiOn, knrValOn_unit]
  norm_num

/-! ## 3. GS (6.1) 在 `K_nr` 上：`v : K_nr^× →+ ℤ`、`U_nr`、正合、分裂 -/

/-- `K_nr^×` 的加性形态。 -/
abbrev KnrUnits' (K : Type) [Field K] := Additive (↥(KnrSubfield K))ˣ

/-- `v : K_nr^× →+ ULift ℤ`（加性形态）。 -/
noncomputable def knrProjOn (K : Type) [Field K] : KnrUnits' K →+ ULift ℤ where
  toFun x := ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul x)))
  map_zero' := by
    show ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul (0 : KnrUnits' K))))
      = ULift.up (0 : ℤ)
    rw [show Additive.toMul (0 : KnrUnits' K) = 1 from rfl, map_one]
    rfl
  map_add' a b := by
    show ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul (a + b))))
      = ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul a)))
        + ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul b)))
    rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl, map_mul]
    rfl

/-- `U_nr := ker v` 到 `K_nr^×` 的包含。 -/
noncomputable def knrInclOn (K : Type) [Field K] :
    Additive ↥(knrValOn K).ker →+ KnrUnits' K where
  toFun y := Additive.ofMul (((Additive.toMul y : ↥(knrValOn K).ker) :
    (↥(KnrSubfield K))ˣ))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem knrInclOn_injective (K : Type) [Field K] : Function.Injective (knrInclOn K) := by
  intro a b h
  have h' : ((Additive.toMul a : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ)
      = ((Additive.toMul b : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ) := h
  exact Additive.toMul.injective (Subtype.ext h')

/-- ★★★★ **GS (6.1) 的正合性**（在 `K_nr` 上）：`ker v = im(U_nr → K_nr^×)`。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8162 quote="1\to U_{nr}\to K_{nr}^{\times}\xrightarrow{v}\mathbf{Z}\to0"
theorem knrProjOn_exact (K : Type) [Field K] :
    Function.Exact (knrInclOn K) (knrProjOn K) := by
  intro y
  constructor
  · intro hy
    have hval : knrValOn K (Additive.toMul y) = 1 := by
      have h0 : Multiplicative.toAdd (knrValOn K (Additive.toMul y)) = 0 := by
        have := congrArg ULift.down hy
        simpa [knrProjOn] using this
      exact Multiplicative.toAdd.injective (by simpa using h0)
    refine ⟨Additive.ofMul ⟨Additive.toMul y, ?_⟩, rfl⟩
    show knrValOn K (Additive.toMul y) = 1
    exact hval
  · rintro ⟨x, rfl⟩
    simp only [knrProjOn]
    show ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul (knrInclOn K x))))
      = ULift.up (0 : ℤ)
    have hx : Additive.toMul (knrInclOn K x) = ((Additive.toMul x : ↥(knrValOn K).ker) :
        (↥(KnrSubfield K))ˣ) := rfl
    rw [hx]
    exact congrArg (fun z => ULift.up (Multiplicative.toAdd z)) (Additive.toMul x).2

/-- ★★★★ **GS (6.1) 的右端满射**（`n ↦ π^n`）。 -/
theorem knrProjOn_surjective (K : Type) [Field K] :
    Function.Surjective (knrProjOn K) := by
  intro n
  refine ⟨Additive.ofMul (knrUnitOn (K := K) (-(ULift.down n))), ?_⟩
  simp only [knrProjOn]
  show ULift.up (Multiplicative.toAdd (knrValOn K (knrUnitOn (K := K) (-(ULift.down n))))) = n
  rw [knrValOn_unit]
  simp

/-- ★★★★ **分裂**：`v π = 1`（GS 的「split by `1 ↦ π`」）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8163 quote="which is split by the map $\mathbf{Z}\to K_{nr}^{\times}$ sending $1$ to a local"
theorem knrProjOn_split :
    knrProjOn K (Additive.ofMul (knrPiOn K)) = ULift.up 1 := by
  simp only [knrProjOn]
  show ULift.up (Multiplicative.toAdd (knrValOn K (knrPiOn K))) = ULift.up (1 : ℤ)
  rw [knrValOn_pi]
  rfl

end L20261018

#print axioms L20261018.knrProjOn_exact
#print axioms L20261018.knrProjOn_surjective
#print axioms L20261018.knrProjOn_split
#print axioms L20261018.knrInclOn_injective
