import L20261018.Hyp464

/-!
# S40 R5：**正确的 `K_nr` 载体** —— `⋃_{K'} K'((π))`（`RECON-R3` §82.4 第 1–2 步）

## 背景（R4 的载体更正）

R2–R4 用的是 `K_s((π)) = LaurentSeries (SeparableClosure K)`，那是 GS 的
`K_nr` 的**真超集**（`RECON-R3` §82）：

```
K_nr = ⋃_{K'/K 有限可分} K'((π))   ⊊   K_s((π))
```

且 `ContinuousSMul G (K_s((π))^×)` **不成立**（`Hyp386` 因此无法入场），而在 `K_nr` 上成立。

## 本轮（第 1–2 步）：造 `K_nr` 这个 objects（`IntermediateField`）

载体构造用**系数包含的像之并**：

* `coeffIncl K' : LaurentSeries ↥K' →+* LaurentSeries (SepCl K)`
  ＝ 逐系数用 `algebraMap ↥K' (SepCl K)`（用 `HahnSeries.map`，同 `Hyp464.knrMap` 的 `convert` 工艺）。
* `Knr := ⨆ (K' : {K' // FiniteDimensional K K'}), (coeffIncl K'.1).fieldRange`
  —— 在 `Subfield` 层做 `iSup`（`Subfield.mem_iSup_of_directed` 要 `Directed`）。
* 族**定向**：`K' ≤ K''` ⟹ `(coeffIncl K').range ≤ (coeffIncl K'').range`
  （因 `coeffIncl K''` 在 `↥K'` 上的限制就是 `coeffIncl K'`）。

## 本轮机检

| 声明 | 内容 |
|---|---|
| `coeffIncl` | 系数包含 `LaurentSeries ↥K' →+* LaurentSeries (SepCl K)` |
| `coeffIncl_coeff` | 逐系数：`(coeffIncl K' x).coeff n = algebraMap _ _ (x.coeff n)` |
| `coeffIncl_comp` | `K' ≤ K''` 时 `coeffIncl K'' ∘ (系数包含) = coeffIncl K'` |
| `KnrSubfield` | `⨆_{K' 有限} (coeffIncl K').fieldRange`（`Subfield`） |
| **`Knr`** | ★★★★★ **`IntermediateField K (LaurentSeries (SepCl K))`**，`= ⋃ K'((π))` |
| **`mem_Knr`** | ★★★★★ `x ∈ Knr ↔ ∃ K' 有限, x ∈ (coeffIncl K').fieldRange`（**并的成员判据**） |
| `finDimensional_sup_mem` | 两个有限中间域的上确界仍有限（定向性用） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-! ## 1. 系数包含 `LaurentSeries ↥K' →+* LaurentSeries (K_s)` -/

/-- ★★★★ **系数包含**：把 `K'((π))` 逐系数嵌进 `K_s((π))`。 -/
noncomputable def coeffIncl (K' : IntermediateField K (SeparableClosure K)) :
    LaurentSeries ↥K' →+* LaurentSeries (SeparableClosure K) where
  toFun x := HahnSeries.map x (algebraMap ↥K' (SeparableClosure K))
  map_zero' := by
    ext n
    rw [HahnSeries.map_coeff]
    simp
  map_one' := by
    convert HahnSeries.map_one (f := (algebraMap ↥K' (SeparableClosure K) : ↥K' →*₀
      SeparableClosure K)) using 2
    all_goals (ext n <;> rfl)
  map_add' x y := by
    convert HahnSeries.map_add (f := (algebraMap ↥K' (SeparableClosure K) : ↥K' →+
      SeparableClosure K)) (x := x) (y := y) using 2
    all_goals (ext n <;> rfl)
  map_mul' x y := by
    convert HahnSeries.map_mul (f := (algebraMap ↥K' (SeparableClosure K) : ↥K' →ₙ+*
      SeparableClosure K)) (x := x) (y := y) using 2
    all_goals (ext n <;> rfl)

theorem coeffIncl_coeff (K' : IntermediateField K (SeparableClosure K))
    (x : LaurentSeries ↥K') (n : ℤ) :
    (coeffIncl (K := K) K' x).coeff n = algebraMap ↥K' (SeparableClosure K) (x.coeff n) :=
  HahnSeries.map_coeff x _ n

/-! ## 2. 下标类型与定向性 -/

/-- 下标：`K` 在 `K_s` 中的**有限维**中间域。 -/
abbrev FinInt (K : Type) [Field K] :=
  { K' : IntermediateField K (SeparableClosure K) // FiniteDimensional K K' }

/-- 有限中间域族**定向**：`K' ⊔ K''` 仍有限。 -/
theorem finInt_sup (K' K'' : FinInt K) :
    ∃ K3 : FinInt K, K'.1 ≤ K3.1 ∧ K''.1 ≤ K3.1 := by
  haveI := K'.2
  haveI := K''.2
  haveI : FiniteDimensional K ↥(K'.1 ⊔ K''.1) := IntermediateField.finiteDimensional_sup K'.1 K''.1
  exact ⟨⟨K'.1 ⊔ K''.1, inferInstance⟩, le_sup_left, le_sup_right⟩

/-- `K' ≤ K''` ⟹ `K'((π)) ⊆ K''((π))`（在 `K_s((π))` 里）。 -/
theorem fieldRange_le_of_le {K' K'' : IntermediateField K (SeparableClosure K)} (h : K' ≤ K'') :
    (coeffIncl (K := K) K').fieldRange ≤ (coeffIncl (K := K) K'').fieldRange := by
  rintro _ ⟨y, rfl⟩
  refine ⟨HahnSeries.map y (IntermediateField.inclusion h), ?_⟩
  ext n
  rw [coeffIncl_coeff, coeffIncl_coeff, HahnSeries.map_coeff,
    IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
    IntermediateField.coe_inclusion]

/-- 有限中间域族在 `Subfield` 意义下**定向**。 -/
theorem knrSubfield_directed :
    Directed (· ≤ ·) (fun K' : FinInt K => (coeffIncl (K := K) K'.1).fieldRange) := by
  intro a b
  obtain ⟨c, hac, hbc⟩ := finInt_sup a b
  exact ⟨c, fieldRange_le_of_le hac, fieldRange_le_of_le hbc⟩

instance knrFinIntNonempty : Nonempty (FinInt K) :=
  ⟨⟨⊥, inferInstance⟩⟩

/-! ## 3. `Knr`：有限不分歧扩张之并 -/

/-- ★★★★★ **GS 的 `K_nr` 的底层子域**：`⋃_{K'/K 有限可分} K'((π))`，
作为 `K_s((π))` 的 `Subfield`。 -/
noncomputable def KnrSubfield (K : Type) [Field K] :
    Subfield (LaurentSeries (SeparableClosure K)) :=
  ⨆ (K' : FinInt K), (coeffIncl (K := K) K'.1).fieldRange

/-- ★★★★★ **并的成员判据**：`x ∈ K_nr ⟺ x 落在某个**有限** `K'((π))` 里。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8152 quote="maximal unramified extension of $K$, i.e. the composite of all finite unramified"
theorem mem_KnrSubfield {x : LaurentSeries (SeparableClosure K)} :
    x ∈ KnrSubfield K ↔ ∃ K' : FinInt K, x ∈ (coeffIncl (K := K) K'.1).fieldRange :=
  Subfield.mem_iSup_of_directed (knrSubfield_directed (K := K))


end L20261018

#print axioms L20261018.coeffIncl_coeff
#print axioms L20261018.finInt_sup
#print axioms L20261018.fieldRange_le_of_le
#print axioms L20261018.knrSubfield_directed
#print axioms L20261018.mem_KnrSubfield
