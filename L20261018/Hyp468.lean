import L20261018.Hyp467

/-!
# S40 R7：`G = Gal(K_s/K)` **保 `K_nr`**（`RECON-R3` §84.3 第 3 步）

## 本轮做什么

R6 已在正确的载体 `KnrSubfield K = ⋃_{K'} K'((π))` 上完成 GS (6.1) 的模层
（`v`／`U_nr`／正合／分裂）。要装 `DiscreteShortExact`，还缺 **`G`-作用**：
须先证 `knrMap σ` **保 `K_nr`**。

**要点**：`x ∈ K'((π))` ⟹ `knrMap σ x ∈ (σ K')((π))`，而 `σ K'` 仍**有限维**
（`IntermediateField.finiteDimensional_map`）⟹ 仍在 `K_nr = ⋃ K'((π))` 里。

## 本轮机检

| 声明 | 内容 |
|---|---|
| `mapField σ K'` | `K'.map σ.toAlgHom`（`σ` 作用在中间域上） |
| `mapField_finite` | `σ K'` 仍有限维 |
| `coeffAlg σ K'` | `↥K' →+* ↥(σ K')`，`c ↦ σ c` |
| `coeffIncl_knrMap` | ★★★★ `knrMap σ (coeffIncl K' y) = coeffIncl (σK') (map y (coeffAlg σ K'))` |
| **`knrMap_mem_Knr`** | ★★★★★ **`x ∈ K_nr ⟹ knrMap σ x ∈ K_nr`** |
| `knrSMul`／`knrMulAction` | ★★★★ `G` 在 `↥K_nr` 上的 `MulAction`（限制） |
| **`knrValOn_smul`** | ★★★★ **`v (σ • u) = v u`**（`v` 的 `G`-不变性，在 `K_nr` 上） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-! ## 1. `σ` 作用在中间域上 -/

/-- `σ K' := K'.map σ.toAlgHom`。 -/
noncomputable def mapField (σ : TauCeti.AbsoluteGaloisGroup K)
    (K' : IntermediateField K (SeparableClosure K)) : IntermediateField K (SeparableClosure K) :=
  IntermediateField.map (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K).toAlgHom K'

/-- `σ K'` 仍有限维。 -/
theorem mapField_finite (σ : TauCeti.AbsoluteGaloisGroup K) (K' : FinInt K) :
    FiniteDimensional K ↥(mapField (K := K) σ K'.1) := by
  haveI := K'.2
  exact IntermediateField.finiteDimensional_map
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K).toAlgHom

/-- `c ↦ σ c` 作为 `↥K' →+* ↥(σ K')`。 -/
noncomputable def coeffAlg (σ : TauCeti.AbsoluteGaloisGroup K)
    (K' : IntermediateField K (SeparableClosure K)) :
    ↥K' →+* ↥(mapField (K := K) σ K') where
  toFun c := ⟨σ (c : SeparableClosure K), by
    rw [mapField, IntermediateField.mem_map]
    exact ⟨(c : ↥K'), c.2, rfl⟩⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' a b := by ext; simp
  map_mul' a b := by ext; simp

/-! ## 2. 系数层：`knrMap` 与 `coeffIncl` 的交换 -/

/-- ★★★★ **`knrMap` 把 `K'((π))` 送进 `(σK')((π))`**（逐系数）。 -/
theorem coeffIncl_knrMap (σ : TauCeti.AbsoluteGaloisGroup K)
    (K' : IntermediateField K (SeparableClosure K)) (y : LaurentSeries ↥K') :
    knrMap σ (coeffIncl (K := K) K' y)
      = coeffIncl (K := K) (mapField (K := K) σ K')
        (HahnSeries.map y (coeffAlg (K := K) σ K')) := by
  ext n
  rw [knrMap_coeff, coeffIncl_coeff, coeffIncl_coeff, HahnSeries.map_coeff,
    IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply]
  rfl

/-! ## 3. `knrMap σ` 保 `K_nr` -/

/-- ★★★★★ **`G` 保 `K_nr`**：`x ∈ K_nr ⟹ knrMap σ x ∈ K_nr`。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8156 quote="G:=\operatorname{Gal}(K_{nr}|K)$ is canonically isomorphic to"
theorem knrMap_mem_Knr (σ : TauCeti.AbsoluteGaloisGroup K)
    {x : LaurentSeries (SeparableClosure K)} (hx : x ∈ KnrSubfield K) :
    knrMap σ x ∈ KnrSubfield K := by
  rw [mem_KnrSubfield] at hx ⊢
  obtain ⟨K', y, hy⟩ := hx
  refine ⟨⟨mapField (K := K) σ K'.1, mapField_finite (K := K) σ K'⟩,
    HahnSeries.map y (coeffAlg (K := K) σ K'.1), ?_⟩
  rw [← hy, coeffIncl_knrMap]

/-! ## 4. `G` 在 `K_nr` 与 `K_nr^×` 上的作用 -/

/-- ★★★★ **`knrMap σ` 限制到 `K_nr`**（环自同态）。 -/
noncomputable def knrMapOn (σ : TauCeti.AbsoluteGaloisGroup K) :
    ↥(KnrSubfield K) →+* ↥(KnrSubfield K) where
  toFun x := ⟨knrMap σ (x : LaurentSeries (SeparableClosure K)), knrMap_mem_Knr σ x.2⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' a b := by ext; simp
  map_mul' a b := by ext; simp

theorem knrMapOn_coe (σ : TauCeti.AbsoluteGaloisGroup K) (x : ↥(KnrSubfield K)) :
    ((knrMapOn (K := K) σ x : ↥(KnrSubfield K)) : LaurentSeries (SeparableClosure K))
      = knrMap σ (x : LaurentSeries (SeparableClosure K)) := rfl

theorem knrMapOn_id : knrMapOn (K := K) (1 : TauCeti.AbsoluteGaloisGroup K) =
    RingHom.id ↥(KnrSubfield K) := by
  ext x
  rw [knrMapOn_coe, RingHom.id_apply, knrMap_id]
  rfl

theorem knrMapOn_mul (σ τ : TauCeti.AbsoluteGaloisGroup K) :
    knrMapOn (K := K) (σ * τ) = (knrMapOn (K := K) σ).comp (knrMapOn (K := K) τ) := by
  ext x
  rw [knrMapOn_coe, RingHom.comp_apply, knrMapOn_coe, knrMapOn_coe, knrMap_mul]
  rfl

/-- ★★★★ **`G` 在 `K_nr` 上的 `MulAction`**。 -/
noncomputable instance knrMulActionOn : MulAction (TauCeti.AbsoluteGaloisGroup K)
    ↥(KnrSubfield K) where
  smul σ x := knrMapOn (K := K) σ x
  one_smul x := by
    show knrMapOn (K := K) 1 x = x
    rw [knrMapOn_id]
    rfl
  mul_smul σ τ x := by
    show knrMapOn (K := K) (σ * τ) x = knrMapOn (K := K) σ (knrMapOn (K := K) τ x)
    rw [knrMapOn_mul]
    rfl

/-- ★★★★ **`G` 在 `K_nr^×` 上的 `MulAction`**。 -/
noncomputable instance knrUnitsMulActionOn : MulAction (TauCeti.AbsoluteGaloisGroup K)
    (↥(KnrSubfield K))ˣ where
  smul σ u := Units.map (knrMapOn (K := K) σ).toMonoidHom u
  one_smul u := by
    show Units.map (knrMapOn (K := K) 1).toMonoidHom u = u
    rw [knrMapOn_id]
    rfl
  mul_smul σ τ u := by
    show Units.map (knrMapOn (K := K) (σ * τ)).toMonoidHom u
      = Units.map (knrMapOn (K := K) σ).toMonoidHom
        (Units.map (knrMapOn (K := K) τ).toMonoidHom u)
    rw [knrMapOn_mul]
    ext
    rfl

/-- 单位层：`K_nr^× ↪ K_s((π))^×` 与作用交换。 -/
theorem knrUnitIncl_smul (σ : TauCeti.AbsoluteGaloisGroup K)
    (u : (↥(KnrSubfield K))ˣ) :
    knrUnitIncl K (σ • u) = σ • knrUnitIncl K u := by
  apply Units.ext
  show (Subfield.subtype (KnrSubfield K))
      ((knrMapOn (K := K) σ) (((u : (↥(KnrSubfield K))ˣ) : ↥(KnrSubfield K))))
    = knrMap σ (Subfield.subtype (KnrSubfield K)
        (((u : (↥(KnrSubfield K))ˣ) : ↥(KnrSubfield K))))
  exact knrMapOn_coe (K := K) σ (((u : (↥(KnrSubfield K))ˣ) : ↥(KnrSubfield K)))

/-- ★★★★ **`v` 的 `G`-不变性**（在 `K_nr` 上）：`v (σ • u) = v u`。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8160 quote="Denoting by $U_{nr}$ the multiplicative group of units in $K_{nr}$, we get an"
theorem knrValOn_smul (σ : TauCeti.AbsoluteGaloisGroup K)
    (u : (↥(KnrSubfield K))ˣ) :
    knrValOn K (σ • u) = knrValOn K u := by
  rw [knrValOn_apply, knrValOn_apply, knrUnitIncl_smul, knrVal_smul]

end L20261018

#print axioms L20261018.knrMapOn_id
#print axioms L20261018.knrMapOn_mul
#print axioms L20261018.knrMulActionOn
#print axioms L20261018.knrUnitsMulActionOn
#print axioms L20261018.knrUnitIncl_smul
#print axioms L20261018.knrValOn_smul
