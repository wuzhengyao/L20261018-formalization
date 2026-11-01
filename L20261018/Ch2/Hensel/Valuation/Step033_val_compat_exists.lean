import L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative

/-!
# R1198（`ValCompat` 非完备见证 · **收官**：`∃ v, ValCompat v`）

`PLAN-VALCOMPAT-HBRIDGE.md` §A 的第 5 步。**只用**
`[ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]`（**无完备性**）。

⟹ 这是一般 Hensel 离散赋值域上的 `ValCompat` **构造性见证**，
此前库内唯一见证（`Hyp189`）需 `[IsNonarchimedeanLocalField F]`。

## 本轮
| 声明 | 内容 |
|---|---|
| `zval_eq_znat` | `a` 整 ⟹ `zval a = znat a` |
| `mem_integer_vCompat` | `0 ≤ zval a ⟹ a ∈ 𝒪[F]` |
| `mem_maximalIdeal_vCompat` | `a ∈ 𝔪 ⟺ 0 < zval a` |
| **`valCompat_of_dvr`** | ★★★★★★ **`ValCompat vCompatHom`** |
| **`exists_valCompat`** | ★★★★★★ **`∃ v : Fˣ →* Multiplicative ℤ, ValCompat v`** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section ValCompatDVR

variable {F : Type} [Field F] [ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]

/-- `zval` 与同态 `toAdd` 一致（定义如此）。 -/
theorem toAdd_vCompatHom (a : Fˣ) :
    Multiplicative.toAdd (vCompatHom (F := F) a) = zval (F := F) a := rfl

/-- `a` 整 ⟹ `zval a = znat a`（取表示 `a = a / 1`）。 -/
theorem zval_eq_znat {a : Fˣ} (h : (a : F) ∈ 𝒪[F]) :
    zval (F := F) a = (znat (F := F) ⟨(a : F), h⟩ : ℤ) := by
  have key := zval_spec (F := F) (a := a) (x := ⟨(a : F), h⟩) (y := 1) one_ne_zero (by simp)
  simpa [znat_one] using key

/-- ★★★★★ **`ValCompat.mem_integer`**。 -/
theorem mem_integer_vCompat (a : Fˣ) :
    0 ≤ Multiplicative.toAdd (vCompatHom (F := F) a) → (a : F) ∈ 𝒪[F] := by
  intro ha
  rw [toAdd_vCompatHom] at ha
  obtain ⟨hy, hya⟩ := numDen_spec (F := F) a
  have hx : (numDen (F := F) a).1 ≠ 0 := num_ne_zero_of_mul_eq hy hya
  have hzx := zval_spec (F := F) (a := a) hy hya
  rw [hzx] at ha
  have hle : znat (F := F) (numDen (F := F) a).2 ≤ znat (F := F) (numDen (F := F) a).1 := by
    omega
  obtain ⟨c, hc⟩ := (znat_le_iff_dvd hy hx).mp hle
  have hy0 : ((numDen (F := F) a).2 : F) ≠ 0 := by simpa using hy
  have hxc : ((numDen (F := F) a).1 : F) = ((numDen (F := F) a).2 : F) * (c : F) := by
    rw [hc]; push_cast; ring
  have hca : (a : F) = (c : F) := by
    have h1 : (a : F) * ((numDen (F := F) a).2 : F)
        = (c : F) * ((numDen (F := F) a).2 : F) := by
      rw [hya, hxc, mul_comm]
    exact mul_right_cancel₀ hy0 h1
  rw [hca]
  exact c.2

/-- ★★★★★ **`ValCompat.mem_maximalIdeal`**。 -/
theorem mem_maximalIdeal_vCompat (a : Fˣ) (h : (a : F) ∈ 𝒪[F]) :
    (⟨(a : F), h⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] ↔
      0 < Multiplicative.toAdd (vCompatHom (F := F) a) := by
  rw [toAdd_vCompatHom, zval_eq_znat (F := F) h]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[F]
  have h𝔪 : IsLocalRing.maximalIdeal ↥𝒪[F] = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hznatπ : znat (F := F) π = 1 := by
    simp only [znat]
    rw [IsDiscreteValuationRing.addVal_uniformizer hπ]
    rfl
  have ha0 : (⟨(a : F), h⟩ : ↥𝒪[F]) ≠ 0 := by
    intro h0
    exact a.ne_zero (congrArg Subtype.val h0)
  rw [h𝔪, Ideal.mem_span_singleton]
  rw [← znat_le_iff_dvd hπ0 ha0, hznatπ]
  omega

/-- ★★★★★★ **`ValCompat` 在**任意**离散赋值域上成立**（**无完备性**）。

取 `v = vCompatHom`（由 `𝒪[F]` 上的 `𝔪`-进阶函数 `addVal` 经分式域延拓得到）。 -/
theorem valCompat_of_dvr : ValCompat (F := F) (vCompatHom (F := F)) where
  mem_integer := mem_integer_vCompat
  mem_maximalIdeal := mem_maximalIdeal_vCompat

/-- ★★★★★★ **存在性**：`∃ v : Fˣ →* Multiplicative ℤ, ValCompat v`。

只用 `[ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]` —— **一般 Hensel 离散赋值域**，
不需要 `[IsNonarchimedeanLocalField F]`（完备性）。 -/
theorem exists_valCompat :
    ∃ v : Fˣ →* Multiplicative ℤ, ValCompat (F := F) v :=
  ⟨vCompatHom, valCompat_of_dvr⟩

end ValCompatDVR

end L20261018

#print axioms L20261018.mem_integer_vCompat
#print axioms L20261018.mem_maximalIdeal_vCompat
#print axioms L20261018.valCompat_of_dvr
#print axioms L20261018.exists_valCompat
