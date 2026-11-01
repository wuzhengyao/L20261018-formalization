import L20261018.Ch2.Hensel.Valuation.Step031_val_compat_well_defined

/-!
# R1197（`ValCompat` 非完备见证 · 第 3 块：`ℤ`-值函数与它的乘性）

`PLAN-VALCOMPAT-HBRIDGE.md` §A 的第 3–4 步：造 `zval : Fˣ → ℤ`（阶），证乘性，
再打包成 `Fˣ →* Multiplicative ℤ`。

## 本轮
| 声明 | 内容 |
|---|---|
| `num_ne_zero_of_mul_eq` | `a * y = x`、`y ≠ 0` ⟹ `x ≠ 0` |
| **`zval`** | ★★★★★ `Fˣ → ℤ`（任一表示 `a = x/y` 的 `znat x − znat y`） |
| `zval_spec` | 在**任意**表示上取值公式 |
| `zval_one`／**`zval_mul`** | ★★★★★ 乘性 |
| **`vCompatHom`** | ★★★★★ `Fˣ →* Multiplicative ℤ` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Zval

variable {F : Type} [Field F] [ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]

/-- 若 `a * y = x` 且 `y ≠ 0`（`a ≠ 0`），则 `x ≠ 0`。 -/
theorem num_ne_zero_of_mul_eq {a : Fˣ} {x y : ↥𝒪[F]} (hy : y ≠ 0)
    (h : (a : F) * (y : F) = (x : F)) : x ≠ 0 := by
  rintro rfl
  have h0 : (a : F) * (y : F) = 0 := by rw [h]; simp
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact a.ne_zero h1
  · exact hy (Subtype.ext h1)

/-- 表示存在性（成对形式，便于 `Classical.choose`）。 -/
theorem exists_num_den' (a : Fˣ) :
    ∃ p : ↥𝒪[F] × ↥𝒪[F], p.2 ≠ 0 ∧ (a : F) * (p.2 : F) = (p.1 : F) := by
  obtain ⟨x, y, hy, h⟩ := exists_num_den (F := F) a
  exact ⟨(x, y), hy, h⟩

/-- 选定的分子／分母。 -/
noncomputable def numDen (a : Fˣ) : ↥𝒪[F] × ↥𝒪[F] :=
  Classical.choose (exists_num_den' (F := F) a)

theorem numDen_spec (a : Fˣ) :
    (numDen (F := F) a).2 ≠ 0 ∧ (a : F) * ((numDen (F := F) a).2 : F) = ((numDen (F := F) a).1 : F) :=
  Classical.choose_spec (exists_num_den' (F := F) a)

/-- ★★★★★ **`Fˣ` 上的阶函数** `zval : Fˣ → ℤ`。

`zval a = znat x − znat y`，其中 `a = x / y`（**与表示无关**，`znat_sub_eq_of_mul_eq`）。 -/
noncomputable def zval (a : Fˣ) : ℤ :=
  (znat (F := F) (numDen (F := F) a).1 : ℤ) - (znat (F := F) (numDen (F := F) a).2 : ℤ)

/-- ★★★★★ **在任意表示上取值**：`a = x / y` ⟹ `zval a = znat x − znat y`。 -/
theorem zval_spec {a : Fˣ} {x y : ↥𝒪[F]} (hy : y ≠ 0)
    (h : (a : F) * (y : F) = (x : F)) :
    zval (F := F) a = (znat (F := F) x : ℤ) - (znat (F := F) y : ℤ) :=
  znat_sub_eq_of_mul_eq (numDen_spec (F := F) a).1 hy (numDen_spec (F := F) a).2 h

theorem zval_one : zval (F := F) 1 = 0 := by
  have h := zval_spec (F := F) (a := 1) (x := 1) (y := 1) one_ne_zero (by simp)
  simpa [znat_one] using h

/-- ★★★★★ **`zval` 乘性**。 -/
theorem zval_mul (a b : Fˣ) :
    zval (F := F) (a * b) = zval (F := F) a + zval (F := F) b := by
  obtain ⟨hy, hya⟩ := numDen_spec (F := F) a
  obtain ⟨hy', hya'⟩ := numDen_spec (F := F) b
  set x := (numDen (F := F) a).1
  set y := (numDen (F := F) a).2
  set x' := (numDen (F := F) b).1
  set y' := (numDen (F := F) b).2
  have hx : x ≠ 0 := num_ne_zero_of_mul_eq hy hya
  have hx' : x' ≠ 0 := num_ne_zero_of_mul_eq hy' hya'
  -- `(a*b) * (y*y') = x*x'`
  have hprod : ((a * b : Fˣ) : F) * ((y * y' : ↥𝒪[F]) : F) = ((x * x' : ↥𝒪[F]) : F) := by
    push_cast
    calc ((a : F) * (b : F)) * ((y : F) * (y' : F))
        = ((a : F) * (y : F)) * ((b : F) * (y' : F)) := by ring
      _ = (x : F) * (x' : F) := by rw [hya, hya']
  have h := zval_spec (F := F) (a := a * b) (x := x * x') (y := y * y')
    (mul_ne_zero hy hy') hprod
  rw [h, zval_spec (F := F) hy hya, zval_spec (F := F) hy' hya',
    znat_mul hx hx', znat_mul hy hy']
  push_cast
  ring

/-- ★★★★★ **`Fˣ →* Multiplicative ℤ`**（`ValCompat` 所需的同态）。 -/
noncomputable def vCompatHom : Fˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (zval (F := F) a)
  map_one' := by simp [zval_one]
  map_mul' a b := by simp [zval_mul, add_comm]

end Zval

end L20261018

#print axioms L20261018.zval_spec
#print axioms L20261018.zval_mul
#print axioms L20261018.vCompatHom
