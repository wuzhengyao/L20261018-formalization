import L20261018.Hyp304

/-!
# R1196（`ValCompat` 非完备见证 · 第 2 块：`a = x/y` 与阶差的良定义性）

`PLAN-VALCOMPAT-HBRIDGE.md` §A 的第 2–3 步。核心是把 `a : Fˣ` 写成 `x / y`
（`x y : ↥𝒪[F]`, `y ≠ 0`），并证明**阶差 `znat x − znat y` 与表示无关**。

表示存在性由 `IsFractionRing ↥𝒪[F] F`（现成实例）＋ `IsLocalization.mk'_surjective` 给出。

## 本轮
| 声明 | 内容 |
|---|---|
| `exists_num_den` | `∀ a : Fˣ, ∃ x y, y ≠ 0 ∧ (a:F) * (y:F) = (x:F)` |
| **`znat_sub_eq_of_mul_eq`** | ★★★★★ **阶差与表示无关**（良定义性的全部内容） |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Fraction

variable {F : Type} [Field F] [ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]

/-- ★★★★★ **把 `a : Fˣ` 写成 `x / y`**（`x y : ↥𝒪[F]`，`y ≠ 0`）。

由 `IsFractionRing ↥𝒪[F] F`（`Valuation.instIsFractionRingInteger`）与
`IsLocalization.mk'_surjective` 给出。 -/
theorem exists_num_den (a : Fˣ) :
    ∃ (x y : ↥𝒪[F]), y ≠ 0 ∧ (a : F) * (y : F) = (x : F) := by
  classical
  obtain ⟨⟨x, y⟩, hy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors ↥𝒪[F]) (a : F)
  have hy0 : (y : ↥𝒪[F]) ≠ 0 :=
    (mem_nonZeroDivisors_iff_ne_zero).mp y.2
  refine ⟨x, (y : ↥𝒪[F]), hy0, ?_⟩
  rw [← hy]
  exact IsLocalization.mk'_spec F x y

/-- ★★★★★ **阶差与表示无关**：若 `a * y = x` 且 `a * y' = x'`（`y, y' ≠ 0`），
则 `znat x − znat y = znat x' − znat y'`。

这是 `v a := znat x − znat y` 良定义性的**全部**内容。 -/
theorem znat_sub_eq_of_mul_eq {a : Fˣ} {x x' y y' : ↥𝒪[F]}
    (hy : y ≠ 0) (hy' : y' ≠ 0)
    (h : (a : F) * (y : F) = (x : F)) (h' : (a : F) * (y' : F) = (x' : F)) :
    (znat (F := F) x : ℤ) - (znat (F := F) y : ℤ)
      = (znat (F := F) x' : ℤ) - (znat (F := F) y' : ℤ) := by
  -- `x ≠ 0`、`x' ≠ 0`（否则 `a * y = 0`）
  have hx : x ≠ 0 := by
    rintro rfl
    have h0 : (a : F) * (y : F) = 0 := by rw [h]; simp
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact a.ne_zero h1
    · exact hy (Subtype.ext h1)
  have hx' : x' ≠ 0 := by
    rintro rfl
    have h0 : (a : F) * (y' : F) = 0 := by rw [h']; simp
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact a.ne_zero h1
    · exact hy' (Subtype.ext h1)
  -- `x * y' = x' * y`
  have hmulF : (x : F) * (y' : F) = (x' : F) * (y : F) := by
    rw [← h, ← h']; ring
  have hmul : x * y' = x' * y := Subtype.ext (by simpa using hmulF)
  -- 取 `znat`
  have hz : znat (F := F) x + znat (F := F) y' = znat (F := F) x' + znat (F := F) y := by
    rw [← znat_mul hx hy', ← znat_mul hx' hy, hmul]
  omega

end Fraction

end L20261018

#print axioms L20261018.exists_num_den
#print axioms L20261018.znat_sub_eq_of_mul_eq
