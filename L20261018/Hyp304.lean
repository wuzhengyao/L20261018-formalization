import L20261018.Hyp301

/-!
# R1195（`ValCompat` 非完备见证 · 第 1 块：`𝒪[F]` 上的 ℤ-值阶函数）

目标：证 `∃ v : Fˣ →* Multiplicative ℤ, ValCompat v`，**只用**
`[ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]`（无完备性）。

工具：`IsDiscreteValuationRing.addVal : AddValuation ↥𝒪[F] ℕ∞`
（`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:402`，**无完备性**），
配合 `IsFractionRing ↥𝒪[F] F`（现成实例）把阶函数延拓到 `Fˣ`。

本轮建立阶函数本体 `znat` 及其乘性／整除判据。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Znat

variable {F : Type} [Field F] [ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]

/-- `addVal` 在非零元上有限。 -/
theorem addVal_ne_top_iff {x : ↥𝒪[F]} :
    IsDiscreteValuationRing.addVal ↥𝒪[F] x ≠ ⊤ ↔ x ≠ 0 := by
  rw [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]

/-- ★★★★★ **`𝒪[F]` 上的阶函数**（`0` 处取 `0`）：`𝔪`-进赋值，取值 `ℕ`。

由 `IsDiscreteValuationRing.addVal`（`ℕ∞`-值）取 `toNat` 得到。 -/
noncomputable def znat (x : ↥𝒪[F]) : ℕ :=
  (IsDiscreteValuationRing.addVal ↥𝒪[F] x).toNat

theorem znat_zero : znat (F := F) 0 = 0 := by
  simp [znat, IsDiscreteValuationRing.addVal_zero]

theorem znat_one : znat (F := F) 1 = 0 := by
  simp [znat, IsDiscreteValuationRing.addVal_one]

/-- 非零元上 `znat` 与 `addVal` 一致。 -/
theorem coe_znat {x : ↥𝒪[F]} (hx : x ≠ 0) :
    ((znat (F := F) x : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal ↥𝒪[F] x :=
  ENat.natCast_toNat ((addVal_ne_top_iff (F := F)).mpr hx)

/-- ★★★★★ **`znat` 乘性**（非零情形）：`znat (x*y) = znat x + znat y`。 -/
theorem znat_mul {x y : ↥𝒪[F]} (hx : x ≠ 0) (hy : y ≠ 0) :
    znat (F := F) (x * y) = znat (F := F) x + znat (F := F) y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have h : ((znat (F := F) (x * y) : ℕ) : ℕ∞)
      = ((znat (F := F) x + znat (F := F) y : ℕ) : ℕ∞) := by
    rw [coe_znat (F := F) hxy, IsDiscreteValuationRing.addVal_mul,
      ← coe_znat (F := F) hx, ← coe_znat (F := F) hy, Nat.cast_add]
  exact Nat.cast_injective h

/-- ★★★★★ **`znat` 整除判据**：`znat x ≤ znat y ↔ x ∣ y`（`x, y` 非零）。

注意方向：**阶小者整除**（`addVal π = 1 ≤ 2 = addVal π²`，而 `π ∣ π²`）。 -/
theorem znat_le_iff_dvd {x y : ↥𝒪[F]} (hx : x ≠ 0) (hy : y ≠ 0) :
    znat (F := F) x ≤ znat (F := F) y ↔ x ∣ y := by
  have h := IsDiscreteValuationRing.addVal_le_iff_dvd (R := ↥𝒪[F]) (a := x) (b := y)
  rw [← coe_znat (F := F) hx, ← coe_znat (F := F) hy] at h
  simpa using h

end Znat

end L20261018

#print axioms L20261018.addVal_ne_top_iff
#print axioms L20261018.znat_mul
#print axioms L20261018.znat_le_iff_dvd
