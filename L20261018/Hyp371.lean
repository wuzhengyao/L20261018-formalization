import Hyp370

/-!
# R1284（S36 C 项 · `hK1` 下界）：`0 < finrank (ker v̄)`

`hK1 : finrank (ker (valLinOf v hp)) = 1` 的一半：**下界** `≥ 1`。
非零见证 = `kc (2)`（**GaloBase** 载体），其非零性由 `Hyp366.hcupG_F` 反推
（`cup (kc 2) (kc π) ≠ 0 ⟹ kc 2 ≠ 0`），其属于 `ker` 由 `valLinOf_kummerClass` ＋ `zval 2 = 0` 给出。

| 声明 | 内容 |
|---|---|
| `kc_two_ne_zero_G` | ★★★★ `KummerBridge.kummerClass F 3 hpF twoUnitF ≠ 0`（GaloBase 载体） |
| **`finrank_ker_valLinOf_pos`** | ★★★★★ `0 < finrank (ZMod 3) ↥(ker (valLinOf v hp))` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity (LaurentSeries (ZMod 7)) 3 :=
  hasEnoughRootsOfUnity_laurentSeries_zmod7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- ★★★★ **`kc (2) ≠ 0`（GaloBase 载体）** —— 由 `hcupG_F` 反推。 -/
theorem kc_two_ne_zero_G :
    KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries twoUnitF
      ≠ 0 := by
  intro h0
  refine hcupG_F ?_
  rw [h0]
  simp

/-- `kc (2) ∈ ker (valLinOf v hp)`。 -/
theorem kc_two_mem_ker :
    valLinOf (F := LaurentSeries (ZMod 7)) (p := 3)
      (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries
      (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries twoUnitF)
      = 0 := by
  rw [valLinOf_kummerClass]
  have hz : zval (F := LaurentSeries (ZMod 7)) twoUnitF = 0 :=
    zval_unit_eq_zero (F := LaurentSeries (ZMod 7)) two_isUnit_O
  show ((Multiplicative.toAdd (vCompatHom (F := LaurentSeries (ZMod 7)) twoUnitF) : ℤ) :
    ZMod 3) = 0
  rw [show vCompatHom (F := LaurentSeries (ZMod 7)) twoUnitF
    = Multiplicative.ofAdd (zval (F := LaurentSeries (ZMod 7)) twoUnitF) from rfl, hz]
  simp

/-- ★★★★★ **`hK1` 的下界**：`0 < finrank (ker v̄)`。 -/
theorem finrank_ker_valLinOf_pos :
    0 < Module.finrank (ZMod 3) ↥(LinearMap.ker (valLinOf
      (F := LaurentSeries (ZMod 7)) (p := 3)
      (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries)) := by
  rw [Module.finrank_pos_iff]
  refine ⟨⟨_, kc_two_mem_ker⟩, 0, ?_⟩
  intro h
  exact kc_two_ne_zero_G (congrArg Subtype.val h)

end FqXt
end L20261018

#print axioms L20261018.FqXt.kc_two_ne_zero_G
#print axioms L20261018.FqXt.finrank_ker_valLinOf_pos
