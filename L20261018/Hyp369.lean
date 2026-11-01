import L20261018.Hyp368
import L20261018.Hyp342

/-!
# R1281（S36 C 项）：4.4 的 `hval` ＋「以 `hK1` 为显式假设」的 4.4

`HANDOFF` §S36 第 14 轮的核对表：4.4（`corollary_4_4_noFinite`）的假设里，除 `hK1` 外全部就位。
本文件把**其余全部输入锁死**，并给出显式带 `hK1` 的 4.4 版本 —— 下一轮只需证 `hK1` 这一条。

| 声明 | 内容 |
|---|---|
| **`hval44_F`** | `∃ u ∈ plane (kc 2) (kc π), v̄ (h1ToVEquiv u) ≠ 0`（取 `u = kEx π`） |
| **`corollary_4_4_F_of_hK1`** | ★★★★★ 4.4 的结论（`finrank commonCupMap.range = 2 ∧ finrank H¹ = 2`），假设 = `hK1` |
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

/-- ★★★★★ **4.4 的 `hval`**：取 `u = kEx π`，`v̄ (h1ToVEquiv u) = 1 ≠ 0`。 -/
theorem hval44_F :
    ∃ u ∈ ResidueCupData.plane (k := ZMod 3)
      (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
        three_isUnit_laurentSeries twoUnitF)
      (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
        three_isUnit_laurentSeries (pi : (LaurentSeries (ZMod 7))ˣ)),
      valLinOf (F := LaurentSeries (ZMod 7)) (p := 3)
        (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries
        (KummerBridge.h1ToVEquiv (LaurentSeries (ZMod 7)) 3
          u) ≠ 0 := by
  refine ⟨GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
    three_isUnit_laurentSeries (pi : (LaurentSeries (ZMod 7))ˣ),
    Submodule.subset_span (by simp), ?_⟩
  rw [show KummerBridge.h1ToVEquiv (LaurentSeries (ZMod 7)) 3
      (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
        three_isUnit_laurentSeries (pi : (LaurentSeries (ZMod 7))ˣ))
      = KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
        (pi : (LaurentSeries (ZMod 7))ˣ) from rfl]
  rw [valLinOf_kummerClass]
  show ((Multiplicative.toAdd (vCompatHom (F := LaurentSeries (ZMod 7))
    (pi : (LaurentSeries (ZMod 7))ˣ)) : ℤ) : ZMod 3) ≠ 0
  rw [pi_hπ]
  simp

set_option maxHeartbeats 16000000 in
/-- ★★★★★ **论文 4.4（`cor:rank-barrier`）在 `𝔽₇((t))`／`p = 3` 上**，
假设只剩 `hK1`（`finrank (ker v̄) = 1`，见 `HANDOFF` §S36 第 14 轮的路线 A）。 -/
theorem corollary_4_4_F_of_hK1
    (hK1 : Module.finrank (ZMod 3) ↥(LinearMap.ker (valLinOf
      (F := LaurentSeries (ZMod 7)) (p := 3)
      (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries)) = 1) :
    Module.finrank (ZMod 3)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := LaurentSeries (ZMod 7)) (p := 3))
          (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
            three_isUnit_laurentSeries twoUnitF)
          (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
            three_isUnit_laurentSeries (pi : (LaurentSeries (ZMod 7))ˣ))).range = 2
      ∧ Module.finrank (ZMod 3)
        (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup (LaurentSeries (ZMod 7))) (ZMod 3)) = 2 := by
  haveI := finite_H1_zmod_F
  exact corollary_4_4_noBridge (F := LaurentSeries (ZMod 7)) (p := 3)
    (v := vCompatHom) (π := pi) (a1 := twoUnitF) (a2 := pi)
    zetaF_spec three_isUnit_O three_isUnit_laurentSeries valCompat_O pi_hπ (by decide)
    hne43_F hval44_F hK1

end FqXt
end L20261018

#print axioms L20261018.FqXt.hval44_F
#print axioms L20261018.FqXt.corollary_4_4_F_of_hK1
