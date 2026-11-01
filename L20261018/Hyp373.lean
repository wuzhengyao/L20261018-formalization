import L20261018.Hyp372

/-!
# R1286（S36 C 项 · `hK1` 上界）：**`finrank (ker v̄) ≤ 1`** ⟹ **`hK1`**

`Hyp148.ker_dependent` 的 `valLinOf` 层对应物：`ker v̄` 中任意两元线性相关。

| 声明 | 内容 |
|---|---|
| **`finrank_ker_valLinOf_le_one`** | ★★★★★ `finrank (ZMod 3) ↥(ker (valLinOf v hp)) ≤ 1` |
| **`hK1_F`** | ★★★★★★ **`finrank (ZMod 3) ↥(ker (valLinOf v hp)) = 1`**（论文 4.4 的 `hK1`） |

**证明骨架**（`finrank_le_one_iff`，生成元 `γ := kc 2`）：
`w ∈ ker` → `exists_unit_rep_F` 给 `w = kc u`（`zval u = 0`）→ `exists_unit_of_zval_eq_zero` 抬成 `U ∈ ↥𝒪ˣ`
→ `residue_dependent U T`（`T` 是 `2` 的单位版）给 `(∃j: U ≡ T^j·立方) ∨ (∃j: T ≡ U^j·立方)`
→ `isCube_of_residue_cube` ＋ `kummerClass_eq_zero_iff` 把「剩余差一个立方」变成「`kc` 差 `j •`」
→ `w = j • γ`（右支则取 `j⁻¹`，并用 `kc_two_ne_zero_G` 排除 `j = 0`）。
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

/-- 局部缩写：`F = 𝔽₇((t))` 的单位 `2` 在 `↥𝒪` 中的版本（`zval = 0`）。 -/
theorem zval_twoUnitF : zval (F := LaurentSeries (ZMod 7)) twoUnitF = 0 :=
  zval_unit_eq_zero (F := LaurentSeries (ZMod 7)) two_isUnit_O

/-- `kc 1 = 0`。 -/
theorem kc_one :
    KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
      (1 : (LaurentSeries (ZMod 7))ˣ) = 0 :=
  (KummerBridge.kummerClass_eq_zero_iff _ _ _ _).mpr
    (MonoidHom.mem_range.mpr ⟨1, by simp⟩)

/-- `kc x⁻¹ = - kc x`。 -/
theorem kc_inv (x : (LaurentSeries (ZMod 7))ˣ) :
    KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries x⁻¹
      = - KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries x := by
  have h := KummerV.kummerClass_mul (F := LaurentSeries (ZMod 7)) (p := 3)
    three_isUnit_laurentSeries x x⁻¹
  rw [mul_inv_cancel, kc_one, eq_comm, add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

/-- 「剩余是立方 ⟹ `kc` 为零」。 -/
theorem kc_eq_zero_of_residue_cube (A V : (↥𝒪[LaurentSeries (ZMod 7)])ˣ)
    (h : unitsResidue A = (unitsResidue V) ^ 3) :
    KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
      (unitsToF A) = 0 := by
  obtain ⟨c, hc⟩ := isCube_of_residue_cube A V h
  rw [KummerBridge.kummerClass_eq_zero_iff, MonoidHom.mem_range]
  exact ⟨c, hc⟩

/-- ★★★★★ **`finrank (ker v̄) ≤ 1`**（`valLinOf` 层的 `ker_dependent`）。 -/
theorem finrank_ker_valLinOf_le_one :
    Module.finrank (ZMod 3) ↥(LinearMap.ker (valLinOf
      (F := LaurentSeries (ZMod 7)) (p := 3)
      (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries)) ≤ 1 := by
  rw [finrank_le_one_iff]
  refine ⟨⟨KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
    twoUnitF, kc_two_mem_ker⟩, ?_⟩
  intro w
  obtain ⟨u, hzu, hkcu⟩ := exists_unit_rep_F (y := w.val) w.2
  obtain ⟨U, hU⟩ := exists_unit_of_zval_eq_zero hzu
  obtain ⟨T, hT⟩ := exists_unit_of_zval_eq_zero (zval_twoUnitF)
  -- 剩余层的相关性（一般形：`A ≡ W'^j · 立方` ⟹ `kc A = j • kc W'`）
  have key : ∀ (A B W' : (↥𝒪[LaurentSeries (ZMod 7)])ˣ) (j : ZMod 3),
      unitsResidue A = (unitsResidue B) ^ 3 * (unitsResidue W') ^ (j.val : ℕ) →
      KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
        (unitsToF A)
        = j • KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
            (unitsToF W') := by
    intro A B W' j hAB
    have hres : unitsResidue (A * (W' ^ (j.val : ℕ))⁻¹) = (unitsResidue B) ^ 3 := by
      rw [map_mul, map_inv, map_pow, hAB]
      group
    have hzero := kc_eq_zero_of_residue_cube (A * (W' ^ (j.val : ℕ))⁻¹) B hres
    rw [map_mul, KummerV.kummerClass_mul, map_inv, map_pow, kc_inv, kummerClass_pow] at hzero
    rw [add_eq_zero_iff_eq_neg, neg_neg] at hzero
    have hcast : (j.val : ℕ) • KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3
        three_isUnit_laurentSeries (unitsToF W')
        = j • KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
            (unitsToF W') := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 3), ZMod.natCast_val, ZMod.cast_id]
    rw [hcast] at hzero
    exact hzero
  rcases residue_dependent U T with ⟨j, V, hV⟩ | ⟨j, V, hV⟩
  · -- 左支：`U ≡ T^j · 立方`
    refine ⟨j, ?_⟩
    refine Subtype.ext ?_
    show j • KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
      twoUnitF = w.val
    rw [← hkcu, ← hU, ← hT]
    exact (key U V T j hV).symm
  · -- 右支：`T ≡ U^j · 立方`（取 `j⁻¹`；`j = 0` 会给出 `kc 2 = 0`，排除）
    have hkey := key T V U j hV
    rw [hT, hU] at hkey
    by_cases hj : j = 0
    · rw [hj, zero_smul] at hkey
      exact absurd hkey kc_two_ne_zero_G
    · refine ⟨j⁻¹, ?_⟩
      refine Subtype.ext ?_
      show j⁻¹ • KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3
        three_isUnit_laurentSeries twoUnitF = w.val
      rw [← hkcu, hkey, smul_smul, inv_mul_cancel₀ hj, one_smul]

/-- ★★★★★★ **`hK1`**：`finrank (ZMod 3) ↥(ker (valLinOf v hp)) = 1`（论文 4.4 的载体条件）。 -/
theorem hK1_F :
    Module.finrank (ZMod 3) ↥(LinearMap.ker (valLinOf
      (F := LaurentSeries (ZMod 7)) (p := 3)
      (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries)) = 1 := by
  have hle := finrank_ker_valLinOf_le_one
  have hpos := finrank_ker_valLinOf_pos
  omega

/-- ★★★★★★★ **论文 4.4（`cor:rank-barrier`）在 `𝔽₇((t))`／`p = 3` 上无条件成立**
（`L1` 非空实例义务满足；`hK1` 由 `Hyp373.hK1_F` 供给）。 -/
-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_F :
    Module.finrank (ZMod 3)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := LaurentSeries (ZMod 7)) (p := 3))
          (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
            three_isUnit_laurentSeries twoUnitF)
          (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
            three_isUnit_laurentSeries (pi : (LaurentSeries (ZMod 7))ˣ))).range = 2
      ∧ Module.finrank (ZMod 3)
        (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup (LaurentSeries (ZMod 7))) (ZMod 3)) = 2 :=
  corollary_4_4_F_of_hK1 hK1_F

end FqXt
end L20261018

#print axioms L20261018.FqXt.finrank_ker_valLinOf_le_one
#print axioms L20261018.FqXt.hK1_F
#print axioms L20261018.FqXt.corollary_4_4_F
