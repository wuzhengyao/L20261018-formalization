import Hyp354
import Hyp332

/-!
# R1266（S36 C 项第 8 步之二）：`𝔽₇((t))` 上的 `hne`／`hval`（照 `Hyp331`／`Hyp332` 逐条搬）

`Hyp331`／`Hyp332` 已在 `ℚ_[7]`／`p = 3` 上把论文 4.2 的假设类全部落地。那些证明的
**结构部分**（`ker v̄ = range inf`、`tame_u_pi`、`redEquiv_cup`、`(R1-σ)`）都是**一般域**的，
只有三处是 `ℚ_[7]` 专属的输入，本文件把它们换成 `𝔽₇((t))` 的对应物：

| `ℚ_[7]` 版 | 本文件 |
|---|---|
| `q7Pi`（`Classical.choose`，opaque） | **`pi`**（`= X`，定义层可见，`Hyp353`） |
| `q7Pi_notpow` | **`not_exists_cube_pi`**（`Hyp353`）／**`not_exists_cube_two`**（`Hyp354`） |
| `two_isUnit_O`／`zval_unit_eq_zero` | **`two_isUnit_O`**（本文件，沿 `powerSeriesEquivO`） |
| `hasEnoughRootsOfUnity_Q7_three`／`zeta3` | **`hasEnoughRootsOfUnity_laurentSeries_zmod7_three`**／`HahnSeries.C 2`（`Hyp351`） |

⟹ `D`（`HenselResidueData`）、`x = kc_T 2 ≠ 0`、`hne`、`hval` 在函数域上成立。
**唯一未落地的输入** = `[FiniteDimensional (ZMod 3) (GaloBase.V F 3)]`（见 `HANDOFF`：
需要 `Finite (Fˣ/(Fˣ)³)`，仍是开口），故最终 4.2 的陈述把它留作假设。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
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

/-- 取定的三次本原单位根（`𝔽₇` 中的 `2`，沿常数嵌入搬到 `𝔽₇((t))`）。 -/
noncomputable def zetaF : LaurentSeries (ZMod 7) := HahnSeries.C (2 : ZMod 7)

/-- `ζ` 确为三次本原单位根。 -/
theorem zetaF_spec : IsPrimitiveRoot (zetaF) 3 :=
  isPrimitiveRoot_C_two

/-- `(2 : 𝔽₇((t))) ≠ 0`。 -/
theorem two_ne_zero_laurentSeries : (2 : LaurentSeries (ZMod 7)) ≠ 0 := by
  intro h0
  have e : (2 : LaurentSeries (ZMod 7))
      = HahnSeries.C (Γ := ℤ) (R := ZMod 7) (2 : ZMod 7) := rfl
  rw [e] at h0
  exact (by decide : (2 : ZMod 7) ≠ 0)
    (HahnSeries.C_injective (by rw [h0]; exact (map_zero _).symm))

/-- `2` 作为 `𝔽₇((t))ˣ` 的元素。 -/
noncomputable def twoUnitF : (LaurentSeries (ZMod 7))ˣ :=
  Units.mk0 (2 : LaurentSeries (ZMod 7)) two_ne_zero_laurentSeries

/-- ★★★★ `h`：常数项非零 ⟹ `↥𝒪[F]` 的单位（沿 `powerSeriesEquivO`）。 -/
theorem isUnit_of_constantCoeff_ne_zero {x : ↥𝒪[LaurentSeries (ZMod 7)]}
    (h : PowerSeries.constantCoeff (R := ZMod 7)
      ((powerSeriesEquivO (K := ZMod 7)).symm x) ≠ 0) : IsUnit x := by
  have h' : IsUnit ((powerSeriesEquivO (K := ZMod 7)).symm x) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr h
  simpa using IsUnit.map (powerSeriesEquivO (K := ZMod 7)).toRingHom h'

/-- ★★★★ **`2` 在 `↥𝒪[𝔽₇((t))]` 中可逆**（`Hyp331` 的 `two_isUnit_O`）。 -/
theorem two_isUnit_O : IsUnit (2 : ↥𝒪[LaurentSeries (ZMod 7)]) := by
  have h : (2 : ↥𝒪[LaurentSeries (ZMod 7)]) = twoO := Subtype.ext rfl
  rw [h]
  exact isUnit_of_constantCoeff_ne_zero (by
    rw [symm_twoO]
    exact (by decide : (2 : ZMod 7) ≠ 0))

/-- ★★★★★ **`muNRep` 侧的 `kc (2)` 非零**（由 `2` 不是立方，`Hyp354`）。 -/
theorem kc_two_ne_zero :
    ClassFieldTheory.kummerClass (LaurentSeries (ZMod 7))
      three_isUnit_laurentSeries twoUnitF ≠ 0 := by
  intro hzero
  rw [ClassFieldTheory.kummerClass_eq_zero_iff] at hzero
  rw [TauCeti.powerSubgroup_eq_range_powMonoidHom, MonoidHom.mem_range] at hzero
  obtain ⟨c, hc⟩ := hzero
  refine not_exists_cube_two (c : LaurentSeries (ZMod 7)) ?_
  have h := congrArg (fun u : (LaurentSeries (ZMod 7))ˣ => (u : LaurentSeries (ZMod 7))) hc
  simpa [twoUnitF, powMonoidHom] using h

/-- 取定的 `HenselResidueData`（`Hyp321` 的无 `hbridge` 版）。 -/
noncomputable def FqD :
    HenselResidueData (ZMod 3)
      ↑(continuousCohomology 1 (ClassFieldTheory.muNRep 3 (LaurentSeries (ZMod 7)))).toModuleCat
      ↑(continuousCohomology (1 + 1)
        (ClassFieldTheory.muNRep 3 (LaurentSeries (ZMod 7)))).toModuleCat
      ↥(LinearMap.ker (valH1LinearGen (p := 3)
        (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries))
      ((ClassFieldTheory.kummerCupPairing zetaF zetaF_spec).cup 1 1) :=
  (exists_henselResidueData_noBridge (F := LaurentSeries (ZMod 7)) (p := 3)
    (v := vCompatHom) (π := pi) zetaF_spec three_isUnit_O three_isUnit_laurentSeries
    valCompat_O pi_hπ (by decide) (kummerCup_skew zetaF_spec)).choose

theorem FqD_val :
    FqD.val = valH1LinearGen (p := 3) (vCompatHom (F := LaurentSeries (ZMod 7)))
      three_isUnit_laurentSeries :=
  (exists_henselResidueData_noBridge (F := LaurentSeries (ZMod 7)) (p := 3)
    (v := vCompatHom) (π := pi) zetaF_spec three_isUnit_O three_isUnit_laurentSeries
    valCompat_O pi_hπ (by decide) (kummerCup_skew zetaF_spec)).choose_spec

/-- 非零核元 `kc_T 2`。 -/
noncomputable def xF :
    ↑(continuousCohomology 1
      (ClassFieldTheory.muNRep 3 (LaurentSeries (ZMod 7)))).toModuleCat :=
  ClassFieldTheory.kummerClass (LaurentSeries (ZMod 7)) three_isUnit_laurentSeries twoUnitF

theorem xF_ne_zero : xF ≠ 0 := kc_two_ne_zero

/-- 杯积的两根：`a₁ = redEquiv1⁻¹ (kc_T 2)`、`a₂ = redEquiv1⁻¹ π`。 -/
noncomputable def a1F : GaloBase.V (LaurentSeries (ZMod 7)) 3 :=
  (H2Bridge.redEquiv1 zetaF_spec).symm xF

noncomputable def a2F : GaloBase.V (LaurentSeries (ZMod 7)) 3 :=
  (H2Bridge.redEquiv1 zetaF_spec).symm FqD.pi

/-- ★★★★★ **`hne`**：`GaloBase.cup a₁ a₂ ≠ 0`。 -/
theorem hne_F : GaloBase.cup (K := LaurentSeries (ZMod 7)) (p := 3) a1F a2F ≠ 0 := by
  have hxval : FqD.val xF = 0 := by
    rw [FqD_val]
    show valH1Gen (p := 3) (vCompatHom (F := LaurentSeries (ZMod 7)))
      three_isUnit_laurentSeries xF = 0
    rw [show xF = ClassFieldTheory.kummerClass (LaurentSeries (ZMod 7))
      three_isUnit_laurentSeries twoUnitF from rfl, valH1Gen_kummerClass]
    have hz : zval (F := LaurentSeries (ZMod 7)) twoUnitF = 0 :=
      zval_unit_eq_zero (F := LaurentSeries (ZMod 7)) two_isUnit_O
    rw [show vCompatHom (F := LaurentSeries (ZMod 7)) twoUnitF
      = Multiplicative.ofAdd (zval (F := LaurentSeries (ZMod 7)) twoUnitF) from rfl, hz]
    simp
  obtain ⟨y, hy⟩ := (exact_infl_val FqD xF).mp hxval
  have hyne : y ≠ 0 := by
    intro h0
    exact xF_ne_zero (by rw [← hy, h0, map_zero])
  have hcupT : ((ClassFieldTheory.kummerCupPairing zetaF zetaF_spec).cup 1 1) xF FqD.pi ≠ 0 := by
    intro h0
    have h1 := FqD.tame_u_pi y
    rw [hy, h0, map_zero] at h1
    exact hyne h1.symm
  intro h0
  have h1 := congrArg (H2Bridge.redEquiv zetaF_spec) h0
  simp only [map_zero, H2Bridge.redEquiv_cup, a1F, a2F, AddEquiv.apply_symm_apply] at h1
  exact hcupT h1

/-- ★★★★★ **`hval`**：`a₂ ∈ plane a₁ a₂` 且 `v̄ a₂ ≠ 0`（用 `(R1-σ)` ＋ `val_pi = 1`）。 -/
theorem hval_F :
    ∃ u ∈ ResidueCupData.plane (k := ZMod 3) a1F a2F,
      valLinOf (F := LaurentSeries (ZMod 7)) (p := 3)
        (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries u ≠ 0 := by
  obtain ⟨c, hc0, hsc⟩ := scaled_bridge_uncond (F := LaurentSeries (ZMod 7)) (p := 3)
    three_isUnit_laurentSeries zetaF_spec
  refine ⟨a2F, Submodule.subset_span (by simp), ?_⟩
  intro hzero
  have hkey := valH1LinearGen_redEquiv1_smul (F := LaurentSeries (ZMod 7)) (p := 3)
    zetaF_spec (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries c hsc a2F
  rw [hzero, smul_zero] at hkey
  have hfun : ⇑(FqD.val) = ⇑(valH1LinearGen (p := 3)
      (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries) := by
    rw [FqD_val]
  have hpv : valH1LinearGen (p := 3) (vCompatHom (F := LaurentSeries (ZMod 7)))
      three_isUnit_laurentSeries FqD.pi = 1 := by
    rw [← hfun]
    exact FqD.val_pi
  have hsymm : (H2Bridge.redEquiv1 zetaF_spec) a2F = FqD.pi :=
    AddEquiv.apply_symm_apply _ _
  have hvpi : valH1LinearGen (p := 3) (vCompatHom (F := LaurentSeries (ZMod 7)))
      three_isUnit_laurentSeries ((H2Bridge.redEquiv1 zetaF_spec) a2F) = 1 := by
    rw [hsymm]
    exact hpv
  rw [hvpi] at hkey
  exact one_ne_zero hkey

/-- ★★★★★★ **论文 4.2（`lem:ramified-vanishing`）在 `𝔽₇((t))`／`p = 3` 上成立**
（唯一剩余假设 = 载体维度 `[FiniteDimensional (ZMod 3) (GaloBase.V F 3)]`）。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_F
    [FiniteDimensional (ZMod 3) (GaloBase.V (LaurentSeries (ZMod 7)) 3)] :
    ResidueCupData.orth (GaloBase.cup (K := LaurentSeries (ZMod 7)) (p := 3)) a1F a2F = ⊥ :=
  orth_eq_bot_noBridge (F := LaurentSeries (ZMod 7)) (p := 3)
    (v := vCompatHom) (π := pi) (ζ := zetaF) zetaF_spec three_isUnit_O
    three_isUnit_laurentSeries valCompat_O pi_hπ (by decide) ⟨by decide⟩ hne_F hval_F

end FqXt
end L20261018

#print axioms L20261018.FqXt.kc_two_ne_zero
#print axioms L20261018.FqXt.hne_F
#print axioms L20261018.FqXt.hval_F
#print axioms L20261018.FqXt.orth_eq_bot_F
