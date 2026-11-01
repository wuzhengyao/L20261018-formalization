import L20261018.Hyp331

/-!
# R1238（S34 第 10 轮）：**论文 4.2 在 `ℚ_[7]`／`p = 3` 上的 `L1` 见证**

`Hyp321.orth_eq_bot_noBridge`（4.2 `lem:ramified-vanishing`，零 `hbridge`、无完备性）
的**假设类终于全部落地**：

| 假设 | 本文件供给 |
|---|---|
| `[ValuativeRel] [TopologicalSpace] [HenselianRing] [Finite (ResidueField)] [IsDiscreteValuationRing]` | mathlib 自动实例（`ℚ_[7]`） |
| `HasEnoughRootsOfUnity ℚ_[7] 3` | `Hyp324.hasEnoughRootsOfUnity_Q7_three` |
| `hζ : IsPrimitiveRoot ζ 3` | `zeta3`／`zeta3_spec` |
| `hp`／`hpF` | `three_isUnit_O`／`three_isUnit_F` |
| `v`／`hv : ValCompat v`／`hπ : v π = 1` | `vCompatHom`／`valCompat_of_dvr`／`q7Pi` |
| `[Fact (Irreducible …)]`／`[Module.Finite …]` | `q7Pi` 的 Capelli ＋ `moduleFinite_adjoinRoot` |
| **`hne : GaloBase.cup a₁ a₂ ≠ 0`** | ★ `hne_Q7`（`Hyp331` 的路，打包） |
| **`hval : ∃ u ∈ plane, v̄ u ≠ 0`** | ★ `hval_Q7`（取 `u = a₂`，用 `(R1-σ)` ＋ `val_pi = 1`） |
| `[FiniteDimensional (ZMod 3) (GaloBase.V)]` | ★ `Hyp330.finiteDimensional_galoBaseV_Q7` |

⟹ **`ResidueCupData.orth (GaloBase.cup) a₁ a₂ = ⊥`** 在真实局部域上机检成立
（这是 4.2 的 `L1` 非空见证：假设类可满足且结论随之成立）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section Q7

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity ℚ_[7] 3 := hasEnoughRootsOfUnity_Q7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- 取定的一致化元（`zval = 1` 且非立方）。 -/
noncomputable def q7Pi : ℚ_[7]ˣ :=
  (exists_uniformizer_not_pow (F := ℚ_[7]) (p := 3) (Fact.out : Nat.Prime 3).ne_one).choose

theorem q7Pi_zval : zval (F := ℚ_[7]) q7Pi = 1 :=
  (exists_uniformizer_not_pow (F := ℚ_[7]) (p := 3) (Fact.out : Nat.Prime 3).ne_one).choose_spec.1

theorem q7Pi_notpow : ∀ c : ℚ_[7], c ^ 3 ≠ (q7Pi : ℚ_[7]) :=
  (exists_uniformizer_not_pow (F := ℚ_[7]) (p := 3) (Fact.out : Nat.Prime 3).ne_one).choose_spec.2

theorem q7Pi_hπ : vCompatHom (F := ℚ_[7]) q7Pi = Multiplicative.ofAdd (1 : ℤ) := by
  rw [show vCompatHom (F := ℚ_[7]) q7Pi
    = Multiplicative.ofAdd (zval (F := ℚ_[7]) q7Pi) from rfl, q7Pi_zval]

instance q7Pi_irred : Fact (Irreducible (X ^ 3 - C (q7Pi : ℚ_[7]))) :=
  ⟨(capelli_irreducible_iff (F := ℚ_[7]) (p := 3) (by decide)).mpr q7Pi_notpow⟩

instance q7Pi_fin : Module.Finite ℚ_[7] (AdjoinRoot (X ^ 3 - C (q7Pi : ℚ_[7]))) :=
  moduleFinite_adjoinRoot (p := 3) (q7Pi : ℚ_[7])

/-- 取定的 `HenselResidueData`（由 `Hyp321` 的无 `hbridge` 版给出）。 -/
noncomputable def q7D :
    HenselResidueData (ZMod 3)
      ↑(continuousCohomology 1 (ClassFieldTheory.muNRep 3 ℚ_[7])).toModuleCat
      ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep 3 ℚ_[7])).toModuleCat
      ↥(LinearMap.ker (valH1LinearGen (p := 3) vCompatHom three_isUnit_F))
      ((ClassFieldTheory.kummerCupPairing zeta3 zeta3_spec).cup 1 1) :=
  (exists_henselResidueData_noBridge (F := ℚ_[7]) (p := 3)
    (v := vCompatHom) (π := q7Pi) zeta3_spec three_isUnit_O three_isUnit_F
    valCompat_of_dvr q7Pi_hπ (by decide) (kummerCup_skew zeta3_spec)).choose

theorem q7D_val :
    q7D.val = valH1LinearGen (p := 3) vCompatHom three_isUnit_F :=
  (exists_henselResidueData_noBridge (F := ℚ_[7]) (p := 3)
    (v := vCompatHom) (π := q7Pi) zeta3_spec three_isUnit_O three_isUnit_F
    valCompat_of_dvr q7Pi_hπ (by decide) (kummerCup_skew zeta3_spec)).choose_spec

/-- 非零核元 `kc_T 2`。 -/
noncomputable def xQ7 : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep 3 ℚ_[7])).toModuleCat :=
  ClassFieldTheory.kummerClass ℚ_[7] three_isUnit_F twoUnit

theorem xQ7_ne_zero : xQ7 ≠ 0 := kc_two_ne_zero_muNRep_Q7

/-- 杯积的两根：`a₁ = redEquiv1⁻¹ (kc_T 2)`、`a₂ = redEquiv1⁻¹ π`。 -/
noncomputable def a1Q7 : GaloBase.V ℚ_[7] 3 := (H2Bridge.redEquiv1 zeta3_spec).symm xQ7

noncomputable def a2Q7 : GaloBase.V ℚ_[7] 3 := (H2Bridge.redEquiv1 zeta3_spec).symm q7D.pi

/-- ★★★★★ **`hne`**：`GaloBase.cup a₁ a₂ ≠ 0`。 -/
theorem hne_Q7 : GaloBase.cup (K := ℚ_[7]) (p := 3) a1Q7 a2Q7 ≠ 0 := by
  have hxval : q7D.val xQ7 = 0 := by
    rw [q7D_val]
    show valH1Gen (p := 3) vCompatHom three_isUnit_F xQ7 = 0
    rw [show xQ7 = ClassFieldTheory.kummerClass ℚ_[7] three_isUnit_F twoUnit from rfl,
      valH1Gen_kummerClass]
    have hz : zval (F := ℚ_[7]) twoUnit = 0 := zval_unit_eq_zero (F := ℚ_[7]) two_isUnit_O
    rw [show vCompatHom (F := ℚ_[7]) twoUnit
      = Multiplicative.ofAdd (zval (F := ℚ_[7]) twoUnit) from rfl, hz]
    simp
  obtain ⟨y, hy⟩ := (exact_infl_val q7D xQ7).mp hxval
  have hyne : y ≠ 0 := by
    intro h0
    exact xQ7_ne_zero (by rw [← hy, h0, map_zero])
  have hcupT : ((ClassFieldTheory.kummerCupPairing zeta3 zeta3_spec).cup 1 1) xQ7 q7D.pi ≠ 0 := by
    intro h0
    have h1 := q7D.tame_u_pi y
    rw [hy, h0, map_zero] at h1
    exact hyne h1.symm
  intro h0
  have h1 := congrArg (H2Bridge.redEquiv zeta3_spec) h0
  simp only [map_zero, H2Bridge.redEquiv_cup, a1Q7, a2Q7, AddEquiv.apply_symm_apply] at h1
  exact hcupT h1

/-- ★★★★★ **`hval`**：`a₂ ∈ plane a₁ a₂` 且 `v̄ a₂ ≠ 0`（用 `(R1-σ)` ＋ `val_pi = 1`）。 -/
theorem hval_Q7 :
    ∃ u ∈ ResidueCupData.plane (k := ZMod 3) a1Q7 a2Q7,
      valLinOf (F := ℚ_[7]) (p := 3) vCompatHom three_isUnit_F u ≠ 0 := by
  obtain ⟨c, hc0, hsc⟩ := scaled_bridge_uncond (F := ℚ_[7]) (p := 3) three_isUnit_F zeta3_spec
  refine ⟨a2Q7, Submodule.subset_span (by simp), ?_⟩
  intro hzero
  have hkey := valH1LinearGen_redEquiv1_smul (F := ℚ_[7]) (p := 3) zeta3_spec
    vCompatHom three_isUnit_F c hsc a2Q7
  rw [hzero, smul_zero] at hkey
  have hfun : ⇑(q7D.val) = ⇑(valH1LinearGen (p := 3) vCompatHom three_isUnit_F) := by
    rw [q7D_val]
  have hpv : valH1LinearGen (p := 3) vCompatHom three_isUnit_F q7D.pi = 1 := by
    rw [← hfun]
    exact q7D.val_pi
  have hsymm : (H2Bridge.redEquiv1 zeta3_spec) a2Q7 = q7D.pi :=
    AddEquiv.apply_symm_apply _ _
  have hvpi : valH1LinearGen (p := 3) vCompatHom three_isUnit_F
      ((H2Bridge.redEquiv1 zeta3_spec) a2Q7) = 1 := by
    rw [hsymm]
    exact hpv
  rw [hvpi] at hkey
  exact one_ne_zero hkey

/-- ★★★★★★ **论文 4.2（`lem:ramified-vanishing`）在 `ℚ_[7]`／`p = 3` 上成立**
（`L1` 非空见证：假设类可满足，结论随之机检成立）。 -/
theorem orth_eq_bot_Q7 :
    ResidueCupData.orth (GaloBase.cup (K := ℚ_[7]) (p := 3)) a1Q7 a2Q7 = ⊥ :=
  orth_eq_bot_noBridge (F := ℚ_[7]) (p := 3) (v := vCompatHom) (π := q7Pi)
    (ζ := zeta3) zeta3_spec three_isUnit_O three_isUnit_F valCompat_of_dvr q7Pi_hπ
    (by decide) ⟨by decide⟩ hne_Q7 hval_Q7

end Q7

end L20261018

#print axioms L20261018.hne_Q7
#print axioms L20261018.hval_Q7
#print axioms L20261018.orth_eq_bot_Q7
