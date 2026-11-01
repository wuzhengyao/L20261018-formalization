import L20261018.Hyp383

/-!
# R1299（S37 第 7 轮）：**第 4 章三条定理去掉 `[Finite (ResidueField)]`**

## 背景

`Hyp321` 的 `orth_eq_bot_noBridge`／`thm_ramified_1_noBridge`／`corollary_4_4_noBridge`
（论文第 4 章的 4.2／4.3(1)／4.4，**零假设**版）挂在
`[Finite (IsLocalRing.ResidueField ↥𝒪[F])]` 的 section 下。`Hyp383` 已证明该实例
**只经一处**进来（`unitsCupVanish`，其 `powClassGen_of_hensel:95` 用 `(𝓀[F])ˣ` 的循环性）。

## 本轮

把第 4 章的三条定理**原样重述**在一个**没有 `[Finite (𝓀[F])]`** 的 section 里，
唯一新增输入是具名假设 `UnitsCupVanish`：

| 声明 | 内容 |
|---|---|
| **`orth_eq_bot_general`** | 4.2 `lem:ramified-vanishing`（一般 Hensel DVR，模 `UnitsCupVanish`） |
| **`thm_ramified_1_general`** | 4.3(1) `thm:ramified`(1) |
| **`corollary_4_4_general`** | 4.4 `cor:rank-barrier` |

证明**逐字照抄** `Hyp321` 的对应件，只把 `tameResidueFacts_Galo_noBridge` 换成
`tameResidueFacts_Galo_of_unitsCupVanish`（`Hyp383`）。⟹ 第 4 章不再依赖有限剩余域；
其**非空见证**仍是有限剩余域（`Hyp383.unitsCupVanish_of_finite`，论文两实例
`ℚ_[7]`／`𝔽₇((t))` 均落在其中，见 `Hyp332`／`Hyp362`–`Hyp373`）。

**口径（诚实）**：这是一条**条件**定理链 —— 一般 Hensel DVR 的第 4 章模
`UnitsCupVanish`；无条件的第 4 章仍是有限剩余域版（`Hyp321`，已机检）。
## ⚠ 更正（S37 收尾自审，2026-10-27）：本件的「一般 Hensel」不是论文的忠实推广

`UnitsCupVanish`（单位杯积**字面为零**）⟺ `H²(κ,μ_p) = 0`（推理：`(u) = inf(ū)`（论文
`prop:prelim-kummer-valuation` (1)）＋ 杯积与膨胀相容 ＋ `inf` 单射（GS 6.8.8 分裂正合列））。
故它对有限 `κ` 成立，对 `κ = ℚ`（`F = ℚ((π))`，仍属论文设定）**不成立**。
⟹ 本件是**更强假设**下的条件定理；论文的 (R2) 只要求 `∂₂((u)∪(w)) = 0`（即 `∈ ker ∂₂ = im(inf)`）。
忠实推广须把 `residueSpan = ⊥` 换成 `residueSpan ⊆ ker res`。详见 `RECON-S2.md` 的「更正」节。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section GeneralHensel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★★ **4.2（`lem:ramified-vanishing`），一般 Hensel DVR，模 `UnitsCupVanish`**。 -/
theorem orth_eq_bot_general {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF)
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_Galo_of_unitsCupVanish (F := F) (p := p) hζ hp hpF hv hπ hp2 hUU)

/-- ★★★★★★ **4.3(1)（`thm:ramified`(1)），一般 Hensel DVR，模 `UnitsCupVanish`**。 -/
theorem thm_ramified_1_general {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF)
    (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F,
      x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hpF a1) (KummerBridge.kummerClass F p hpF a2),
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    (Theo352.Bex (F := F) (p := p) hpF hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ :=
  thm_ramified_1_of_discrete_valuation (F := F) (p := p) (Δ := Δ) (hp := hpF) (hp2 := hp2)
    hroots hU v hπ
    (tameResidueFacts_Galo_of_unitsCupVanish (F := F) (p := p) hζ hp hpF hv hπ hp2 hUU)
    ha1 ha2 hne hval

/-- ★★★★★★ **4.4（`cor:rank-barrier`），一般 Hensel DVR，模 `UnitsCupVanish`**。 -/
theorem corollary_4_4_general {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF)
    {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2),
      valLinOf (F := F) (p := p) v hpF (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hpF)) = 1)
    [FiniteDimensional (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    [NeZero (2 : ZMod p)] :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a2)).range = 2
      ∧ Module.finrank (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 :=
  corollary_4_4_of_discrete_valuation (F := F) (p := p) hpF v hπ
    (tameResidueFacts_Galo_of_unitsCupVanish (F := F) (p := p) hζ hp hpF hv hπ hp2 hUU)
    hne hval hK1

end GeneralHensel

end L20261018

#print axioms L20261018.orth_eq_bot_general
#print axioms L20261018.thm_ramified_1_general
#print axioms L20261018.corollary_4_4_general
