import L20261018.Ch4.Step033_ch4_three_and_exists_d
import L20261018.Ch2.Hensel.ResidueMap.Step035_hens_residue_data_no_finite

/-!
# R1251（S35 入口 B）：把 `[Finite (ResidueField)]` 换成论文的 `∂₂` 两条性质

S34 的 `Hyp321` 三条（4.2／4.3(1)／4.4）与 `Hyp323` 的 `∃D` 都带
`[Finite (IsLocalRing.ResidueField ↥𝒪[F])]` —— 这是**论文没有的假设**
（论文第 4 章只用 `prop:prelim-residue` (1) 的两条：`∂₂(inf ξ)=0`、`∂₂(inf η ∪ (π))=η`）。

本轮把该假设换成 `d` 的两条性质（`Hyp338.tameResidueFacts_of_residueMap`
的 Galo 载体实例化），并把 `d` 沿签名上传：

* `tameResidueFacts_Galo_of_residueMap` —— `(R1)∧(R2)` 由 `d` 的两条性质给出（无有限剩余域）；
* `orth_eq_bot_noFinite` —— 4.2；
* `thm_ramified_1_noFinite` —— 4.3(1)；
* `corollary_4_4_noFinite` —— 4.4；
* `exists_henselResidueData_noFinite'` —— `muNRep` 载体的 `∃D`（`hskew` 也由
  `Hyp323.kummerCup_skew` 消去）。

旧版（带 `[Finite (ResidueField)]`）保留作回归对照：`Hyp332`／`Hyp336`／`Hyp337`
在 `ℚ_[7]` 上仍走旧版。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section NoFinite

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- `VK`（Galo 载体）：`ker v̄`（必须 `abbrev`，否则实例搜索无法展开）。 -/
noncomputable abbrev VKG (F : Type) [Field F] (p : ℕ) [NeZero p] [Fact p.Prime]
    [HasEnoughRootsOfUnity F p]
    (v : Fˣ →* Multiplicative ℤ) (hpF : IsUnit (p : F)) : Type :=
  ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hpF))

/-- ★★★★★★ **`TameResidueFacts` 由 `∂₂` 的两条性质推出**（Galo 载体，无 `[Finite (ResidueField)]`）。

`infl` 取 `ker v̄ ↪ V` 的子类型包含（`prop:prelim-kummer-valuation` 的满射性自动成立）。

出处（`S62-GS2017-CROSSCHECK.md`）：GS **6.8.8**（印版 p207 `Corollary 6.8.8` 分裂正合序列）
＋ 其 `Prop 6.8.7` 的证明（$s^i_\pi(\operatorname{Inf}(b))=\partial^{i+1}_v((-\pi)\cup b)$、
$\partial^1_v((-\pi))=1$）给出 `hd_cup_pi`；`∂(Inf(ξ))=0` 是正合性。
⚠ 本地 `GilleSzamuely2017.tex` 是**异版**（其 6.8.7/6.8.8 编号与印版不同）⟹ 下面的 `@source`
只能挂 tex 的**同内容**条目（cup-product 与剩余映射相容），**印版已目视**（p206–207）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:lemma-residue-cup-product quote="\partial^{p+q}(a\cup\operatorname{Inf}(b))=\partial^{p}(a)\cup b."
theorem tameResidueFacts_Galo_of_residueMap
    (hpF : IsUnit (p : F))
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF)
    (hd_infl : ∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (hd_cup_pi : ∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) :=
  tameResidueFacts_of_residueMap (GaloBase.cup (K := F) (p := p))
    (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)
    (LinearMap.ker (valLinOf (F := F) (p := p) v hpF)).subtype (fun y => y.2)
    (fun x hx => ⟨⟨x, hx⟩, rfl⟩) d hd_infl hd_cup_pi

/-- ★★★★★★ **4.2（`lem:ramified-vanishing`）—— 无 `[Finite (ResidueField)]`**。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_noFinite {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF)
    (hd_infl : ∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (hd_cup_pi : ∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y)
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := v) (π := π)
      hpF d hd_infl hd_cup_pi)

/-- ★★★★★★ **4.3(1) —— 无 `[Finite (ResidueField)]`**。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_noFinite {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF)
    (hd_infl : ∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (hd_cup_pi : ∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y)
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
    (tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := v) (π := π)
      hpF d hd_infl hd_cup_pi)
    ha1 ha2 hne hval

/-- ★★★★★★ **4.4（`cor:rank-barrier`）—— 无 `[Finite (ResidueField)]`**。 -/
-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_noFinite {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF)
    (hd_infl : ∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (hd_cup_pi : ∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y)
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
    (tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := v) (π := π)
      hpF d hd_infl hd_cup_pi)
    hne hval hK1

end NoFinite

section MuNRep

variable {F : Type} [Field F]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★★ **`∃D`（`muNRep` 载体）—— 无 `[Finite (ResidueField)]`、无 `hskew`**。

`Hyp341.exists_henselResidueData_noFinite` 的 `hskew` 由 `Hyp323.kummerCup_skew` 供给。 -/
theorem exists_henselResidueData_noFinite' {ζ : F} {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    (hζ : IsPrimitiveRoot ζ p) (hpF : IsUnit (p : F))
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (d : ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat →ₗ[ZMod p]
      VKern F p v hpF)
    (hd_infl : ∀ y z : VKern F p v hpF,
      d (((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) (y : _) (z : _)) = 0)
    (hd_cup_pi : ∀ y : VKern F p v hpF,
      d (((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) (y : _)
        (ClassFieldTheory.kummerClass F hpF π)) = y) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
        (VKern F p v hpF) ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hpF :=
  exists_henselResidueData_noFinite (F := F) (p := p) hpF hζ hπ
    (kummerCup_skew (F := F) (p := p) hζ) d hd_infl hd_cup_pi

end MuNRep

end L20261018

#print axioms L20261018.tameResidueFacts_Galo_of_residueMap
#print axioms L20261018.orth_eq_bot_noFinite
#print axioms L20261018.thm_ramified_1_noFinite
#print axioms L20261018.corollary_4_4_noFinite
#print axioms L20261018.exists_henselResidueData_noFinite'
