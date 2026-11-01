import Hyp800
import Hyp342

/-!
# S78 R2：第 4 章 3 条陈述的 **`d`-假设消除**（`prop:prelim-residue`(1) 已无条件）

## 靶子

第 4 章（`raw/L20261018.tex` §4，`:1554`–`:1651`）的陈述在 `Hyp342` 里已机检，但都吃
`(d : H² →ₗ VKG)` ＋ `hd_infl` ＋ `hd_cup_pi` 三个参数（＝第 2 章 `prop:prelim-residue`(1) 的两条值）。
`Hyp800.exists_residueMap` 已把这三个参数**构造**出来 ⟹ 本件把三参数**从语句里拿掉**。

## 口径（⚠ 与 `Hyp342._noFinite` 的差别，**必须登记**）

`Hyp342` 的版本是**最大一般性**的：`[Field F] [ValuativeRel F] [TopologicalSpace F]
[HenselianRing ↥𝒪[F] …]` ＋ **任意** `v`（配 `ValCompat v`）。
本件额外带 **`[IsNonarchimedeanLocalField F]`** 并把 `v` 固定为 `TauCeti.normalizedValuation F` ——
因为 `Hyp800` 的整条链条建在 `TauCeti` 的**连续上同调**上（`AbsoluteGaloisGroup`／`inertiaLoc`／
`normalizedValuation`／`LocallyCompactSpace` 实例），那套库的载体就是 `IsNonarchimedeanLocalField`
（＝ `IsValuativeTopology` ＋ `LocallyCompactSpace` ＋ `IsNontrivial`，**不含**剩余域有限）。

**⟹ 这是「载体口径差」，不是新数学假设**；补齐它 ＝ 在 `IsValuativeTopology` 层重建
`prop:prelim-residue`，属独立基建任务（`GAP3-PLAN` §25）。

## 交付

| 声明 | 对应论文陈述 |
|---|---|
| **`orth_eq_bot_viaResidue`** | 4.2 `lem:ramified-vanishing`（`:1608`） |
| **`thm_ramified_1_viaResidue`** | 4.3(1) `thm:ramified`（`:1636`） |
| **`corollary_4_4_viaResidue`** | 4.4 `cor:rank-barrier`（`:1648`） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
variable (hcop : p.Coprime q)

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS78R2 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS78R2 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- 技术实例：`μ_pᴵ` 上 `Γ⧸I` 连续作用。 -/
local instance instContSmulMuPInvS78R2 :
    ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) := inferInstance

variable {π : Fˣ}

/-! ## 1 4.2 `lem:ramified-vanishing` -/

/-- ★★★★★★★ **4.2（`lem:ramified-vanishing`）—— 无 `d` 假设**。

`Hyp342.orth_eq_bot_noFinite` 的三参数 `(d, hd_infl, hd_cup_pi)` 由
`Hyp800.exists_residueMap` **构造**（＝ `prop:prelim-residue`(1) 的无条件形）。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_viaResidue (qq : ℕ) [Fact qq.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) qq]
    (hcopq : p.Coprime qq)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hpq' : ¬ ringChar 𝓀[F] ∣ p) (hp2 : p ≠ 2)
    (t : TameModel F)
    (ht : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' t : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers t = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hpF π)))
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ := by
  obtain ⟨d, hd_infl, hd_cup_pi⟩ := exists_residueMap (F := F) (p := p) (q := qq)
    (hcop := hcopq) hpF hpq' hp t ht hgen (pi0 := π) hπ z hδ
  exact orth_eq_bot_noFinite (F := F) (p := p)
    (v := TauCeti.normalizedValuation F) (π := π) hζ hp hpF
    (valCompat_normalizedValuation F) hπ hp2 d hd_infl hd_cup_pi hp2' hne hval

/-! ## 2 4.3(1) `thm:ramified` -/

/-- ★★★★★★★ **4.3(1)（`thm:ramified`）—— 无 `d` 假设**。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_viaResidue (qq : ℕ) [Fact qq.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) qq]
    (hcopq : p.Coprime qq)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hpq' : ¬ ringChar 𝓀[F] ∣ p) (hp2 : p ≠ 2)
    (t : TameModel F)
    (ht : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' t : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers t = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hpF π)))
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
      valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    (Theo352.Bex (F := F) (p := p) hpF hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ := by
  obtain ⟨d, hd_infl, hd_cup_pi⟩ := exists_residueMap (F := F) (p := p) (q := qq)
    (hcop := hcopq) hpF hpq' hp t ht hgen (pi0 := π) hπ z hδ
  exact thm_ramified_1_noFinite (F := F) (p := p)
    (v := TauCeti.normalizedValuation F) (π := π) hζ hp hpF
    (valCompat_normalizedValuation F) hπ hp2 d hd_infl hd_cup_pi Δ hroots hU ha1 ha2 hne hval

/-! ## 3 4.4 `cor:rank-barrier` -/

/-- ★★★★★★★ **4.4（`cor:rank-barrier`）—— 无 `d` 假设**。 -/
-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_viaResidue (qq : ℕ) [Fact qq.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) qq]
    (hcopq : p.Coprime qq)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hpq' : ¬ ringChar 𝓀[F] ∣ p) (hp2 : p ≠ 2)
    (t : TameModel F)
    (ht : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' t : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers t = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hpF π)))
    {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2),
      valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hpF
        (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hpF)) = 1)
    [FiniteDimensional (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    [NeZero (2 : ZMod p)] :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a2)).range = 2
      ∧ Module.finrank (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 := by
  obtain ⟨d, hd_infl, hd_cup_pi⟩ := exists_residueMap (F := F) (p := p) (q := qq)
    (hcop := hcopq) hpF hpq' hp t ht hgen (pi0 := π) hπ z hδ
  exact corollary_4_4_noFinite (F := F) (p := p)
    (v := TauCeti.normalizedValuation F) (π := π) hζ hp hpF
    (valCompat_normalizedValuation F) hπ hp2 d hd_infl hd_cup_pi hne hval hK1

end L20261018

#print axioms L20261018.orth_eq_bot_viaResidue
#print axioms L20261018.thm_ramified_1_viaResidue
#print axioms L20261018.corollary_4_4_viaResidue

