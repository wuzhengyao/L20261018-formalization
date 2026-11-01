import L20261018.Hyp319
import L20261018.Hyp302

/-!
# R1226（S34）：**第四章三条 ＋ `∃D` —— 去掉 `hbridge`，且无完备性**

`PROMPT-S34` §① 把 `hΘ` 当作"唯一数学开口"、把载体桥当作"唯一载体开口"。本战役本轮
（`Hyp319`／`Hyp320`）已把两者**同时消去**，走的是**库内已有资产**：

```
Hyp223.t1_closed（R1092，全仓从未被使用）
  ──(Hyp320 去完备性重写)──> t1_closed'
  ──(Hyp207.scaled_bridge_of_bridgeKc)──> (R1-σ)：redEquiv1 kc = c • kc_T
  ──(Hyp207.residuePhi_injective_of_bridgeKc)──> (R1) 在 GaloBase 载体
  ──(Hyp319 的载体运输)──> (R1) 在 muNRep 载体 ＋ (R2) 载体运输
  ──(Hyp288.tameResidueFacts_of_units_cup)──> TameResidueFacts
  ──(Hyp162 三条 ＋ generalHensel_reduction)──> 第四章三条 ＋ ∃D
```

⟹ **`hbridge` 从本章彻底消失**，`hΘ` 也不再被需要。

## 本轮

| 声明 | 内容 |
|---|---|
| **`tameResidueFacts_Galo_noBridge`** | ★ TameResidueFacts（`GaloBase` 载体），无假设 |
| **`exists_henselResidueData_noBridge`** | ★★★★★ **`∃D`（`muNRep` 载体），无 `hbridge`** |
| **`orth_eq_bot_noBridge`** | ★★★★★ **4.2**，无 `hbridge` |
| **`thm_ramified_1_noBridge`** | ★★★★★ **4.3(1)**，无 `hbridge` |
| **`corollary_4_4_noBridge`** | ★★★★★ **4.4**，无 `hbridge` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section ClosureUncond

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **`TameResidueFacts`（`GaloBase` 载体）—— 零假设**（除论文自身的 §2.4 层级）。

(R1) 由 `residuePhi_injective_t1`（无 `hbridge`、无完备性），(R2) 由 `unitsCupVanish`
（`Hyp302`，无假设）＋ 载体运输 `residueSpan_Galo_eq_bot_of_muNRep'`。 -/
-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem tameResidueFacts_Galo_noBridge_of_hζ {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hph : hpF = hζ.neZero'.out.isUnit)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) := by
  subst hph
  have hUU := unitsCupVanish (p := p) hζ hp hζ.neZero'.out.isUnit hp2 hv
  refine tameResidueFacts_of_span_eq_bot ?_ ?_
  · exact residueSpan_Galo_eq_bot_of_muNRep' (F := F) (p := p) (v := v) hζ hζ.neZero'.out.isUnit
      (residueSpan_eq_bot_of_units (p := p) hζ v hζ.neZero'.out.isUnit hπ hUU)
  · exact residuePhi_injective_t1 (F := F) (p := p) (v := v) (π := π) hp hζ hv hπ hp2

/-- ★★★★★ **`TameResidueFacts`（`GaloBase` 载体）—— 任意 `hpF`**。 -/
theorem tameResidueFacts_Galo_noBridge {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) :=
  tameResidueFacts_Galo_noBridge_of_hζ (F := F) (p := p) hζ hp hpF
    (Subsingleton.elim _ _) hv hπ hp2

/-- ★★★★★★ **一般 Hensel 的 `D` 存在 —— 零假设**（`muNRep` 载体，`D.val = v̄`）。

`Hyp288.exists_henselResidueData_of_units_cup` 的 `hbridge` 已被 `residuePhi_injective_muNRep'` 消去。 -/
theorem exists_henselResidueData_noBridge {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x)) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
        ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hpF :=
  (generalHensel_reduction (p := p) v hpF hζ hπ hskew).mpr
    (tameResidueFacts_of_units_cup (p := p) hζ v hpF hπ
      (unitsCupVanish (p := p) hζ hp hpF hp2 hv)
      (residuePhi_injective_muNRep' (F := F) (p := p) (v := v) (π := π) hp hpF hζ hv hπ hp2))

/-- ★★★★★★ **4.2（`lem:ramified-vanishing`）—— 零假设**（Hensel，不完备，无 `hbridge`）。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_noBridge {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_Galo_noBridge (F := F) (p := p) hζ hp hpF hv hπ hp2)

/-- ★★★★★★ **4.3(1) —— 零假设**（`hUU`／`hbridge` 均已消）。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_noBridge {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
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
    (tameResidueFacts_Galo_noBridge (F := F) (p := p) hζ hp hpF hv hπ hp2)
    ha1 ha2 hne hval

/-- ★★★★★★ **4.4（`cor:rank-barrier`）—— 零假设**。 -/
-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_noBridge {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
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
    (tameResidueFacts_Galo_noBridge (F := F) (p := p) hζ hp hpF hv hπ hp2)
    hne hval hK1

end ClosureUncond

end L20261018

#print axioms L20261018.tameResidueFacts_Galo_noBridge
#print axioms L20261018.exists_henselResidueData_noBridge
#print axioms L20261018.orth_eq_bot_noBridge
#print axioms L20261018.thm_ramified_1_noBridge
#print axioms L20261018.corollary_4_4_noBridge
