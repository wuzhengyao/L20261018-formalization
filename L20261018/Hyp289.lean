import Hyp288
import Hyp162

/-!
# R1172（**第 4 章收口：四条定理的 `hfacts` 已消去，唯一假设 = `UnitsCupVanish`**）

## 本轮做什么

`Hyp162` 把第 4 章的四条定理（4.1／4.2／4.3(1)／4.4）写成「`D` 作输入」或「`hfacts` 作输入」
的条件定理。R1170 消去了 (R1) 的两载体接线，R1171 把 (R2) 压成单条具名假设
`UnitsCupVanish`（[[hyp-units-cup-vanish]]）并机检了 `GaloBase` 载体的 `TameResidueFacts`。

**本轮把这最后一步接上**：把 `Hyp162` 三条定理的 `hfacts` 输入换成
`tameResidueFacts_Galo_of_units_cup` 的输出 ⟹ **第 4 章的四条在一般 Hensel 下成立，
唯一假设是 `UnitsCupVanish`**（外加 `∅-bridge` `hbridge` 与论文自身的 §2.4 假设）。

## 为什么这一轮值得单独做

「唯一残余是一条具名假设」这句话，只有**把下游定理在无 `hfacts` 的形态下重新机检**之后
才成立：否则 `hfacts` 仍是接口上的一个洞。本轮的三个定理是第 4 章的**最终形态**
（`Hyp162` 的版本保留为中间层，便于单独调用）。

## 本轮

| 声明 | 对照 `Hyp162` |
|---|---|
| **`orth_eq_bot_of_discrete_valuation'`** | 4.2（`lem:ramified-vanishing`），`hfacts` 已消 |
| **`thm_ramified_1_of_discrete_valuation'`** | 4.3(1)，`hfacts` 已消 |
| **`corollary_4_4_of_discrete_valuation'`** | 4.4（`cor:rank-barrier`），`hfacts` 已消 |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section PaperLevel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]

/-- **4.2（`lem:ramified-vanishing`）—— `hfacts` 已消**：唯一假设 = `UnitsCupVanish`。

对照 `Hyp162.orth_eq_bot_of_discrete_valuation`：`hfacts` 一行被
`tameResidueFacts_Galo_of_units_cup` 取代，其输入逐条是论文自身的 Hensel 层级。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_of_discrete_valuation' {ζ : F} {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0)
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_Galo_of_units_cup (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hbridge hv hπ hp2 hUU)

/-- **4.3(1) —— `hfacts` 已消**：`U^⊥ = N = 0`，唯一假设 = `UnitsCupVanish`。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_of_discrete_valuation' {ζ : F} {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0)
    (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
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
  thm_ramified_1_of_discrete_valuation (F := F) (p := p) Δ hpF hp2 hroots hU v hπ
    (tameResidueFacts_Galo_of_units_cup (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hbridge hv hπ hp2 hUU)
    ha1 ha2 hne hval

/-- **4.4（`cor:rank-barrier`）—— `hfacts` 已消**：`d_K = 1`（`hK1`，论文假设）⟹
`rank Φ = 2 ∧ d_F = 2`，唯一假设 = `UnitsCupVanish`。 -/
-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_of_discrete_valuation' {ζ : F} {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0)
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
    (tameResidueFacts_Galo_of_units_cup (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hbridge hv hπ hp2 hUU)
    hne hval hK1

end PaperLevel

end L20261018

#print axioms L20261018.orth_eq_bot_of_discrete_valuation'
#print axioms L20261018.thm_ramified_1_of_discrete_valuation'
#print axioms L20261018.corollary_4_4_of_discrete_valuation'
