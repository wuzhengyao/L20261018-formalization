import L20261018.Ch2.Hensel.ResidueMap.Step042_residue_span_subset_ker_res
import L20261018.Ch4.Step037_ch4_without_finite_dimensional_v
import L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface

/-!
# S39 第 5 轮（B 第 1 步）：**把 B 归约成一条 `Disjoint`**（`Hyp431`）

## 本步的发现

`Hyp389.exists_residueMap_of_faithfulR2` 的第二个参数 `HK2` 是**任意类型**（`{HK2 : Type u_1}`
＋ `[AddCommGroup] [Module (ZMod p)]` ＋ `(infl₂ : HK2 →ₗ H2)`）。⟹ **不需要真的把 `H²(K)` 建成对象**：
取

```
HK2    := ↥(residueSpan (GaloBase.cup F p) (valLinOf v hpF))
infl₂  := (residueSpan …).subtype
```

则 **R2a**（`residueSpan ≤ infl₂.range`）由 `Submodule.range_subtype` **平凡成立**，只剩 **R2′**：

```
Disjoint (residuePhi cup val (π)).range (residueSpan cup val)
```

⟹ **B 的全部剩余内容 = 这一条 `Disjoint`**（`im(∪·π) ∩ span{y∪z : y,z ∈ ker v̄} = ⊥`）。
「载体层」问题（建 `H²(K)` 对象）**被绕开**，不是被解决。

## 机检件

| 件 | 内容 |
|---|---|
| **`exists_residueMap_of_disjoint`** | ★★★★★ `Disjoint ⟹ ∃ d`（两条值性质） |
| **`tameResidueFacts_of_disjoint`** | `Disjoint ⟹ TameResidueFacts`（喂 `Hyp342` 的 Galo 载体版） |
| **`orth_eq_bot_of_disjoint`** | ★★★★★ **4.2**：Hensel ＋ `Disjoint`，无有限残域、无有限维、无 `UnitsCupVanish` |
| **`thm_ramified_1_of_disjoint`** | ★★★★★ **4.3(1)**：同上 |

⟹ B 的单点残余：`Disjoint (residuePhi …).range (residueSpan …)`，即 GS 6.8.5／6.8.8 的
`∂₂` 两条值公式（`∂₂(y∪z)=0`、`∂₂(y∪π)=y`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section DisjointReduction

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **`Disjoint ⟹ ∃ d`**（两条值性质）。

取 `HK2 := ↥(residueSpan …)`、`infl₂ := subtype`：R2a 由 `Submodule.range_subtype` 平凡成立，
故 `Hyp389.exists_residueMap_of_faithfulR2` 只剩 `Disjoint` 一个假设。 -/
theorem exists_residueMap_of_disjoint {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hd : Disjoint
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π)).range
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF))) :
    ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
      (∀ y z : VKG F p v hpF,
        d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p)) (z : GaloBase.V F p)) = 0) ∧
      (∀ y : VKG F p v hpF,
        d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p))
          (KummerBridge.kummerClass F p hpF π)) = y) := by
  refine exists_residueMap_of_faithfulR2 (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2
    (HK2 := ↥(residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)))
    (Submodule.subtype _) ?_ ?_
  · rw [Submodule.range_subtype]
  · rw [Submodule.range_subtype]
    exact hd

/-- ★★★★ **`Disjoint ⟹ TameResidueFacts`**（Galo 载体版，喂 `Hyp342`／`Hyp385` 链）。 -/
theorem tameResidueFacts_of_disjoint {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hd : Disjoint
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π)).range
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF))) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) := by
  obtain ⟨d, hd_infl, hd_cup_pi⟩ :=
    exists_residueMap_of_disjoint (F := F) (p := p) (v := v) (π := π) hζ hp hpF hv hπ hp2 hd
  exact tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := v) (π := π)
    hpF d hd_infl hd_cup_pi

/-- ★★★★★ **4.2（`lem:ramified-vanishing`）**：Hensel ＋ **一条 `Disjoint`**；
**无** `[Finite (ResidueField)]`、**无** `FiniteDimensional`、**无** `UnitsCupVanish`。 -/
theorem orth_eq_bot_of_disjoint {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p))
    (hd : Disjoint
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π)).range
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)))
    {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation_nofin (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_of_disjoint (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hv hπ hp2 hd)

/-- ★★★★★ **4.3(1)（`thm:ramified`(1)）**：同上，只多一条 `Disjoint`。 -/
theorem thm_ramified_1_of_disjoint {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p))
    (hd : Disjoint
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π)).range
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)))
    (Δ : Subgroup Fˣ) [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
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
      valLinOf (F := F) (p := p) v hpF u ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hpF hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ :=
  thm_ramified_1_of_discrete_valuation_nofin (F := F) (p := p) hpF hp2 Δ hroots hU
    v hπ (tameResidueFacts_of_disjoint (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hv hπ hp2 hd) ha1 ha2 hne hval

end DisjointReduction

end L20261018

#print axioms L20261018.exists_residueMap_of_disjoint
#print axioms L20261018.tameResidueFacts_of_disjoint
#print axioms L20261018.orth_eq_bot_of_disjoint
#print axioms L20261018.thm_ramified_1_of_disjoint
