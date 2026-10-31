import Hyp200
import Hyp201

/-!
# R1061（**S29 · ④.2 收口（缩放版）**）：`(R1)` 只需**缩放**载体桥

## 为什么必须缩放（R970 的同类前例）

`hbridge`（`Hyp164`／`Hyp201`／`Hyp202` 的残余）断言两套 Kummer 类**相等**。但两侧的系数同构
**都不是典范的**：

* 战役侧 `KummerBridge.kummerCoeffLinearEquiv = LinearEquiv.ofFinrankEq _ _ …`（**基的任意选择**）；
* TauCeti 侧 `kummerCoeffEquivMuNRep`／`kummerCoeffAddEquivZMod`，其 docstring 逐字写
  「The isomorphism is **not canonical**; it amounts to a choice of primitive `n`th root of unity in `Kˢ`」
  （`Coefficients.lean:186`）。

R970 已对**另一对** Kummer 类（`bridgeKc` vs `KummerBridge.kummerClass`）判定：两者的两个一维 `ZMod p`-系数识别
**必然相差一个单位标量** `c ∈ (ZMod p)^×` ⟹ 相等**不可证**；正确目标是**缩放版**
`∃ c ≠ 0, bridgeKc a = c • kc a`，且因 `cup (c•x)(c•y) = (c*c) • cup x y`、`c*c ≠ 0`（`ZMod p` 是域），
**杯积消失的等价性不受影响**。

本文件把同一处理用到 `(R1)`：**只需**缩放桥即可收口 —— 数学强度不变（`(R1)` 仍被证明）。

| 声明 | 内容 |
|---|---|
| **`kummerCup_smul_smul`** | `cup 1 1 (c•x) (c•y) = (c*c) • cup 1 1 x y` |
| **`cup_eq_zero_iff_mem_normGroup_of_scaled_bridge`** | 缩放桥版符号–范数判据（杯积形式） |
| **`residuePhi_injective_iff_norm_of_scaled_bridge`** | `(R1)` ⟺ 范数形态（缩放桥版） |
| **`residuePhi_injective_of_norm_form_scaled`** | **`(R1)`：`residuePhi` 单射**（缩放桥 ＋ 论文假设） |
| **`tameResidueFacts_of_scaled_bridge`** | `TameResidueFacts`（`phi_injective` 已证，只剩 `disjoint`） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section PairingScale

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

/-- **杯积的双齐次性**：`cup 1 1 (c•x) (c•y) = (c*c) • cup 1 1 x y`。 -/
theorem kummerCup_smul_smul (hζ : IsPrimitiveRoot ζ p) (c : ZMod p)
    (x y : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat) :
    (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1 (c • x) (c • y)
      = (c * c) • (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1 x y := by
  have h1 : (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1 (c • x)
      = c • ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1 x) := LinearMap.map_smul _ c x
  rw [h1, LinearMap.smul_apply, LinearMap.map_smul, smul_smul]

end PairingScale

section ScaledBridge

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

/-- **符号–范数判据（缩放桥版）**：只需 `redEquiv1 (kc a) = c • kummerClass a`（`c ≠ 0`）。 -/
theorem cup_eq_zero_iff_mem_normGroup_of_scaled_bridge (hp : IsUnit (p : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hp a) = c • ClassFieldTheory.kummerClass F hp a)
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] {s : L} {b : Fˣ}
    (hs : s ^ p = algebraMap F L b) (hgen : IntermediateField.adjoin F {s} = ⊤) (a : Fˣ) :
    GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
        (KummerBridge.kummerClass F p hp b) = 0 ↔ a ∈ normGroup F L := by
  obtain ⟨c, hc0, hc⟩ := hbridge
  rw [cup_eq_zero_iff_redequiv (F := F) (p := p) hp hζ a b, hc a, hc b,
    kummerCup_smul_smul (F := F) (p := p) hζ c, smul_eq_zero]
  have hcc : c * c ≠ 0 := mul_ne_zero hc0 hc0
  simp only [hcc, false_or]
  exact ClassFieldTheory.cup_kummerClass_eq_zero_iff_mem_normGroup (n := p) (K := F) hζ hp a b hs hgen

/-- **`(R1)` ⟺ 范数形态（缩放桥版）**。 -/
theorem residuePhi_injective_iff_norm_of_scaled_bridge (hp : IsUnit (p : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (π : Fˣ)
    (hbridge : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hp a) = c • ClassFieldTheory.kummerClass F hp a)
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] {s : L}
    (hs : s ^ p = algebraMap F L π) (hgen : IntermediateField.adjoin F {s} = ⊤) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π)) ↔
      ∀ u : Fˣ, valOfUnitOf (p := p) v u = 0 → u ∈ normGroup F L →
        u ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  rw [residuePhi_injective_iff_kummer (F := F) (p := p) hp v π]
  constructor
  · intro hk u hu hmem
    refine (KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp u).mp ?_
    refine hk u hu ?_
    exact (cup_eq_zero_iff_mem_normGroup_of_scaled_bridge (F := F) (p := p) hp hζ hbridge
      (b := π) hs hgen u).mpr hmem
  · intro hn u hu hcup
    refine (KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp u).mpr ?_
    refine hn u hu ?_
    exact (cup_eq_zero_iff_mem_normGroup_of_scaled_bridge (F := F) (p := p) hp hζ hbridge
      (b := π) hs hgen u).mp hcup

end ScaledBridge

section Final

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ} {ζ : F}

/-- **`(R1)`（缩放桥版）**：`residuePhi` 单射。 -/
theorem residuePhi_injective_of_norm_form_scaled
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hpF a) = c • ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)) := by
  haveI : Fact (Irreducible (X ^ p - C (π : F))) :=
    ⟨irreducible_X_pow_sub_C_uniformizer (F := F) p v hπ hp2⟩
  haveI : Module.Finite F (AdjoinRoot (X ^ p - C (π : F))) :=
    finite_adjoinRoot_uniformizer_f (F := F) p π
  refine (residuePhi_injective_iff_norm_of_scaled_bridge (F := F) (p := p) hpF hζ v π hbridge
    (L := AdjoinRoot (X ^ p - C (π : F)))
    (s := AdjoinRoot.root (X ^ p - C (π : F)))
    ?_ (adjoin_root_eq_top (F := F) (p := p) (π := π))).mpr ?_
  · rw [root_pow_eq_of]
    rfl
  · intro u hval hmem
    exact mem_pow_of_mem_normGroup_of_valOfUnitOf_eq_zero (F := F) p hp hv hπ hp2 hval hmem

/-- **`TameResidueFacts`（缩放桥版）**：`phi_injective` 已证，只剩 `disjoint` ＝ (R2)。 -/
theorem tameResidueFacts_of_scaled_bridge
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hpF a) = c • ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hdisjoint : Disjoint
      (LinearMap.range (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)))
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF))) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) where
  phi_injective := residuePhi_injective_of_norm_form_scaled (F := F) p hp hpF hζ hbridge hv hπ hp2
  disjoint := hdisjoint

end Final

end L20261018

#print axioms L20261018.kummerCup_smul_smul
#print axioms L20261018.cup_eq_zero_iff_mem_normGroup_of_scaled_bridge
#print axioms L20261018.residuePhi_injective_iff_norm_of_scaled_bridge
#print axioms L20261018.residuePhi_injective_of_norm_form_scaled
#print axioms L20261018.tameResidueFacts_of_scaled_bridge
