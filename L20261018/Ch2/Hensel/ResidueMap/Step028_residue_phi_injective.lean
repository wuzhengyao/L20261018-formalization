import L20261018.Ch2.Hensel.ResidueMap.Step027_norm_group_form
import L20261018.Ch2.Hensel.Valuation.Step003_r1_norm_form
import L20261018.Ch2.Hensel.Valuation.Step002_principal_units_without_completeness

/-!
# R1054（**S29 · ④.2 收口 —— (R1) 机检**）：`residuePhi` 单射

本文件把前面四件拼成 **(R1)** 本身：

```
Function.Injective (residuePhi (GaloBase.cup) (valLinOf v hp) ((π)))
```

`Hyp161.TameResidueFacts.phi_injective` 由此**从假设变定理**（`tameResidueFacts_of_norm_form`：
只剩 `disjoint` ＝ (R2) 作为输入）。

## 路线（每步都已机检）

1. **`Hyp163.residuePhi_injective_iff_kummer`**：(R1) ⟺「`v`-整单位 `u`：`(u)∪(π) = 0 ⟹ (u) = 0`」；
2. **`Hyp164.residuePhi_injective_iff_norm_of_bridge`**：再 ⟺ 范数形态
   「`u ∈ N_{L/F}(Lˣ) ∩ 𝒪_Fˣ ⟹ u ∈ F^{×p}`」，**以载体桥 `hbridge` 为唯一接口假设**；
3. **`Hyp200.mem_pow_of_mem_normGroup_of_valOfUnitOf_eq_zero`**：范数形态**已机检**
   （＝ `Hyp197` 整性判据 ＋ `Hyp198` Hensel ＋ `Hyp199` 模 `p` 归约）；
4. **`adjoin_root_eq_top`**：`F⟮root⟯ = ⊤`（`AdjoinRoot.adjoinRoot_eq_top` ＋ `mem_adjoin_simple_iff`）；
5. `hs : rootᵖ = algebraMap F L π`（`Hyp174.root_pow_eq_of`）。

## 残余（诚实记账）

| 项 | 性质 | 处置 |
|---|---|---|
| **`hbridge`** | **载体身份**（两套 `H¹` 载体上 Tame Kummer 类的相等），**不是数学缺口** | 登记为 `∅-bridge`；R1016 实测**不是 `rfl`**（三层等价链的复合 vs `muNRepH1Equiv`） |
| `[Fact (Irreducible (Xᵖ − Cπ))]` | 模型是域 ⟸ `π ∉ Fᵖ` | DVF 中由 `v(π)=1` 自动成立（`π = aᵖ ⟹ 1 = p·v(a)` 在 `ℤ` 中不可能）；Capelli 判据为独立基建项 |
| `[HenselianRing 𝒪_F 𝔪]`／`p` 可逆／`HasEnoughRootsOfUnity`／`hζ` | **论文自身假设**（§2.4 的 Hensel 性、`\char K 
e p`、`μ_p ⊂ F`） | 不是缺口 |
| `disjoint` | (R2) | 见 `⑦` 的 go/no-go |

## 非空性（L1／L10①）

假设类非空：`ValCompat` 由 `Hyp189`（任一完备局部域）、`v π = 1` 由 `TauCeti.exists_isUniformizer`、
`ValCompat`＋`hbridge`＋`hζ` 在 `F = ℚ_p`（`p` 奇）上逐条成立。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section Final

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ} {ζ : F}

/-- `F⟮s⟯ = ⊤`（模型 `L = AdjoinRoot(Xᵖ − Cπ)`、`s = root`）。 -/
theorem adjoin_root_eq_top [Fact (Irreducible (X ^ p - C (π : F)))] :
    IntermediateField.adjoin F
      ({AdjoinRoot.root (X ^ p - C (π : F))} : Set (AdjoinRoot (X ^ p - C (π : F)))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [IntermediateField.mem_adjoin_simple_iff]
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨q, 1, ?_⟩
  rw [map_one, div_one, AdjoinRoot.aeval_eq]

/-- **`(R1)`：`residuePhi` 单射**（以载体桥 `hbridge` 为唯一接口假设）。 -/
theorem residuePhi_injective_of_norm_form
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hpF a) = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine (residuePhi_injective_iff_norm_of_bridge (F := F) (p := p) hpF hζ v π hbridge
    (L := AdjoinRoot (X ^ p - C (π : F)))
    (s := AdjoinRoot.root (X ^ p - C (π : F)))
    ?_ (adjoin_root_eq_top (F := F) (p := p) (π := π))).mpr ?_
  · rw [root_pow_eq_of]
    rfl
  · intro u hval hmem
    exact mem_pow_of_mem_normGroup_of_valOfUnitOf_eq_zero (F := F) p hp hv hπ hp2 hval hmem

/-- **`TameResidueFacts` 的 `phi_injective` 从假设变定理**：只剩 `disjoint`（＝(R2)）作为输入。 -/
theorem tameResidueFacts_of_norm_form
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hpF a) = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hdisjoint : Disjoint
      (LinearMap.range (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)))
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF))) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) where
  phi_injective := residuePhi_injective_of_norm_form (F := F) p hp hpF hζ hbridge hv hπ hp2
  disjoint := hdisjoint

end Final

end L20261018

#print axioms L20261018.adjoin_root_eq_top
#print axioms L20261018.residuePhi_injective_of_norm_form
#print axioms L20261018.tameResidueFacts_of_norm_form


