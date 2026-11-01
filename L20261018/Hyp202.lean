import L20261018.Hyp201
import L20261018.Hyp167

/-!
# R1055（**S29 · ④.2 收口（去假设）**）：模型域性从假设变定理

`Hyp201` 的 `(R1)` 收口还带两条**非论文**假设；本文件把两条都**机检消掉**：

| 假设 | 处置 |
|---|---|
| `[Fact (Irreducible (Xᵖ − Cπ))]`（模型是域） | **`Hyp167.irreducible_X_pow_sub_C_uniformizer`**（`X_pow_sub_C_irreducible_of_odd` ＋ `v(π)=1 ⟹ π ∉ Fᵖ`）⟹ `haveI` 就地供给 |
| `[Module.Finite F (AdjoinRoot …)]` | **`Hyp193.finite_adjoinRoot_uniformizer_f`** ⟹ `haveI` 就地供给 |

⟹ **(R1) 的假设类收缩为**：`[HenselianRing 𝒪_F 𝔪]`（论文 Hensel 性）、`p` 在 `𝒪_F`／`F` 中可逆
（`char K ≠ p`）、`μ_p ⊂ F`（`HasEnoughRootsOfUnity` ＋ `hζ`）、`ValCompat` ＋ `v(π)=1`（DVF 数据）、
`p ≠ 2`（论文「`p` 为奇素数」）—— **全部是论文自身的假设** —— 外加**唯一一条载体桥 `hbridge`**（`∅-bridge`）。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section FinalNoFact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ} {ζ : F}

-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_q\bigl(\mathrm{inf}(\eta)\cup(\pi)\bigr)=\eta,\partial_q(\mathrm{inf}(\xi))=0."
/-- **`(R1)`（无「模型是域」假设）**：`residuePhi` 单射。 -/
theorem residuePhi_injective_of_norm_form' [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hpF a) = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)) := by
  haveI : Fact (Irreducible (X ^ p - C (π : F))) :=
    ⟨irreducible_X_pow_sub_C_uniformizer (F := F) p v hπ hp2⟩
  haveI : Module.Finite F (AdjoinRoot (X ^ p - C (π : F))) :=
    finite_adjoinRoot_uniformizer_f (F := F) p π
  exact residuePhi_injective_of_norm_form (F := F) p hp hpF hζ hbridge hv hπ hp2

-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_q\bigl(\mathrm{inf}(\eta)\cup(\pi)\bigr)=\eta,\partial_q(\mathrm{inf}(\xi))=0."
/-- **`TameResidueFacts`（无「模型是域」假设）**：`phi_injective` 已证，只剩 `disjoint` ＝ (R2)。 -/
theorem tameResidueFacts_of_norm_form' [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
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
  phi_injective := residuePhi_injective_of_norm_form' (F := F) p hp hpF hζ hbridge hv hπ hp2
  disjoint := hdisjoint

end FinalNoFact

end L20261018

#print axioms L20261018.residuePhi_injective_of_norm_form'
#print axioms L20261018.tameResidueFacts_of_norm_form'
