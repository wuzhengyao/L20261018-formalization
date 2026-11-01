import L20261018.Hyp429

/-!
# S62 R22：**4.4 的论文假设层级版** —— 第 4 章最后一块「论文口径」的件

## 为什么需要它

`FRONTIER.md` 的 4.2／4.3(1) 已经有**论文层级**的机检件（`Hyp429.orth_eq_bot_paper`／
`thm_ramified_1_paper`：入口 ＝ `d` ＋ `prop:prelim-residue`(1) 的两条性质
`hd_infl`／`hd_cup_pi`，**无 `[Finite 𝓀]`、无 `MerkurjevSuslin`**），但 **4.4 只有 MS 入口版**
（`corollary_4_4_of_merkurjevSuslin`）。用户已裁定第 4 章不依赖 MS ⟹ 4.4 必须补论文层级版。

## 机检件

| 声明 | 内容 |
|---|---|
| **`corollary_4_4_paper`** | ★★★★★ **4.4（`line:1646` 的推论）在论文精确假设层级**：入口同 `*-paper`（`d` ＋两条性质） |

证明是**纯组装**（零数学）：`corollary_4_4_of_discrete_valuation`（`Hyp162`）
＋ `tameResidueFacts_Galo_of_residueMap`（把 `d` 的两条性质转成 `TameResidueFacts`）。

## 诚实边界

* 不证 `d` 的存在（＝ `prop:prelim-residue`(1)，论文自己证的命题，出处 GS 6.8.8）——
  它作为假设传入，与 `orth_eq_bot_paper`／`thm_ramified_1_paper` 口径一致。
* 不碰 MS（`thm:prelim-ms` 不在第 4 章的依赖里）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section PaperExact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **4.4（§4 末段推论）在论文的精确假设层级**。

假设 = 论文 §4 开头段（Hensel 离散赋值域、`char K ≠ p`、`μ_p ⊂ F`、`v(π)=1`）
＋ **`prop:prelim-residue`(1) 的两条性质**（`hd_infl`／`hd_cup_pi`）
＋ 论文 4.4 自己的两条数值假设（`hK1 : d_K = 1` 的 Lean 形态、`d_F < ∞`）。
**无** `[Finite (ResidueField)]`、**无** `MerkurjevSuslin`。 -/
-- @source file=raw/L20261018.tex locator=line:1646 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_paper {ζ : F} (hζ : IsPrimitiveRoot ζ p)
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
    (hne : Theo352.cupLin (F := F) (p := p)
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
  corollary_4_4_of_discrete_valuation (F := F) (p := p) (a1 := a1) (a2 := a2) hpF v hπ
    (tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := v) (π := π) hpF d hd_infl hd_cup_pi)
    hne hval hK1

end PaperExact

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.corollary_4_4_paper
