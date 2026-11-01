import L20261018.Hyp343

/-!
# R1253（S35 第 2 轮）：新接口 `d` 的 **`L1` 非空见证**（有限剩余域）

`Hyp342` 把第 4 章三条定理与 `∃D` 的 `[Finite (ResidueField)]` 换成了论文
`prop:prelim-residue` (1) 的 `d` 两条性质。按 `L1` 义务，新假设类必须给出**机检的非空见证**（`ℚ_[7]` 的具体实例见 `Hyp332` 的 `q7D`）：

1. **一般有限剩余域情形**：`(R1)∧(R2)`（`Hyp321` 已机检）＋ `Hyp343` 的反向等价
   ⟹ `∃ d`（Galo 载体，两条性质）；

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_residueMap_of_finite`** | ★★★★ 有限剩余域 ⟹ `∃ d`（Galo 载体，两条性质） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section FiniteCase

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

-- @source file=raw/L20261018.tex locator=line:1023 quote="\partial_q\bigl(\mathrm{inf}(\eta)\cup(\pi)\bigr)=\eta,\partial_q(\mathrm{inf}(\xi))=0."
/-- ★★★★ **有限剩余域 ⟹ `∃ d`（论文 `prop:prelim-residue` (1) 的两条性质）**，Galo 载体。 -/
theorem exists_residueMap_of_finite {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
      (∀ y z : VKG F p v hpF,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0) ∧
      (∀ y : VKG F p v hpF,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
          (KummerBridge.kummerClass F p hpF π)) = y) := by
  have hfacts := tameResidueFacts_Galo_noBridge (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2
  exact (exists_residueMap_iff_tameResidueFacts (GaloBase.cup (K := F) (p := p))
    (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)
    (valLinOf_pi (F := F) (p := p) v hpF hπ)
    (GaloBase.cup_skew (K := F) (p := p))).mpr hfacts

end FiniteCase

end L20261018

#print axioms L20261018.exists_residueMap_of_finite
