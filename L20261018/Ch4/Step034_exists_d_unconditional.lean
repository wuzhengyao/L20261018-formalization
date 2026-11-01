import L20261018.Ch4.Step033_ch4_three_and_exists_d
import L20261018.Ch4.Step032_v_and_d_exists

/-!
# R1227（S34）：**`∃D` 的完全无条件版 —— `hbridge` 也消去**

`Hyp310.exists_henselResidueData_uncond`（R1201）把 `hv`／`hπ`／`[Fact (Irreducible …)]`／
`[Module.Finite …]`／`{π}` 全部造出，**但仍以 `hbridge` 为输入**。
本轮把它接到 `Hyp321.exists_henselResidueData_noBridge` 上 ⟹ **`hbridge` 消去**。

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_henselResidueData_uncond_noBridge`** | ★★★★★★ `∃ v, ValCompat v ∧ ∃ D, D.val = valH1LinearGen v hpF`（**零 `hbridge`**） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section UncondNoBridge

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
  [IsDiscreteValuationRing ↥𝒪[F]]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★★ **`∃D` 的完全无条件版（无 `hbridge`）**。

与 `Hyp310.exists_henselResidueData_uncond` 相比：`hbridge` 已由 `Hyp321` 的
`(T1)` 路线消去（`residuePhi_injective_muNRep'` ＋ `unitsCupVanish`）。

剩余假设 = `[IsDiscreteValuationRing ↥𝒪[F]]`（论文「离散」二字的直接编码，且被
`hπ : v π = ofAdd 1` 隐含）＋ `p ≠ 2` ＋ 双线性型的斜对称性（`hskew`，论文
`BiKummerData.skew` 的载体版）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_q\bigl(\mathrm{inf}(\eta)\cup(\pi)\bigr)=\eta,\partial_q(\mathrm{inf}(\xi))=0."
theorem exists_henselResidueData_uncond_noBridge {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x)) :
    ∃ (v : Fˣ →* Multiplicative ℤ),
      ValCompat (F := F) v ∧
      ∃ D : HenselResidueData (ZMod p)
          ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
          ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
          ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
          ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
        D.val = valH1LinearGen (p := p) v hpF := by
  obtain ⟨π, hzπ, hnotpow⟩ :=
    exists_uniformizer_not_pow (F := F) (p := p) (Fact.out : p.Prime).ne_one
  haveI hIrred : Fact (Irreducible (X ^ p - C (π : F))) :=
    ⟨(capelli_irreducible_iff (F := F) (p := p) hp2).mpr hnotpow⟩
  haveI hFin : Module.Finite F (AdjoinRoot (X ^ p - C (π : F))) :=
    moduleFinite_adjoinRoot (p := p) (π : F)
  have hπ : vCompatHom (F := F) π = Multiplicative.ofAdd (1 : ℤ) := by
    rw [show vCompatHom (F := F) π = Multiplicative.ofAdd (zval (F := F) π) from rfl, hzπ]
  exact ⟨vCompatHom, valCompat_of_dvr,
    exists_henselResidueData_noBridge (F := F) (p := p) hζ hp hpF
      valCompat_of_dvr hπ hp2 hskew⟩

end UncondNoBridge

end L20261018

#print axioms L20261018.exists_henselResidueData_uncond_noBridge
