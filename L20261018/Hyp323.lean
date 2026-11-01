import L20261018.Hyp322

/-!
# R1228（S34）：**`hskew` 也消去** —— `kummerCupPairing` 的斜对称性是库内定理

`Hyp303`／`Hyp321`／`Hyp322` 都以 `hskew`（`muNRep` 载体上 cup 的斜对称性）为输入。
侦察发现 **TauCeti 早已给出**：

* `ClassFieldTheory.kummerCupPairing_flip : (kummerCupPairing ζ hζ).flip = kummerCupPairing ζ hζ`
  （`NumberTheory/ClassFieldTheory/Local/Symbol.lean:278`，由 `kummerCupPairing_bil_comm`）；
* `TopPairing.cup_gradedComm`（`Cup/Graded/Basic.lean`）—— 分次交换性。

⟹ 照 `A.lean` 的 `GaloBase.cup_skew` 抄一遍即得 `kummerCup_skew`（**零假设**）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`kummerCup_skew`** | ★ `cup x y = - cup y x`（`kummerCupPairing`，**无条件**） |
| **`exists_henselResidueData_uncond_noBridge'`** | ★★★★★★ 同 `Hyp322`，但 **`hskew` 也消去** |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ClassFieldTheory

namespace L20261018

section Skew

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [NeZero p]
  [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- ★ **`kummerCupPairing` 的一次杯积是斜对称的** —— **无条件**。

与 `A.lean` 的 `GaloBase.cup_skew` 同一证明骨架：`cup_gradedComm`（分次交换性）
＋ `kummerCupPairing_flip`（配对对称）＋ `(1,1)` 的符号 `(-1)^{1·1} = -1`。 -/
theorem kummerCup_skew {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (a b : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat) :
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) a b
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) b a) := by
  have h := TopPairing.cup_gradedComm (ClassFieldTheory.kummerCupPairing ζ hζ) 1 1 a b
  rw [show (1 * 1 : ℕ) = 1 by norm_num, pow_one] at h
  rw [show Nat.add_comm 1 1 = rfl from Subsingleton.elim _ _] at h
  rw [ContinuousCohomology.degreeCast_rfl] at h
  rw [ClassFieldTheory.kummerCupPairing_flip ζ hζ] at h
  simpa using h

end Skew

section Uncond

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
  [IsDiscreteValuationRing ↥𝒪[F]]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★★ **`∃D` 的完全无条件版：`hbridge`／`hskew`／`hv`／`hπ`／`{π}` 全部消去**。

剩余假设 = `[IsDiscreteValuationRing ↥𝒪[F]]`（「离散」）＋ `p ≠ 2`。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_q\bigl(\mathrm{inf}(\eta)\cup(\pi)\bigr)=\eta,\partial_q(\mathrm{inf}(\xi))=0."
theorem exists_henselResidueData_uncond_noBridge' {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hp2 : p ≠ 2) :
    ∃ (v : Fˣ →* Multiplicative ℤ),
      ValCompat (F := F) v ∧
      ∃ D : HenselResidueData (ZMod p)
          ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
          ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
          ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
          ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
        D.val = valH1LinearGen (p := p) v hpF :=
  exists_henselResidueData_uncond_noBridge (F := F) (p := p) hζ hp hpF hp2
    (kummerCup_skew (F := F) (p := p) hζ)

end Uncond

end L20261018

#print axioms L20261018.kummerCup_skew
#print axioms L20261018.exists_henselResidueData_uncond_noBridge'
