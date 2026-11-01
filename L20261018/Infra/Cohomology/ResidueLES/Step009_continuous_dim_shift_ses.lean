import L20261018.Infra.Cohomology.ResidueLES.Step008_base_ring_alignment

/-!
# S45 R11：★★★★ **连续版 `dimShiftSES` ＋ `δ₀`** —— (A) 的步骤 ③

离散侧对应物：`Hyp541.dimShiftSES = X.map (Rep.resFunctor S.subtype)`、`Hyp230.deltaZero_coindBot`。

连续侧只用库内件：`ContCohomology.coindShortExact Γ ⊥ ↥(ZMod p)` ＋ `DiscreteShortExact.restrict T`
＋ `DiscreteShortExact.delta`（`HomologySequence.lean:109`）。**不新建短正合列。**
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- 连续侧系数短正合列：`0 → μ_p → Coind(μ_p) → CoindQuotient(μ_p) → 0`（`ℤ`-基底）。 -/
noncomputable abbrev contCoindSES :
    DiscreteShortExact (AbsoluteGaloisGroup F) (ZMod p)
      (DiscreteCoind (AbsoluteGaloisGroup F) ⊥ (ZMod p))
      (CoindQuotient (AbsoluteGaloisGroup F) ⊥ (ZMod p)) :=
  coindShortExact (AbsoluteGaloisGroup F) ⊥ (ZMod p)

/-- ★★★★ **连续版 `dimShiftSES`**：把上面的短正合列限制到闭子群 `T`（`I_K` 就取 `T`）。 -/
noncomputable abbrev contDimShiftSES (T : Subgroup (AbsoluteGaloisGroup F)) [CompactSpace ↥T] :
    DiscreteShortExact ↥T (ZMod p)
      (DiscreteCoind (AbsoluteGaloisGroup F) ⊥ (ZMod p))
      (CoindQuotient (AbsoluteGaloisGroup F) ⊥ (ZMod p)) :=
  (contCoindSES (F := F) p).restrict T

/-- ★★★★★ **连续版 `δ₀`**：`H⁰_cont(T, C) ⟶ H¹_cont(T, μ_p)`。

对应离散侧的 `Hyp230.deltaZero_coindBot`；`T = I_K` 时就是 GS 的 `C^{I} → H¹(I, μ_p)`。 -/
noncomputable abbrev contDeltaZeroBar (T : Subgroup (AbsoluteGaloisGroup F)) [CompactSpace ↥T] :
    continuousCohomology 0
        (ofDiscreteModule ℤ ↥T (CoindQuotient (AbsoluteGaloisGroup F) ⊥ (ZMod p)))
      ⟶ continuousCohomology 1 (ofDiscreteModule ℤ ↥T (ZMod p)) :=
  (contDimShiftSES (F := F) p T).delta 0

end L20261018

#print axioms L20261018.contCoindSES
#print axioms L20261018.contDimShiftSES
#print axioms L20261018.contDeltaZeroBar
