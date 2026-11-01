import Hyp549

/-!
# S45 R14：★★★★★ **连续 (F2)** —— `coeffMap(proj) ≫ δ₀ = 0`

离散侧 (F2)（`Hyp541.deltaZero_coindBot_comp_coind`）说「`δ₀` 在 `T = im(H⁰(Coind) → H⁰(C))` 上为零」。
连续侧**库内已有一行**：`TauCeti.ContCohomology.DiscreteShortExact.coeffMap_proj_comp_delta`
（`port/.../ContCohomology/HomologySequence.lean:252`，`#check` 逐字已核）：

```
coeffMap_proj_comp_delta (S : DiscreteShortExact G A B C) (n : ℕ) :
  ContinuousCohomology.coeffMap (ofDiscreteModuleMap S.proj.toIntLinearMap ⋯) n ≫ S.delta n = 0
```

本件把它**在战役的短正合列**（`Hyp549.contDimShiftSES T`）上开火，得连续 (F2)。
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
  (T : Subgroup (AbsoluteGaloisGroup F)) [CompactSpace ↥T]

/-- ★★★★★ **连续 (F2)**：`proj` 在 `H⁰` 上诱导的映射复合 `δ₀` 为零。

即「`δ₀` 在 `im(H⁰_cont(T, Coind μ_p) → H⁰_cont(T, C))` 上为零」——
GS (6.17) 右半在连续载体的形态，对应离散侧 `Hyp541`。 -/
theorem contDeltaZeroBar_kills_proj :
    ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap (contDimShiftSES (F := F) p T).proj.toIntLinearMap (fun _ _ => rfl)) 0
      ≫ contDeltaZeroBar (F := F) p T = 0 :=
  DiscreteShortExact.coeffMap_proj_comp_delta (contDimShiftSES (F := F) p T) 0

end L20261018

#print axioms L20261018.contDeltaZeroBar_kills_proj
