import L20261018.Infra.Cohomology.ResidueLES.Step010_continuous_f2

/-!
# S45 R16：★★★★ **连续侧 `res`–`δ` 交换方块** —— (A) 的 ⑤（连续 F1）的第一块

GS 的「inflation 与 boundary map 相容」（`raw/GilleSzamuely2017.tex:9540–9542`）在连续侧的
第一块就是**把 `Γ` 侧的 `δ` 限制到 `T = I`**：这正是库内的
`TauCeti.ContCohomology.DiscreteShortExact.delta_res`
（`port/.../ContCohomology/HomologySequence.lean:455`，`#check` 逐字已核）。

离散侧对应物：`Hyp543.delta_coind_comp_infl` 的 `δ_naturality` 应用。
本件不引入任何新数学：**一行**。
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

/-- ★★★★ **连续侧 `res`–`δ` 交换方块**：

`δ_Γ ≫ res_T = res_T ≫ δ_T`

（左侧 `δ_Γ` 是 `0 → μ_p → Coind → C → 0` 在 `Γ` 上的连接映射，右侧 `δ_T` 是它限制到 `T` 后的）。
这是 GS「inflation 与 boundary map 相容」的**限制半**；离散侧对应 `Hyp543` 里 `δ_naturality` 的那一步。 -/
theorem contDelta_res_naturality :
    (contCoindSES (F := F) p).delta 0
        ≫ ContinuousCohomology.res T (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) 1
      = ContinuousCohomology.res T
          (ofDiscreteModule ℤ (AbsoluteGaloisGroup F)
            (CoindQuotient (AbsoluteGaloisGroup F) ⊥ (ZMod p))) 0
        ≫ contDeltaZeroBar (F := F) p T :=
  DiscreteShortExact.delta_res (contCoindSES (F := F) p) T 0

/-- 载体锁定：`contDeltaZeroBar` 就是 `(contDimShiftSES T).delta 0`（供下游 `rw` 对齐）。 -/
theorem contDeltaZeroBar_eq_delta :
    contDeltaZeroBar (F := F) p T = (contDimShiftSES (F := F) p T).delta 0 := (rfl)

end L20261018

#print axioms L20261018.contDelta_res_naturality
#print axioms L20261018.contDeltaZeroBar_eq_delta
