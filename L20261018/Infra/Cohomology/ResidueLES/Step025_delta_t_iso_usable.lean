import L20261018.Infra.Cohomology.ResidueLES.Step024_top_rep_iso_coind

/-!
# S46 R13：★★★ **`δ_T` 同构的可用形态**（`Epi`、`n = 1`、惯性群实例化）

`Hyp564.isIso_contInvSES_delta_uncond` 给了一般的 `IsIso δ_T`。本件把它整成下游要用的三件：

* `epi_contInvSES_delta_uncond` —— `(d)` 收口要的 `Epi`（`δ ≫ X = 0 ⟹ X = 0`）；
* `contInvSES_delta_one_isIso` —— `n = 1` 的显式形态（`∂₂` 只用这一档）；
* `isIso_contInvSES_delta_inertia` —— **在战役的惯性群 `inertiaLoc F` 上实例化**
  （补 `IsClosed` 与 `I.Normal` 两个前提）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
  (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [IsClosed (I : Set (AbsoluteGaloisGroup F))]

/-- ★★★★ **`δ_T` 是满的**（`(d)` 收口：`δ ≫ X = 0 ⟹ X = 0` 必须 `Epi`，不是 `Mono`）。 -/
theorem epi_contInvSES_delta_uncond (n : ℕ) (hn : 1 ≤ n) :
    Epi ((contInvSES (F := F) p I).delta n) := by
  haveI := isIso_contInvSES_delta_uncond (F := F) p I n hn
  infer_instance

/-- `n = 1` 的显式形态（`∂₂` 唯一用到的那一档）。 -/
theorem contInvSES_delta_one_isIso :
    IsIso ((contInvSES (F := F) p I).delta 1) :=
  isIso_contInvSES_delta_uncond (F := F) p I 1 le_rfl

/-- `n = 1` 的 `Epi`。 -/
theorem epi_contInvSES_delta_one : Epi ((contInvSES (F := F) p I).delta 1) :=
  epi_contInvSES_delta_uncond (F := F) p I 1 le_rfl

section Inertia

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- `I` 闭（`Hyp380.isClosed_inertiaLoc`，其证明实为 `fixingSubgroup_isClosed`，无条件）。 -/
local instance closedInertiaLoc :
    IsClosed ((inertiaLoc F : Subgroup (AbsoluteGaloisGroup F)) : Set (AbsoluteGaloisGroup F)) :=
  isClosed_inertiaLoc F

/-- `I ◁ Γ`。 -/
local instance normalInertiaLoc : (inertiaLoc F).Normal :=
  normal_inertiaLoc F

/-- ★★★★★ **在战役的惯性群上实例化**：`δ_T` 对 `I = inertiaLoc F` 无条件同构。 -/
theorem isIso_contInvSES_delta_inertia (n : ℕ) (hn : 1 ≤ n) :
    IsIso ((contInvSES (F := F) p (inertiaLoc F)).delta n) :=
  isIso_contInvSES_delta_uncond (F := F) p (inertiaLoc F) n hn

/-- `I = inertiaLoc F` 时 `n = 1` 的 `Epi` 形态。 -/
theorem epi_contInvSES_delta_inertia_one :
    Epi ((contInvSES (F := F) p (inertiaLoc F)).delta 1) :=
  epi_contInvSES_delta_uncond (F := F) p (inertiaLoc F) 1 le_rfl

end Inertia

end L20261018

#print axioms L20261018.epi_contInvSES_delta_uncond
#print axioms L20261018.contInvSES_delta_one_isIso
#print axioms L20261018.isIso_contInvSES_delta_inertia
