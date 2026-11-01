import L20261018.Infra.Cohomology.ResidueLES.Step032_inf_c_inverse_narrowed

/-!
# S46 R21：★★★ **`RestrictedCoindAcyclic` 的非空见证**（KB 规则 L1／L10①）

`Hyp572` 把 `Inf_C⁻¹` 的假设面收窄成具名缺口 `RestrictedCoindAcyclic p I`
（`= Subsingleton (H¹(I, DiscreteCoind Γ ⊥ μ_p))`）。**具名假设必须给非空见证**，
否则下游的条件定理是空的。本件给两例：

* `I = ⊥`：`↥⊥` 是平凡群，由 `subsingleton_continuousCohomology_succ_of_subsingleton` 即得。

**注意**：`I = ⊤` 那一例**不成立直接套用**——`↥⊤` 与 `Γ` 只是同构而非 defeq，
库内 `subsingleton_continuousCohomology_discreteCoind_iff` 要求系数恰为同群的 `DiscreteCoind`
（已实测：先要一条 `DiscreteCoind ↥⊤ ⊥ A ≅ DiscreteCoind Γ ⊥ A`，本轮未做）。
本件只做 `⊥` 那一例；它不覆盖战役真正需要的 `I = inertiaLoc F`（非平凡、非全群），
故 `RestrictedCoindAcyclic` 的**一般情形仍未证**——本件只保证该假设**非空**。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- `↥(⊥ : Subgroup (Γ⧸I))` 等平凡作用样板（此处只需 `Γ` 上的平凡作用）。 -/
local instance trivialActionZModR21 : DistribMulAction (AbsoluteGaloisGroup F) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulZModR21 :
    ContinuousSMul (AbsoluteGaloisGroup F) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★ **见证二**：`I = ⊥` 时 `RestrictedCoindAcyclic` 成立（平凡群零调）。 -/
theorem restrictedCoindAcyclic_bot :
    RestrictedCoindAcyclic (F := F) p (⊥ : Subgroup (AbsoluteGaloisGroup F)) := by
  rw [RestrictedCoindAcyclic]
  exact TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_succ_of_subsingleton
    (n := 0) (X := ofDiscreteModule ℤ (↥(⊥ : Subgroup (AbsoluteGaloisGroup F))) (contB (F := F) p))

end L20261018

#print axioms L20261018.restrictedCoindAcyclic_bot
