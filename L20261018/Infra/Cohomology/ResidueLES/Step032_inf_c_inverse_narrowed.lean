import L20261018.Infra.Cohomology.ResidueLES.Step031_inf_c_inverse_hypothesis

/-!
# S46 R20：★★★ **`Inf_C⁻¹` 的假设面收窄到一件，并给出具名缺口**

`Hyp571` 把 `Subsingleton (H¹(I, C))` 化归为
`Subsingleton (H¹(I, Bᴵ)) ∧ Subsingleton (H²(I, μ_p))`。本件在**战役的惯性群**上实例化，
用 `Hyp517` 无条件供给后者，于是：

```
Subsingleton (H¹(I, Bᴵ))  ⟹  Subsingleton (H¹(I, C))          （I = inertiaLoc F）
```

并把剩下的这件具名化为 `RestrictedCoindAcyclic`（带类型锁），作为**单一事实来源**登记缺口。

## 为什么这件不是"库内已有"

`Bᴵ = DiscreteCoind Γ ⊥ μ_p` **作为 `↥I`-模**不是 `DiscreteCoind ↥I` 形态，故
`subsingleton_continuousCohomology_discreteCoind_iff`、`subsingleton_H1_discreteCoind_bot`
（两者都要求系数是 `DiscreteCoind G U A` 且群相同）**都套不上**。
数学上 `Bᴵ` 是「Γ 上局部常值函数」限制到 `I`，应当零调（余诱导模的限制仍是余诱导的乘积），
但库内没有这条。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

/-- ★★★ **具名缺口**：受限余诱导模在 `I` 上的 `H¹` 零调（`Inf_C⁻¹` 的最后一件输入）。

类型锁：源/靶写死；改群、改系数、改次数即编译失败。 -/
def RestrictedCoindAcyclic {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
    (I : Subgroup (AbsoluteGaloisGroup F)) : Prop :=
  Subsingleton (continuousCohomology 1
    (ofDiscreteModule ℤ ↥I (contB (F := F) p)))

section Inertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime]


/-- `inertiaLoc F` 闭（`Hyp380.isClosed_inertiaLoc`）。 -/
local instance closedInertiaLocR20 :
    IsClosed ((inertiaLoc F : Subgroup (AbsoluteGaloisGroup F)) : Set (AbsoluteGaloisGroup F)) :=
  isClosed_inertiaLoc F

/-- `inertiaLoc F` 正规。 -/
local instance normalInertiaLocR20 : (inertiaLoc F).Normal :=
  normal_inertiaLoc F

/-- `↥(inertiaLoc F)` 紧。 -/
local instance compactSpaceInertiaLocR20 : CompactSpace ↥(inertiaLoc F) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaLoc F).isCompact

/-- ★★★★ **`Subsingleton (H¹(I, C))`**（`I = inertiaLoc F`），唯一假设是具名缺口
`RestrictedCoindAcyclic`。`H²(I, μ_p)` 那一半由 `Hyp517` 无条件供给。 -/
theorem subsingleton_H1_contC_inertia
    (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hpq : p.Coprime q)
    (hB : RestrictedCoindAcyclic (F := F) p (inertiaLoc F)) :
    Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (contC (F := F) p))) := by
  haveI : Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (contB (F := F) p))) := hB
  haveI := inertiaLoc_subsingleton_H2_zmod (F := F) q p hpq
  exact subsingleton_H1_contC (F := F) p (inertiaLoc F)

end Inertia

end L20261018

#print axioms L20261018.subsingleton_H1_contC_inertia
