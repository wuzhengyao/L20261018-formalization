import L20261018.Hyp376

/-!
# R1290（S36 · GS §6.8 战役 #4）：`ℚ` 的**离散副本**上的 `H¹` 零调

(G4′) 需要 `H¹_cont(G, ℚ) = 0`，但 mathlib 的 `ℚ` 带**序拓扑**（非离散）。
GS 的系数是**离散模**，故用 mathlib 现成的 `WithDiscreteTopology ℚ`（`Topology/Order.lean:588`）。

| 声明 | 内容 |
|---|---|
| `Qdisc` | `WithDiscreteTopology ℚ`（离散 `ℚ`，代数结构沿 `def` 透明搬运） |
| **`subsingleton_H1_rat_disc_absGal`** | ★★★★ `H¹(AbsGal F, Qdisc) = 0` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

/-- 离散拓扑下的 `ℚ`（`ULift` 副本 ＋ `⊥` 拓扑）：GS 的系数是**离散模**，
而 mathlib 的 `ℚ` 自带序拓扑（非离散），故必须换副本。 -/
abbrev Qdisc : Type := ULift ℚ

instance : TopologicalSpace Qdisc := ⊥
instance : DiscreteTopology Qdisc := ⟨rfl⟩

instance : IsAddTorsionFree Qdisc where
  eq_of_nsmul_eq_nsmul_of_addCommute := by
    intro n hn a b _ hab
    refine ULift.ext (IsAddTorsionFree.eq_of_nsmul_eq_nsmul_of_addCommute hn (add_comm a.down b.down) ?_)
    have h := congrArg ULift.down hab
    simpa using h

variable (F : Type) [Field F]

/-- 平凡作用（局部实例）。 -/
local instance : SMul (TauCeti.AbsoluteGaloisGroup F) Qdisc := ⟨fun _ m => m⟩
local instance : DistribMulAction (TauCeti.AbsoluteGaloisGroup F) Qdisc where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl
local instance : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) Qdisc := ⟨continuous_snd⟩

/-- ★★★★ **`H¹(AbsGal F, ℚ_disc) = 0`**（(G4′) 的 `n = 1` 输入）。 -/
theorem subsingleton_H1_rat_disc_absGal :
    Subsingleton (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) Qdisc) :=
  ContCohomology.subsingleton_H1_of_isAddTorsionFree (fun _ _ => rfl)

end L20261018

#print axioms L20261018.subsingleton_H1_rat_disc_absGal
