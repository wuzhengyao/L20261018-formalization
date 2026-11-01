import Hyp741

/-!
# S67 R1b：**离散码域上的 `ContinuousSMul` 判据**（`ContinuousSMul (G⧸I) (TBI S I)` 的前置）

`S67-4D-NOTES.md` §3.2：战役级接线 `Hyp742` 需要 `ContinuousSMul (Γ⧸I) (TBI (contCoindSES p) I)`，
而 `TBI` 的拓扑是 `⊥`（离散）。库内**没有**商作用的 `ContinuousSMul` 实例（已 `grep`：
`AddSubgroup.quotientDistribMulAction` 无伴随连续性引理）。

本件给**判据**：码域离散时，`ContinuousSMul` 只需逐点轨道映射连续。

`M` 离散 ⟹ `{p | p.1 • p.2 = y} = ⋃ m, {g | g • m = y} × {m}`，每项两开集之积，
故 `rw [continuous_def]` 后对 `U` 的单点分解即得。

**用途**：`TBI` 侧取 `h : y ↦ (q ↦ q • y)`，写 `y = mk' x` 后它是 `mk' ∘ (q ↦ q • x)`，
由 `[ContinuousSMul (G⧸I) Bᴵ]` ＋ `continuous_quot_mk` 即得（下一件 `Hyp743`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018


/-! ## 0 离散码域上的 `ContinuousSMul` 判据 -/

/-- **离散码域判据**：若每个点的轨道映射连续，则联合作用是连续的。

理由：`M` 离散 ⟹ `{p | p.1 • p.2 = y} = ⋃ m, {g | g • m = y} × {m}`，
每项是两个开集之积。`ContinuousSMul` 只在码域非离散时需要更多。 -/
theorem continuous_smul_of_forall_continuous {G M : Type*} [Group G] [TopologicalSpace G]
    [TopologicalSpace M] [DiscreteTopology M] [MulAction G M]
    (h : ∀ m : M, Continuous fun g : G => g • m) :
    Continuous fun p : G × M => p.1 • p.2 := by
  have hset : ∀ y : M, IsOpen {p : G × M | p.1 • p.2 = y} := by
    intro y
    have hEq : {p : G × M | p.1 • p.2 = y}
        = ⋃ m : M, {g : G | g • m = y} ×ˢ ({m} : Set M) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro hp; exact ⟨p.2, hp, rfl⟩
      · rintro ⟨m', hp, rfl⟩; exact hp
    rw [hEq]
    exact isOpen_iUnion fun m =>
      IsOpen.prod ((h m).isOpen_preimage {y} (isOpen_discrete _)) (isOpen_discrete _)
  rw [continuous_def]
  intro U hU
  have hpre : (fun p : G × M => p.1 • p.2) ⁻¹' U
      = ⋃ y ∈ U, (fun p : G × M => p.1 • p.2) ⁻¹' ({y} : Set M) := by
    ext p; simp
  rw [hpre]
  exact isOpen_biUnion fun y _ => hset y

end L20261018

#print axioms L20261018.continuous_smul_of_forall_continuous
