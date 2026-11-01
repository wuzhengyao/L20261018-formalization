import L20261018.Infra.Cohomology.Coinduced.Step002_coind_subgroup_acyclic_carrier

/-!
# S63 R3：零调性缺口再削一层 —— **只需 `j = 1` 那一格**

## 为什么

`S63-C2-PLAN.md` §1 已论：GS 6.8.1 在 `i = 2` 时，`D` 步的五项正合列
`0 → H¹(G/H,C^H) → H¹(G,C) → H¹(H,C)^{G/H} → …` 只要求 **`H¹(H,C) = 0`**；
而 `C` 步给 `H¹(H,C)=0` 只需 **`H¹(H, M^G(A)) = 0`**（`M^G(A) = Coind_1^G A`）。

`Hyp712.CoindSubgroupAcyclic` 却按 `S62-COEFF-PLAN`／`S43-REMAINING` 的旧估工写成了
**全次数**（`∀ j ≥ 1`）。本件把缺口收到**一格**：

```
CoindSubgroupAcyclicOne H : Subsingleton (H¹(H, Coind_1^G A))
```

## 机检内容

| 声明 | 内容 |
|---|---|
| **`CoindSubgroupAcyclicOne`** | ★★★★★ **唯一缺口的 `j = 1` 形态**（比 `Hyp712` 弱得多） |
| **`subsingleton_H1_quot_subgroup`** | ★★★★★ **GS 6.8.1 的 C 步（`j = 1`）**，输入 = 上者 ＋ `H²(H,A)=0` |
| **`coindSubgroupAcyclicOne_bot`** | 非空见证（`H = ⊥`，平凡群 cd = 0） |

## 与 `Hyp712` 的关系

`Hyp712.subsingleton_cohomology_quot_subgroup`（`∀ j ≥ 1`）是**强形式**；本件是它真正被用到的
那一格，且**证明独立**（不经过 `Hyp712` 的全次数陈述，直接用 `Hyp210` 的三项长正合列论证）。
⟹ 下一轮攻 `CoindSubgroupAcyclicOne`（一次 `H¹` 计算），不必攻全次数。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- ★★★★★ **C2 的唯一缺口，`j = 1` 形态**：`Coind_1^G A` 在闭子群 `H` 上一阶零调。

（`Hyp712.CoindSubgroupAcyclic` 的全次数形态是它的充分加强；本战役 `i = 2` 只需本形态。） -/
def CoindSubgroupAcyclicOne (H : Subgroup G) : Prop :=
  Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H (DiscreteCoind G ⊥ A)))

/-- **非空见证**：`H = ⊥` 时 `↥⊥` 是平凡群，`H¹` 必零（`TrivialGroup`）。 -/
theorem coindSubgroupAcyclicOne_bot : CoindSubgroupAcyclicOne (G := G) (A := A) ⊥ := by
  haveI : Subsingleton ↥(⊥ : Subgroup G) :=
    ⟨fun a b => Subtype.ext (by
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  change Subsingleton (continuousCohomology 1
    (ofDiscreteModule ℤ ↥(⊥ : Subgroup G) (DiscreteCoind G ⊥ A)))
  exact inferInstance

section One

variable (H : Subgroup G) [IsClosed (H : Set G)]

instance : CompactSpace ↥H := isCompact_iff_compactSpace.mp (‹IsClosed (H : Set G)›).isCompact

/-- ★★★★★ **GS 6.8.1 的 C 步，`j = 1` 一格**：`H¹(H, Q) = 0`，输入只有
`H¹(H, Coind_1^G A) = 0`（`CoindSubgroupAcyclicOne`）＋ `H²(H,A) = 0`。

证明（`Hyp210` 的三项长正合列，特化到 `j = 1`）：
`δ¹ : H¹(H,C) → H²(H,A)` 的靶为零 ⟹ `δ¹ = 0`；正合性给 `H¹(H, M^G(A)) → H¹(H,C)` 满射；
源为零 ⟹ `H¹(H,C) = 0`。 -/
theorem subsingleton_H1_quot_subgroup
    (hB : CoindSubgroupAcyclicOne (G := G) (A := A) H)
    (hA : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ ↥H A))) :
    Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H (Q (G := G) (A := A)))) := by
  classical
  haveI := hA
  haveI : Subsingleton
      (continuousCohomology 1 (ofDiscreteModule ℤ ↥H (DiscreteCoind G ⊥ A))) := hB
  have hdelta : ⇑(CategoryTheory.ConcreteCategory.hom
      ((coindShortExactSubgroup (G := G) (A := A) H).delta 1)) = fun _ => 0 := by
    funext x
    exact Subsingleton.elim _ _
  have hex := (coindShortExactSubgroup (G := G) (A := A) H).longExact_exact₃ 1
  have hsurj : Function.Surjective
      ⇑(CategoryTheory.ConcreteCategory.hom
        (ContinuousCohomology.coeffMap (ofDiscreteModuleMap (R := ℤ) (G := ↥H)
          (coindShortExactSubgroup (G := G) (A := A) H).proj.toIntLinearMap
          (coindShortExactSubgroup (G := G) (A := A) H).proj_equivariant) 1)) := by
    intro y
    have h := hex y
    rw [hdelta] at h
    exact h.mp rfl
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  rw [Subsingleton.elim a b, hb]

end One

end L20261018

#print axioms L20261018.coindSubgroupAcyclicOne_bot
#print axioms L20261018.subsingleton_H1_quot_subgroup
