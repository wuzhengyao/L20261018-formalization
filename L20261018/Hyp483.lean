import L20261018.Hyp482

/-!
# S40 R23：★ **动作 A 第三段完成** —— `integralBockstein` 的 range 引理

## 关键侦察（R17 纪律）

`longExact_exact₄` **不存在**（R22 记的障碍），但 **不需要它** ——
`HomologySequence.lean:223` 的 **`longExact_exact₁`** 就是

```lean
theorem longExact_exact₁ (n : ℕ) :
    Function.Exact (S.delta n)
      (coeffMap (ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 1))
```
docstring 逐字：**"Exactness at `Hⁿ⁺¹(G, A)`: the image of the connecting map `Hⁿ(G, C) ⟶ Hⁿ⁺¹(G, A)`
is the kernel of the coefficient map induced by `A → B`"** —— 正是 `range δ = ker incl_*` ✓。

配合 `integralBocksteinShortExact_incl : incl = nsmulAddMonoidHom n`，
即得 **`range (integralBockstein n 1) = ker (x ↦ n • x)`**。

## 机检件

| 声明 | 内容 |
|---|---|
| **`integralBockstein_one_range`** | ★★★★★ **`(∃ y, δ y = x) ↔ nsmulAddMonoidHom n x = 0`**（像 = `n`-挠） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- `G` 在 `ULift ℤ` 上的平凡作用。 -/
local instance integralTrivialAction' : DistribMulAction G (ULift.{0} ℤ) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- `G` 在 `ULift ℤ` 上的平凡作用连续（离散）。 -/
local instance integralContinuousSMul' : ContinuousSMul G (ULift.{0} ℤ) := ⟨continuous_snd⟩

/-- `G` 在 `ULift (ZMod n)` 上的平凡作用。 -/
local instance cyclicTrivialAction (n : ℕ) : DistribMulAction G (ULift.{0} (ZMod n)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该作用连续（离散）。 -/
local instance cyclicContinuousSMul (n : ℕ) : ContinuousSMul G (ULift.{0} (ZMod n)) :=
  ⟨continuous_snd⟩

/-- ★★★★★ **`integralBockstein` 的像 = `n`-挠**（动作 A 第三段）。

`range δ = ker (incl_*)` 由 `longExact_exact₁`（exactness at `Hⁿ⁺¹(G,A)`）；
`incl = nsmulAddMonoidHom n` 由 `integralBocksteinShortExact_incl`。 -/
theorem integralBockstein_one_range (n : ℕ) [NeZero n]
    (x : ↑(continuousCohomology 2
      (TauCeti.ofDiscreteModule ℤ G (ULift.{0} ℤ))).toModuleCat) :
    (∃ y, ⇑(ConcreteCategory.hom (TauCeti.integralBockstein G n 1)) y = x) ↔
      nsmulAddMonoidHom n x = 0 := by
  have hex := (TauCeti.integralBocksteinShortExact G n).longExact_exact₁ 1
  rw [show ⇑(ConcreteCategory.hom (TauCeti.integralBockstein G n 1))
      = ⇑(ConcreteCategory.hom ((TauCeti.integralBocksteinShortExact G n).delta 1)) from rfl]
  refine (hex x).symm.trans ?_
  simp only [TauCeti.integralBocksteinShortExact_incl]
  constructor <;> intro h
  · simpa using h
  · simpa using h

end L20261018

#print axioms L20261018.integralBockstein_one_range
