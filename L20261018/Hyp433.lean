import Hyp432
import Hyp138

/-!
# S39 第 7 轮（B 第 3 步）：**完备情形的真正引擎是一维性，不是有限性**（`Hyp433`）

## 本轮定位（读 `Hyp138.ker_dependent` 的证明得到）

`Hyp138.kerCupPi_injective`（完备情形 `Φ` 单射）的**唯一引擎**是

```
ker_dependent : ∀ y z ∈ ker v̄, y ∈ k ∙ z ∨ z ∈ k ∙ y
```

即 **`ker v̄` 一维（任意两元素线性相关）**。这可机检地推出 ——

> **一维 ＋ `∪` 交替 ⟹ `residueSpan = ⊥`**：
> `residueSpan = span{∪ y z}`，而一维时 `y ∈ k∙z` 或 `z ∈ k∙y`，
> 故 `∪ y z` 是 `c • (∪ z z)` 或 `c • (∪ y y)`，交替性给 `∪ x x = 0` ⟹ `∪ y z = 0`。

⟹ **完备情形的 `residueSpan = ⊥` 不是因为「残域有限」，而是因为 `dim ker v̄ = 1`。**
二者在局部域上重合（`IsNonarchimedeanLocalField` ⟹ 有限残域 ⟹ `H¹(κ) ≅ Z/p`），
但在 `κ = ℂ(t)` 上 **`dim ker v̄ = ∞`**，一维性**不可得**，交替性给不出任何东西。

**这是 B 无法用完备情形模板的真正原因**（比「有限残域」更精确）。

## 机检件

| 件 | 内容 |
|---|---|
| **`residueSpan_eq_bot_of_dependent`** | ★★★★★ 抽象：**一维依赖 ＋ 交替 ⟹ `residueSpan = ⊥`** |
| **`exists_residueMap_of_dependent`** | ★★★★★ 具体：同一维性 ⟹ `∃ d`（两条值性质），**无有限残域／无有限维／无 `UnitsCupVanish`** |
| `disjoint_of_dependent` | 同一维性 ⟹ `Disjoint` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

/-! ## 1. 抽象层：一维依赖 ＋ 交替 ⟹ `residueSpan = ⊥` -/

section AbstractDep

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- ★★★★★ **一维依赖 ＋ 交替 ⟹ 单位杯积块为零**。

`ker val` 中任意两元素线性相关 ⟹ 每个 `∪ y z` 都是 `c • (∪ z z)` 或 `c • (∪ y y)`，
再由 `∪ x x = 0` 得零。**这正是完备情形（`ker_dependent`）的真正引擎。** -/
theorem residueSpan_eq_bot_of_dependent (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (hself : ∀ x : V, cup x x = 0)
    (hdep : ∀ y z : V, val y = 0 → val z = 0 → y ∈ k ∙ z ∨ z ∈ k ∙ y) :
    residueSpan cup val = ⊥ := by
  rw [residueSpan, Submodule.span_eq_bot]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  rcases hdep (y : V) (z : V) y.2 z.2 with h | h
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    show cup (y : V) (z : V) = 0
    rw [show (y : V) = c • (z : V) from hc.symm, map_smul, LinearMap.smul_apply, hself, smul_zero]
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    show cup (y : V) (z : V) = 0
    rw [show (z : V) = c • (y : V) from hc.symm, LinearMap.map_smul, hself, smul_zero]

/-- 一维依赖 ⟹ `Disjoint`（经 `residueSpan = ⊥`）。 -/
theorem disjoint_of_dependent (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)
    (hself : ∀ x : V, cup x x = 0)
    (hdep : ∀ y z : V, val y = 0 → val z = 0 → y ∈ k ∙ z ∨ z ∈ k ∙ y) :
    Disjoint (LinearMap.range (residuePhi cup val π)) (residueSpan cup val) :=
  disjoint_of_residueSpan_eq_bot cup val π (residueSpan_eq_bot_of_dependent cup val hself hdep)

end AbstractDep

/-! ## 2. 具体层：第 4 章的 `∃ d`（一维性作假设） -/

section ConcreteDep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **`∃ d`（两条值性质）⟸ `ker v̄` 一维**。

假设是 `Hyp138.ker_dependent` 的**类无关版**（`∀ y z ∈ ker v̄, y ∈ k∙z ∨ z ∈ k∙y`），
比 `Hyp138` 的版本**更一般**（不要求 `[IsNonarchimedeanLocalField F]`、不要求完备性、
不要求有限残域、不要求有限维）。
**无** `UnitsCupVanish`、**无** `[Finite (ResidueField)]`、**无** `FiniteDimensional`。 -/
theorem exists_residueMap_of_dependent {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p))
    (hdep : ∀ y z : GaloBase.V F p,
      valLinOf (F := F) (p := p) v hpF y = 0 → valLinOf (F := F) (p := p) v hpF z = 0 →
      y ∈ ZMod p ∙ z ∨ z ∈ ZMod p ∙ y) :
    ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
      (∀ y z : VKG F p v hpF,
        d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p)) (z : GaloBase.V F p)) = 0) ∧
      (∀ y : VKG F p v hpF,
        d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p))
          (KummerBridge.kummerClass F p hpF π)) = y) := by
  refine exists_residueMap_of_disjoint (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2 ?_
  exact disjoint_of_dependent (GaloBase.cup (K := F) (p := p))
    (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)
    (fun x => cup_self_free (F := F) (p := p) hp2' x) hdep

end ConcreteDep

end L20261018

#print axioms L20261018.residueSpan_eq_bot_of_dependent
#print axioms L20261018.disjoint_of_dependent
#print axioms L20261018.exists_residueMap_of_dependent
