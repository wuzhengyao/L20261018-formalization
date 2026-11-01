import L20261018.Infra.Cohomology.Boundary.Step001_acyclicity_short_exact

/-!
# R1074（**(R2) 建造 H-5-1c**）：GS 的嵌入 `A ↪ M^G(A)`

GS 6.8.5（`cons-residue-map-finite-coefficients`）第一步：把 `A` 嵌入余诱导模 `M^G(A)`。
余诱导模上的 `G`-作用是**纯右平移** `(g • f) x = f (x * g)`（`TauCeti.ContCohomology.coind_smul_apply`），
故 `G`-等变的嵌入**不是常函数**，而是

```
incl a := (g ↦ g • a)
```

（`(incl (g' • a)) x = x • (g' • a) = (x * g') • a = (g' • incl a) x` ✓）。

| 声明 | 内容 |
|---|---|
| **`coindIncl`** | `A →+ DiscreteCoind G ⊥ A`，`a ↦ (g ↦ g • a)` |
| **`coindIncl_apply`** | 计算规则 `coindIncl a g = g • a` |
| **`coindIncl_injective`** | 单射（在 `g = 1` 取值） |
| **`coindIncl_equivariant`** | `G`-等变：`coindIncl (g • a) = g • coindIncl a` |

**下一步（H-5-1d）**：商 `C := DiscreteCoind G ⊥ A ⧸ range (coindIncl)`（配上离散拓扑与 `G`-作用）
＋ `DiscreteShortExact` 六项数据，接 `Hyp210.subsingleton_cohomology_three_of_coind`。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open TauCeti

namespace L20261018

section Incl

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SeparatelyContinuousMul G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- **GS 6.8.5 的嵌入 `A ↪ M^G(A)`**：`a ↦ (g ↦ g • a)`。 -/
def coindIncl : A →+ DiscreteCoind G ⊥ A where
  toFun a := DiscreteCoind.mk G ⊥ A (fun g => g • a)
    ((IsLocallyConstant.iff_continuous _).mpr (continuous_id.smul continuous_const))
    (fun u g => by
      have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp u.2)
      rw [hu]
      simp)
  map_zero' := by
    ext g
    simp
  map_add' a b := by
    ext g
    simp

@[simp]
theorem coindIncl_apply (a : A) (g : G) : coindIncl (G := G) (A := A) a g = g • a := by
  simp [coindIncl]

/-- **嵌入是单射**（在 `g = 1` 处取值）。 -/
theorem coindIncl_injective : Function.Injective (coindIncl (G := G) (A := A)) := by
  intro a b hab
  have h := congrArg (fun f => f (1 : G)) hab
  simpa using h

/-- **嵌入是 `G`-等变的**。 -/
theorem coindIncl_equivariant (g : G) (a : A) :
    coindIncl (G := G) (A := A) (g • a) = g • coindIncl (G := G) (A := A) a := by
  ext x
  simp [mul_smul]

end Incl

end L20261018

#print axioms L20261018.coindIncl_injective
#print axioms L20261018.coindIncl_equivariant
