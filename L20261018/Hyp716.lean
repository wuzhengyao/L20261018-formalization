import Hyp715

/-!
# S64 R3：**B 步收口** —— 任意闭子群上的零调性（`C2-INFRA-2`）

`Hyp715` 只给了**有限指数**闭子群上的 `H¹(H, Coind_⊥^G A) = 0`。战役的 `H` 是**惯性群**，
**不是**有限指数。本件用库内的 colimit 化归把有限指数情形推到任意闭子群：

```
H¹(H, X) = colim_{H ≤ V open} H¹(V, X)
```
（`TauCeti.ContinuousCohomology.exists_openSubgroup_le_resLE_eq`：每个类都来自某个开子群 `V ⊇ H`；
紧群的**开子群必有限指数** `finiteIndex_of_isOpen`。）

## 内容

| 声明 | 内容 |
|---|---|
| `finiteIndex_of_isOpen` | 紧群的开子群有限指数（`OpenSubgroup.quotient_finite_of_isOpen`） |
| **`coindSubgroupAcyclicOne`** | ★★★★★ **`Hyp714.CoindSubgroupAcyclicOne`，任意闭 `H`**（B 步收口） |
| **`subsingleton_H1_quot_subgroup_of_isClosed`** | ★★★★★ **GS 6.8.1 的 C 步，假设已消除**（只剩 `H²(H,A)=0`） |

`Hyp714.subsingleton_H1_quot_subgroup` 的输入 `hB : CoindSubgroupAcyclicOne H` 现在**无条件可给**，
故 C 步的**唯一数值输入**是 `H²(H,A) = 0`（战役由 `cd_ℓ(I) ≤ 1`／`Hyp517` 提供）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

section Final

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G] [TotallyDisconnectedSpace G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- **紧群的开子群有限指数**（`G ⧸ U` 离散 ＋ 紧 ⟹ 有限）。 -/
theorem finiteIndex_of_isOpen {U : Subgroup G} (hU : IsOpen (U : Set G)) : U.FiniteIndex :=
  Subgroup.finiteIndex_iff_finite_quotient.mpr (Subgroup.quotient_finite_of_isOpen U hU)

/-- ★★★★★ **B 步收口（`C2-INFRA-2`）**：`Coind_⊥^G A` 在**任意闭子群** `H` 上一阶零调。

证明：任取 `y ∈ H¹(H, Coind_⊥^G A)`，colimit 化归给出开子群 `V ⊇ H` 与
`x ∈ H¹(V, Coind_⊥^G A)` 使 `resLE x = y`；`V` 开 ⟹ 有限指数 ⟹ `x = 0`
（`Hyp715.subsingleton_continuousCohomology_one_coindBot`）⟹ `y = 0`。 -/
theorem coindSubgroupAcyclicOne {H : Subgroup G} (hH : IsClosed (H : Set G)) :
    CoindSubgroupAcyclicOne (G := G) (A := A) H := by
  change Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H (DiscreteCoind G ⊥ A)))
  have hX : IsSmoothDiscrete ℤ (ofDiscreteModule ℤ G (DiscreteCoind G ⊥ A)) :=
    ofDiscreteModule_isSmoothDiscrete (R := ℤ) (G := G) (M := DiscreteCoind G ⊥ A)
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨V, hHV, x, hx⟩ := ContinuousCohomology.exists_openSubgroup_le_resLE_eq
    (k := ℤ) (X := ofDiscreteModule ℤ G (DiscreteCoind G ⊥ A)) hX hH (n := 1) y
  haveI : ((V : Subgroup G)).FiniteIndex := finiteIndex_of_isOpen V.isOpen
  haveI : IsClosed ((V : Subgroup G) : Set G) := V.isClosed
  have hVsub : Subsingleton (continuousCohomology 1
      (TopRep.res ((V : Subgroup G)).subtype (ofDiscreteModule ℤ G (DiscreteCoind G ⊥ A)))) := by
    rw [res_ofDiscreteModule]
    exact subsingleton_continuousCohomology_one_coindBot (H := (V : Subgroup G)) V.isOpen
  haveI := hVsub
  have hx0 : x = 0 := Subsingleton.elim x 0
  rw [← hx, hx0, map_zero]
  rfl

end Final

/-! ## C 步：假设消除 -/

section Cstep

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G] [TotallyDisconnectedSpace G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable (H : Subgroup G) [IsClosed (H : Set G)]

instance : CompactSpace ↥H := isCompact_iff_compactSpace.mp ‹IsClosed (H : Set G)›.isCompact

/-- ★★★★★ **GS 6.8.1 的 C 步，`hB` 假设已消除**：`H¹(H, Q) = 0`，唯一输入是
`H²(H, A) = 0`（战役由 `cd_ℓ(I) ≤ 1` 提供）。 -/
theorem subsingleton_H1_quot_subgroup_of_isClosed
    (hA : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ ↥H A))) :
    Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H (Q (G := G) (A := A)))) :=
  subsingleton_H1_quot_subgroup (G := G) (A := A) H (coindSubgroupAcyclicOne ‹IsClosed (H : Set G)›) hA

end Cstep

end L20261018

#print axioms L20261018.finiteIndex_of_isOpen
#print axioms L20261018.coindSubgroupAcyclicOne
#print axioms L20261018.subsingleton_H1_quot_subgroup_of_isClosed
