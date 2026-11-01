import L20261018.Infra.Cohomology.Boundary.Step028_inflation_h1_iso
import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.ConnectingMap

/-!
# S41 R6（动作 V2f 第一块）：**`G` 在 `Hⁿ(H,A)` 上的共轭作用**及其在 `H` 上的平凡性

## 本件在 GS §6.8 的哪一格

GS **Construction 6.8.1** 的最后一段：

> But from the long exact sequence in `H`-cohomology coming from (6.14) we also obtain a map
> `C^H → H^1(H,A)`, **which is a morphism of `G/H`-modules** by Lemma (conjugation-long-exact).
> Hence there are induced maps `H^{i-1}(G/H,C^H) → H^{i-1}(G/H,H^1(H,A))`.

本件把「`H¹(H,A)` 是 `G/H`-模」这一半机检到位：

| 声明 | 内容 |
|---|---|
| **`cohomologyConjAction`** | ★★★ `DistribMulAction G (Hⁿ(H,A))`，`g • x := conjNormalMap g n x`（库内 `conjNormalMap_one`／`_comp` 供两条公理） |
| **`cohomologyConjAction_of_mem`** | ★★★★ **`h ∈ H ⟹ h • x = x`**（内自同构在上同调上平凡，库内 `conjMap_eq_id_of_mem`） |
| `cohomologyConjAction_eq_conjMap` | 与库内 `conjMap` 的一致性 |

⟹ 由 `H` 作用的平凡性，`G`-作用**下降**到 `G ⧸ H`（下一步 `quotientConjAction`）；
再把 `C^H → H¹(H,A)` 的 `G`-等变性（库内 **`DiscreteShortExact.delta_conjNormalMap`**：
「共轭与连接映射逐次交换」）接上，即得 GS 要的 `G/H`-模态射。

## 库内命中（规则 23／L46）

| 件 | 位置 | 内容 |
|---|---|---|
| **`conjNormalMap (g) (n)`** | `Corestriction/Conjugation.lean:259` | 正规子群上的共轭自同态 `Hⁿ(V,M) → Hⁿ(V,M)` |
| `conjNormalMap_one`／`conjNormalMap_comp` | 同上 `:277,291` | 它是**作用**（`1 ↦ id`、`g ≫ h = h*g`） |
| **`conjMap_eq_id_of_mem`** | `Conjugation/AllDegrees.lean:268` | ★★★ 内自同构在上同调上**平凡** |
| `conjMap_eq_conjNormalMap` | `Conjugation/AllDegrees.lean:207` | 正规情形 `conjMap = conjNormalMap` |
| **`DiscreteShortExact.delta_conjNormalMap`** | `Conjugation/ConnectingMap.lean:106` | ★★★★ **共轭与连接映射逐次交换**（V2f 的另一半） |

## 诚实边界

* 本件**只做 `G`-作用与 `H`-平凡性**。`G ⧸ H`-作用的下降、`delta_conjNormalMap` 的装配、
  以及 `H¹(H,A)` 的 `TopRep (G ⧸ H)` 结构**未做**（下一步）。
* 本件**不**触及 `KnrResidueObligation`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (H : Subgroup G) [H.Normal]

/-- ★★★★ **`G` 在 `Hⁿ(H,A)` 上的共轭作用**（`g • x := conjNormalMap g n x`）。

两条公理分别来自库内 `conjNormalMap_one` 与 `conjNormalMap_comp`。 -/
noncomputable instance cohomologyConjAction (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] (n : ℕ) :
    DistribMulAction G
      ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ ↥H A)).toModuleCat where
  smul g x := (TauCeti.ContinuousCohomology.conjNormalMap H A g n).hom x
  one_smul x := by
    show (TauCeti.ContinuousCohomology.conjNormalMap H A 1 n).hom x = x
    rw [TauCeti.ContinuousCohomology.conjNormalMap_one]
    rfl
  mul_smul g h x := by
    show (TauCeti.ContinuousCohomology.conjNormalMap H A (g * h) n).hom x
      = (TauCeti.ContinuousCohomology.conjNormalMap H A g n).hom
        ((TauCeti.ContinuousCohomology.conjNormalMap H A h n).hom x)
    rw [← TauCeti.ContinuousCohomology.conjNormalMap_comp]
    rfl
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _

/-- ★★★★★ **`H` 在 `Hⁿ(H,A)` 上作用平凡**（内自同构平凡）。

即 GS 所说的「`H¹(H,A)` 是 `G/H`-模」的**必要条件**。 -/
theorem cohomologyConjAction_of_mem (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] (n : ℕ)
    (hHcl : IsClosed (H : Set G)) {k : G} (hk : k ∈ H)
    (x : ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ ↥H A)).toModuleCat) :
    (k • x : ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ ↥H A)).toModuleCat) = x := by
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.mp hHcl.isCompact
  haveI : LocallyCompactSpace ↥H := inferInstance
  haveI : ContinuousSMul ↥H A := inferInstance
  have hH : H = H.map (MulAut.conj k).toMonoidHom := (Subgroup.Normal.map_conj_eq H k).symm
  show (TauCeti.ContinuousCohomology.conjNormalMap H A k n).hom x = x
  rw [← TauCeti.ContinuousCohomology.conjMap_eq_conjNormalMap (V := H) (M := A) (g := k) hH n]
  rw [TauCeti.ContinuousCohomology.conjMap_eq_id_of_mem (U := H) (M := A) (g := k) (n := n) hk hH]
  rfl

end L20261018

#print axioms L20261018.cohomologyConjAction_of_mem

#print axioms L20261018.cohomologyConjAction
