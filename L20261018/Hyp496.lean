import L20261018.Hyp495

/-!
# S41 R7（动作 V2f 第二块）：**共轭作用下降到 `G ⧸ H`**

## 本件在 GS §6.8 的哪一格

`Hyp495` 给了 `G` 在 `Hⁿ(H,A)` 上的共轭作用（`conjNormalMap`）及 `H` 上平凡。
GS Construction 6.8.1 的最后一段要的是 **`G/H`-模结构**：

> … a map `C^H → H^1(H,A)`, which is a morphism of `G/H`-modules …

本件把 `G`-作用**沿 `QuotientGroup.lift` 下降**到 `G ⧸ H`：

| 声明 | 内容 |
|---|---|
| `conjEndQuotient` | `(G ⧸ H) →* AddMonoid.End (Hⁿ(H,A))`，由 `QuotientGroup.lift` 沿 `H ≤ ker` 下降 |
| **`quotientConjAction`** | ★★★★★ **`DistribMulAction (G ⧸ H) (Hⁿ(H,A))`** |

## 机制（全部库内件）

```
DistribMulAction.toAddMonoidEnd G M : G →* AddMonoid.End M     -- 作用的自同态形态
QuotientGroup.lift H φ (h : H ≤ φ.ker) : G ⧸ H →* M            -- 商下降
Hyp495.cohomologyConjAction_of_mem                            -- h ∈ H ⟹ h • x = x（即 H ≤ ker）
```

## 诚实边界

* 本件只做**模结构**（`DistribMulAction`）。把它装成 `TopRep (G ⧸ H)`、
  证明 `ContinuousSMul`、以及装配 `delta_conjNormalMap`（库内：共轭与连接映射逐次交换）
  ⟹ 完整的 `coeffMap : H¹(G⧸H, C^H) → H¹(G⧸H, H¹(H,A))` —— **下一步**。
* 本件**不**触及 `KnrResidueObligation`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (H : Subgroup G) [H.Normal]
variable (A : Type) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable (n : ℕ)

/-- ★★★★★ **`(G ⧸ H) →* AddMonoid.End (Hⁿ(H,A))`**：共轭作用沿 `H ≤ ker` 下降。

`H ≤ ker` 就是 `Hyp495.cohomologyConjAction_of_mem`（内自同构在上同调上平凡）。 -/
noncomputable def conjEndQuotient (hHcl : IsClosed (H : Set G)) :
    (G ⧸ H) →* AddMonoid.End
      ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ ↥H A)).toModuleCat :=
  QuotientGroup.lift H (DistribMulAction.toAddMonoidEnd G _) (fun g hg => by
    rw [MonoidHom.mem_ker]
    refine AddMonoidHom.ext (fun x => ?_)
    show g • x = x
    exact cohomologyConjAction_of_mem H A n hHcl hg x)

/-- ★★★★★★ **`G ⧸ H` 在 `Hⁿ(H,A)` 上的作用**（V2f 的模结构）。 -/
noncomputable def quotientConjAction (hHcl : IsClosed (H : Set G)) :
    DistribMulAction (G ⧸ H)
      ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ ↥H A)).toModuleCat where
  smul q x := conjEndQuotient H A n hHcl q x
  one_smul x := by
    show conjEndQuotient H A n hHcl 1 x = x
    rw [map_one]
    rfl
  mul_smul a b x := by
    show conjEndQuotient H A n hHcl (a * b) x
      = conjEndQuotient H A n hHcl a (conjEndQuotient H A n hHcl b x)
    rw [map_mul]
    rfl
  smul_zero q := (conjEndQuotient H A n hHcl q).map_zero
  smul_add q := (conjEndQuotient H A n hHcl q).map_add

end L20261018

#print axioms L20261018.conjEndQuotient
#print axioms L20261018.quotientConjAction
