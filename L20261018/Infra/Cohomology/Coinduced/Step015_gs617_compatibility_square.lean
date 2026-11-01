import L20261018.Infra.Cohomology.Coinduced.Step014_coinduced_invariants

/-!
# S65 R3：分片 **4c-i** —— GS (6.17) 的**兼容方块**（`delta_infl` 的 `T`-变体）

⚠ **`DiscreteShortExact.delta_infl` 在本战役用不了**：它要求
`SN : DiscreteShortExact (G ⧸ N) (A^N) (B^N) (C^N)`，即 `0 → A^I → B^I → C^I → 0` **本身短正合**；
而本战役 `coker(B^I → C^I) ≅ H¹(I, A) ≅ ℤ/p ≠ 0`（`Hyp521`）。这正是 GS 要拆 (6.17) 的原因。

正解：库内 `DeltaNaturality.lean` / `HomologySequence.delta_map` 的**一般方块**只要求两条**兼容等式**
（`fB ∘ SN.incl = S.incl ∘ fA`、`fC ∘ SN.proj = S.proj ∘ fB`），**不要求不变子序列正合**
（`delta_infl` 的 docstring 原文："the invariants of a short exact sequence need not be exact,
so the sequence over `G ⧸ N` is data a caller supplies"）。

本件把第三条换成 `T := B^I / A^I`，`fC : T →+ C`（`G⧸N`-等变、且在 `B^I` 上与 `S.proj` 一致）：

```
       SN.delta n                map φ (A^I ↪ A)
Hⁿ(G⧸N,T) --------> Hⁿ⁺¹(G⧸N,A^I) -------------> Hⁿ⁺¹(G,A)
                                                  
       S.delta n                 map φ fC
  Hⁿ(G,C) --------> Hⁿ⁺¹(G,A)   ≈   Hⁿ(G⧸N,T) --> Hⁿ(G,C)
```

即 `SN.delta n ≫ map φ (A^I ↪ A) (n+1) = map φ fC n ≫ S.delta n` —— **4d 的第一格**。

## 与 `delta_infl` 的关系

`delta_infl` ＝ 本件 ＋ `fC := (C^I ↪ C)` ＋ `coeffMap_ofDiscreteModuleQuotient_comp_infl`
（把 `map φ (·)` 译成 `coeffMap ≫ infl`）。本件只用 `map` 形态，故**不需要** `C^I` 正合；
后面的 `infl` 形态另立一片（须对一般 `fC` 给出 `map φ fC ↔ coeffMap ≫ infl` 的桥）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]
variable {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

/-- ★★ **GS (6.17) 的兼容方块（`T`-变体）**：给定 `S : 0 → A → B → C → 0`（`G` 上）与
`SN : 0 → A^N → B^N → T → 0`（`G⧸N` 上，其前两项是 `S` 的前两项的不变子模），
以及 `fC : T →+ C` 在 `B^N` 上与 `S.proj` 一致，则

`SN.delta n ≫ map φ (A^N ↪ A) (n+1) = map φ fC n ≫ S.delta n`，`φ = G → G⧸N`。

**不要求** `0 → A^N → B^N → C^N → 0` 正合 —— 这正是它能用于本战役的原因。 -/
theorem delta_map_quotient_T (N : Subgroup G) [N.Normal]
    {T : Type u} [AddCommGroup T] [TopologicalSpace T] [DiscreteTopology T]
    [DistribMulAction (G ⧸ N) T]
    (S : DiscreteShortExact G A B C)
    (SN : DiscreteShortExact (G ⧸ N) (FixedPoints.addSubgroup N A)
      (FixedPoints.addSubgroup N B) T)
    (fC : T →+ C)
    (hfC : ∀ (g : G) (x : T), fC ((g : G ⧸ N) • x) = g • fC x)
    (hincl : ∀ a : FixedPoints.addSubgroup N A, (SN.incl a : B) = S.incl ↑a)
    (hproj : ∀ b : FixedPoints.addSubgroup N B, fC (SN.proj b) = S.proj ↑b)
    (n : ℕ) :
    SN.delta n ≫ ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom N)
        (ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom N : G →* G ⧸ N)
          (FixedPoints.addSubgroup N A).subtype.toIntLinearMap
          N.fixedPoints_subtype_quotientMk_smul) (n + 1) =
      ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom N)
        (ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom N : G →* G ⧸ N)
          fC.toIntLinearMap hfC) n ≫ S.delta n :=
  SN.delta_map S (Subgroup.quotientMkContinuousMonoidHom N)
    (FixedPoints.addSubgroup N A).subtype (FixedPoints.addSubgroup N B).subtype fC
    N.fixedPoints_subtype_quotientMk_smul N.fixedPoints_subtype_quotientMk_smul hfC hincl hproj n

end L20261018

#print axioms L20261018.delta_map_quotient_T
