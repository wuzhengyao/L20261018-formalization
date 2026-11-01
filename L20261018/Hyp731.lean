import L20261018.Hyp730
import L20261018.Hyp728

/-!
# S66 R1：分片 **4c-iii** —— `SES1` 的 `(δ¹)` 是**同构**（GS (6.17) 的中项零调）

`SES1 : 0 → Aᴵ → Bᴵ → T → 0`（`Hyp730.sesCoind1`，`T = TBI S I`）。本件证：

```
H¹(G⧸I, T)  ≃+  H²(G⧸I, Aᴵ)        （= (δ¹_{SES1})⁻¹ ∘ …）
```

由 `Hyp492.deltaAddEquiv_of_subsingleton`：只要中项 `Bᴵ` 在 `G⧸I` 上**相邻两度零调**。
而 `Bᴵ` 的零调性在战役里由 **4b**（`Hyp728`，`B = Coind_⊥^G A`）给 —— 见 §2 的兑现件。

## 4d 里它怎么用（方向检查，`M12`）

`delta_map_quotient_T`（`Hyp729`）的方块是
`δ¹_{SES1} ≫ Inf₂ = map φ fC 1 ≫ δ¹_Γ`。**因 `δ¹_{SES1}` 是同构**，可把它**消去**：

```
(δ¹_Γ)⁻¹ ∘ Inf₂ = map φ fC 1 ∘ (δ¹_{SES1})⁻¹
```

—— 这就是 4d 追图的第一格（把 `Inf₂` 从 `δ¹_Γ` 上搬到 `SES1` 一侧，代价是 `T`-系数）。
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

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]
variable {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

/-! ## 0 局部重推 `Hyp492` 的两条判据（避免 import 整条 `Hyp487`–`Hyp492` 链） -/

/-- `δ_n` 单射：`B` 在 `n` 度零调（`ker δ_n = im(incl_*)`）。与 `Hyp492` 同型。 -/
theorem delta_injective_sesCoind1 (S : DiscreteShortExact G A B C) (n : ℕ)
    (hB : Subsingleton ↑(continuousCohomology n
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat) :
    Function.Injective ⇑(ConcreteCategory.hom (S.delta n)) := by
  intro x y hxy
  have h3 := S.longExact_exact₃ n
  rw [Function.Exact] at h3
  have hx0 : ⇑(ConcreteCategory.hom (S.delta n)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hsub : x - y = 0 := by
    obtain ⟨w, hw⟩ := (h3 (x - y)).1 hx0
    rw [← hw]
    have : w = 0 := Subsingleton.elim w 0
    rw [this, map_zero]
  exact sub_eq_zero.1 hsub

/-- `δ_n` 满射：`B` 在 `n+1` 度零调（`range δ_n = ker(incl_*)`）。与 `Hyp492` 同型。 -/
theorem delta_surjective_sesCoind1 (S : DiscreteShortExact G A B C) (n : ℕ)
    (hB : Subsingleton ↑(continuousCohomology (n + 1)
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat) :
    Function.Surjective ⇑(ConcreteCategory.hom (S.delta n)) := by
  intro y
  have h1 := S.longExact_exact₁ n
  rw [Function.Exact] at h1
  have hzero : ⇑(ConcreteCategory.hom (ContinuousCohomology.coeffMap
      (TauCeti.ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 1))) y = 0 := by
    have hsingle : ⇑(ConcreteCategory.hom (ContinuousCohomology.coeffMap
        (TauCeti.ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 1))) y
        = 0 := Subsingleton.elim _ _
    exact hsingle
  exact (h1 y).mp hzero

/-- ★★★★ **GS (6.15)**（本件局部版）：`B` 相邻两度零调 ⟹ `δ_n` 可逆。 -/
theorem delta_bijective_sesCoind1 (S : DiscreteShortExact G A B C) (n : ℕ)
    (h1 : Subsingleton ↑(continuousCohomology n
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (h2 : Subsingleton ↑(continuousCohomology (n + 1)
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat) :
    Function.Bijective ⇑(ConcreteCategory.hom (S.delta n)) :=
  ⟨delta_injective_sesCoind1 S n h1, delta_surjective_sesCoind1 S n h2⟩

/-! ## 1 4c-iii：`δ¹_{SES1}` 是同构 -/

/-- ★★★★ **GS (6.17) 的 `δ¹` 可逆**：`H¹(G⧸I, T) ≃+ H²(G⧸I, Aᴵ)`，只要 `Bᴵ` 在 `G⧸I` 上
相邻两度零调（`hB1`／`hB2`）。

这就是 **4c-iii**：它把 4d 追图里的 `(δ¹_{SES1})` 变成可消去的同构。 -/
noncomputable def deltaAddEquiv_sesCoind1 (S : DiscreteShortExact G A B C)
    (I : Subgroup G) [I.Normal]
    (hB1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat)
    (hB2 : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat) :
    ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I) (TBI S I))).toModuleCat ≃+
      ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
        ↥(FixedPoints.addSubgroup (↥I) A))).toModuleCat :=
  AddEquiv.ofBijective ((sesCoind1 S I).delta 1).hom.toLinearMap.toAddMonoidHom
    (delta_bijective_sesCoind1 (sesCoind1 S I) 1 hB1 hB2)

/-- 4c-iii 的**值形态**（供 4d 直接用）：`δ¹_{SES1}` 的逆作用在 `H²(G⧸I,Aᴵ)` 上给出
`H¹(G⧸I,T)` 里的元素，且 `δ¹` 把它送回原元素。 -/
theorem delta_sesCoind1_apply_symm (S : DiscreteShortExact G A B C)
    (I : Subgroup G) [I.Normal]
    (hB1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat)
    (hB2 : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat)
    (x : ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) A))).toModuleCat) :
    (deltaAddEquiv_sesCoind1 S I hB1 hB2) ((deltaAddEquiv_sesCoind1 S I hB1 hB2).symm x) = x :=
  (deltaAddEquiv_sesCoind1 S I hB1 hB2).apply_symm_apply x

/-! ## 2 非空实例义务（`L1` ＋ `L10①`）

**战役里的兑现**：`B := contB`（余诱导模）时，`hB1`／`hB2` **就是 4b**
（`Hyp728.subsingleton_H_quot_coindBot_invariants`，GS `lemma-coinduced-invariants`）——
两者陈述的 `G⧸I`-模类型逐字一致（`↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))`），
故本件的假设类在战役里**非空**。（不在本文件内联实例化：`DiscreteCoind` ＋ `G ⧸ I` 的组合
令 `whnf` 超预算 —— 见 `PROMPT-S66` 坑 I 的同型。）

**机检的非空见证**（下面这条，与上式同型）：`[Subsingleton B]` 时假设自动成立。 -/

/-- ★★★★ **非空见证**：`B` 单点时 `hB1`／`hB2` 自动成立，`4c-iii` 给出**真正的同构**。 -/
noncomputable def deltaAddEquiv_sesCoind1_witness (S : DiscreteShortExact G A B C)
    (I : Subgroup G) [I.Normal] [Subsingleton B] :
    ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I) (TBI S I))).toModuleCat ≃+
      ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
        ↥(FixedPoints.addSubgroup (↥I) A))).toModuleCat := by
  haveI hBI : Subsingleton ↥(FixedPoints.addSubgroup (↥I) B) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim (x : B) (y : B))⟩
  haveI h1 : Subsingleton (TauCeti.ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B)).V := hBI
  have hS : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat :=
    ContinuousCohomology.subsingleton_continuousCohomology_of_subsingleton
      (TauCeti.ofDiscreteModule ℤ (G ⧸ I) ↥(FixedPoints.addSubgroup (↥I) B)) 2
  have hS1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat :=
    ContinuousCohomology.subsingleton_continuousCohomology_of_subsingleton
      (TauCeti.ofDiscreteModule ℤ (G ⧸ I) ↥(FixedPoints.addSubgroup (↥I) B)) 1
  exact deltaAddEquiv_sesCoind1 S I hS1 hS

end L20261018

#print axioms L20261018.delta_injective_sesCoind1
#print axioms L20261018.delta_surjective_sesCoind1
#print axioms L20261018.delta_bijective_sesCoind1
#print axioms L20261018.deltaAddEquiv_sesCoind1
#print axioms L20261018.delta_sesCoind1_apply_symm
#print axioms L20261018.deltaAddEquiv_sesCoind1_witness
