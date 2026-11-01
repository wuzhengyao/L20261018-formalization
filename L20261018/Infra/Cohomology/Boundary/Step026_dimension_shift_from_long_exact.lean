import L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted
import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Acyclic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.ConnectingMap

/-!
# S41 R3（动作 V2 第一块）：**GS (6.15) 的核心** —— 长正合列给出的维数平移同构

## 本件在 GS §6.8 的哪一格

GS **Construction 6.8.1**（`cons-residue-map-finite-coefficients`，`raw/GilleSzamuely2017.tex:9475`）
构造 `∂^i : H^i(G,A) → H^{i-1}(G/H, H^1(H,A))`，其第一步是：把 `A` 嵌入余诱导模 `M^G(A)`，

```
0 → A → M^G(A) → C → 0                                    (6.14)
```

由 `M^G(A)` 的**零调性**（`H^j(G,M^G(A)) = 0`，`j > 0`）得

```
H^{i-1}(G, C) ≅ H^i(G, A)                                  (6.15)
```

—— GS 原文：「for `i ≥ 2` we get from the long exact sequence associated with (6.14)
isomorphisms `H^{i-1}(G,C) ≅ H^i(G,A)`」。

**本件把这半格抽象地机检**（对任意 `DiscreteShortExact G A B C` ＋ `B` 在相邻两度的零调性）：

| 声明 | 内容 |
|---|---|
| `delta_injective_of_subsingleton` | `Hⁿ(G,B)` 单点 ⟹ `δ_n` **单射**（用 `longExact_exact₃`：`ker δ_n = im(proj_*)`） |
| `delta_surjective_of_subsingleton` | `Hⁿ⁺¹(G,B)` 单点 ⟹ `δ_n` **满射**（用 `longExact_exact₁`：`range δ_n = ker(incl_*)`） |
| **`delta_bijective_of_subsingleton`** | 两者 ⟹ `δ_n` **双射** |
| **`deltaAddEquiv_of_subsingleton`** | ★★★ 打包成 `Hⁿ(G,C) ≃+ Hⁿ⁺¹(G,A)`（**即 (6.15)**） |

## 库内命中（本轮侦察，规则 23／L46）

| 件 | 位置 | 用途 |
|---|---|---|
| **`coindAcyclic`** | `Coinduced/Acyclic.lean:330` | ★★★ `IsZero (Hⁿ(G, Coind_1^G A))`（`n > 0`）＝ **`H^j(G,M^G(A)) = 0`** |
| `subsingleton_continuousCohomology_discreteCoind_bot` | 同文件（Main results） | 上述的 `Subsingleton` 形态 |
| `explicitInfl0/1/2` | `Inflation/Basic.lean:144,210,400` | **膨胀映射** `H^n(G ⧸ N, M^N) →+ H^n(G,M)` |
| `explicitInfl1_injective`／`explicitInfRes_exact` | `Inflation/Basic.lean:254,353` | 1 次的膨胀-限制正合：`range infl1 = ker res1` |
| `explicitInfRes2_exact` | `Inflation/Basic.lean:634` | 2 次（`N` 开、`H¹(N,M)` 单点） |
| **`DiscreteShortExact.delta_infl`** | `Inflation/ConnectingMap.lean` | ★★★ **膨胀与连接映射逐次交换** |
| `DiscreteCoind` 的可逆性／`transIso` | `Coinduced/Transitivity.lean:156` | 余诱导对子群的传递性（`H^j(H, Coind_1^G A)` 用） |
| `CohomologicalDimension/`（`ClosedSubgroup`／`OpenSubgroup`／`Basic`） | 目录 | `cd(H) ≤ 1` 的载体 |

## 诚实边界

* 本件**只做 (6.15) 那一格**（纯同调代数）。`∂^i` 的另两格
  （`inf` 是同构；`C^H → H^1(H,A)` 的 `G/H`-等变性）与 `∂_v` 的系数识别（Kummer ＋ 赋值）**未做**。
* 本件**不**触及 `Ch4TameSymbolHyp`；新路线的总设计图见 `S41-RECON-IV-GS68.md` §7.5。
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
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]
variable {B : Type} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

/-- ★★★ **`δ_n` 的单射性由 `Hⁿ(G,B)` 的零调性给出**（`ker δ_n = im(proj_*)`，`longExact_exact₃`）。 -/
theorem delta_injective_of_subsingleton (S : DiscreteShortExact G A B C) (n : ℕ)
    (hB : Subsingleton ↑(continuousCohomology n
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat) :
    Function.Injective ⇑(ConcreteCategory.hom (S.delta n)) := by
  intro x y hxy
  have h3 := S.longExact_exact₃ n
  rw [Function.Exact] at h3
  -- `δ_n x = 0` ⟹ `x = proj_* y = 0`
  have hx0 : ⇑(ConcreteCategory.hom (S.delta n)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hsub : x - y = 0 := by
    obtain ⟨w, hw⟩ := (h3 (x - y)).1 hx0
    rw [← hw]
    have : w = 0 := Subsingleton.elim w 0
    rw [this, map_zero]
  exact sub_eq_zero.1 hsub

/-- ★★★ **`δ_n` 的满射性由 `Hⁿ⁺¹(G,B)` 的零调性给出**（`range δ_n = ker(incl_*)`，`longExact_exact₁`）。 -/
theorem delta_surjective_of_subsingleton (S : DiscreteShortExact G A B C) (n : ℕ)
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

/-- ★★★★ **GS (6.15)**：`B` 在相邻两度零调 ⟹ `δ_n : Hⁿ(G,C) ≃ Hⁿ⁺¹(G,A)`。 -/
theorem delta_bijective_of_subsingleton (S : DiscreteShortExact G A B C) (n : ℕ)
    (h1 : Subsingleton ↑(continuousCohomology n
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (h2 : Subsingleton ↑(continuousCohomology (n + 1)
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat) :
    Function.Bijective ⇑(ConcreteCategory.hom (S.delta n)) :=
  ⟨delta_injective_of_subsingleton S n h1, delta_surjective_of_subsingleton S n h2⟩

/-- ★★★★★ **GS (6.15) 的等价形式**：`Hⁿ(G,C) ≃+ Hⁿ⁺¹(G,A)`。 -/
noncomputable def deltaAddEquiv_of_subsingleton (S : DiscreteShortExact G A B C) (n : ℕ)
    (h1 : Subsingleton ↑(continuousCohomology n
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (h2 : Subsingleton ↑(continuousCohomology (n + 1)
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat) :
    ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ G C)).toModuleCat ≃+
      ↑(continuousCohomology (n + 1) (TauCeti.ofDiscreteModule ℤ G A)).toModuleCat :=
  AddEquiv.ofBijective (S.delta n).hom.toLinearMap.toAddMonoidHom
    (delta_bijective_of_subsingleton S n h1 h2)

/-! ## 非空实例义务（L1 ＋ L10①）与判别力自证（L43）

`delta_bijective_of_subsingleton` 的两条假设**不是空类**：取 `B` 本身是单点模
（`[Subsingleton B]`）时，`H^n(G,B)` 自动单点，故定理给出**真实例**。
反之，去掉假设结论为**假**（例：`integralBocksteinShortExact G n` 的 `δ_1` 单射但不满射，
见 `Hyp483`），故本件的假设**承重**。 -/

/-- ★★★★ **非空见证**：`[Subsingleton B]` 时假设自动成立，定理给出真正的双射。 -/
theorem delta_bijective_of_subsingleton_witness [Subsingleton B]
    (S : DiscreteShortExact G A B C) (n : ℕ) :
    Function.Bijective ⇑(ConcreteCategory.hom (S.delta n)) := by
  haveI : Subsingleton (TauCeti.ofDiscreteModule ℤ G B).V := ‹Subsingleton B›
  exact delta_bijective_of_subsingleton S n
    (ContinuousCohomology.subsingleton_continuousCohomology_of_subsingleton
      (TauCeti.ofDiscreteModule ℤ G B) n)
    (ContinuousCohomology.subsingleton_continuousCohomology_of_subsingleton
      (TauCeti.ofDiscreteModule ℤ G B) (n + 1))

end L20261018

#print axioms L20261018.delta_bijective_of_subsingleton_witness
#print axioms L20261018.delta_injective_of_subsingleton
#print axioms L20261018.delta_surjective_of_subsingleton
#print axioms L20261018.delta_bijective_of_subsingleton
#print axioms L20261018.deltaAddEquiv_of_subsingleton
