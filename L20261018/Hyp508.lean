import Hyp504
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Procyclic

/-!
# S42 R8（（★）的**最弱充分条件**）：`I` 的 `p`-Sylow **procyclic ＋ 非挠** ⟹ `cd_p(I) ≤ 1`

## 本件在（★）的哪一格

（★）＝「惯性群的最大 pro-`p` 商 ≅ `ℤ_p`」，S42 R2 把它 type-locked 成
`InertiaProPSylowData`（`∃ P, IsProPSylow p P ∧ ↥P ≃ₜ* ℤ_p`）。
R7 已机检**有限层**（`Hyp507`：各层 `ℓ`-Sylow 循环，`ℓ ≠ char κ`）。
本件把（★）**再降一档**：只需 Sylow 是 **procyclic（由一个元素拓扑生成）且该元素非挠** ——
这正是「驯惯性 `I_t ≅ lim← μ_n` 的 `p`-部分」的最弱抽象形态，
且**由 TauCeti 的 `IsProP.padicPowEquiv` 一步给出** `↥P ≃ₜ* ℤ_p`。

## 机制（一步）

```
Pro-p 群 P 由 a 拓扑生成（closure{a}.topologicalClosure = ⊤）且 a 非挠
  ⟹ Multiplicative ℤ_[p] ≃ₜ* P            -- TauCeti.IsProP.padicPowEquiv
  ⟹ InertiaProPSylowData I p               -- 取 Symm
  ⟹ cd_p(I) ≤ 1, H²(I,μ_p) = 0            -- Hyp504
```

## 为什么这是「最弱」形态

* Serre Ch. IV §2 Cor 1（R6 目视；R7 已在 TauCeti）给有限层：`G_0/G_1` 循环、`G_1` 是 `p`-群；
* （★）的经典形态 `I_t ≅ lim←_n μ_n` ⟹ 其 pro-`p` 部分 ≅ `lim←_k ℤ/p^k = ℤ_p`，
  而后者**正是**「procyclic ＋ 非挠」（`lim← ℤ/p^k` 的自然生成元是 `(1 mod p^k)_k`，非挠）。
⟹ 本件之后，**(★) 只剩一个纯群论＋数论的陈述要用逆极限去证**：
「`I` 的 `p`-Sylow 是 procyclic 的、且其生成元非挠」。
（`procyclic` 那一半由 `Hyp507` ＋ `limitSubgroup` 的逆极限给出；`非挠` 那一半需要
「`K` 有任意高次的驯分歧扩张」，即 `K(π^{1/p^n})/K` 的 Eisenstein 性。见 `S42-ROUTE2.md`。）

## 诚实边界

* 本件**不证明** procyclic／非挠；（★）仍**未**机检。
* 本件**不**触及 `KnrResidueObligation`。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable {p : ℕ} [Fact p.Prime]

/-- ★★★★ **procyclic pro-`p` ＋ 非挠生成元 ⟹ `P ≅ₜ* ℤ_p`**（TauCeti `IsProP.padicPowEquiv`）。 -/
noncomputable def padicEquiv_of_procyclic {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P]
    (hP : IsProP p P) (a : P)
    (ha : (Subgroup.closure ({a} : Set P)).topologicalClosure = ⊤) (hfin : ¬ IsOfFinOrder a) :
    P ≃ₜ* Multiplicative ℤ_[p] :=
  (hP.padicPowEquiv ha hfin).symm

/-- ★★★★★ **（★）的 type-locked 数据由「procyclic ＋ 非挠」给出**。 -/
noncomputable def inertiaProPSylowData_of_procyclic {I : Type} [Group I] [TopologicalSpace I]
    [IsTopologicalGroup I] [CompactSpace I] [TotallyDisconnectedSpace I]
    (P : Subgroup I) (hP : IsProPSylow p P) (a : P)
    (ha : (Subgroup.closure ({a} : Set P)).topologicalClosure = ⊤) (hfin : ¬ IsOfFinOrder a) :
    InertiaProPSylowData I p where
  P := P
  isProPSylow := hP
  padicEquiv := by
    haveI : CompactSpace ↥P := isCompact_iff_compactSpace.mp hP.isClosed.isCompact
    exact ⟨padicEquiv_of_procyclic hP.isProP a ha hfin⟩

/-- ★★★★★ **（★）⟸「procyclic ＋ 非挠」⟹ `cd_p(I) ≤ 1`**（经 `Hyp504`）。 -/
theorem cdLE_of_procyclic {I : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [CompactSpace I] [TotallyDisconnectedSpace I]
    (P : Subgroup I) (hP : IsProPSylow p P) (a : P)
    (ha : (Subgroup.closure ({a} : Set P)).topologicalClosure = ⊤) (hfin : ¬ IsOfFinOrder a) :
    CohomologicalDimensionLE.{0, 0} p I 1 :=
  (inertiaProPSylowData_of_procyclic P hP a ha hfin).cdLE

/-- ★★★★ **`H²(I, M) = 0`**（`M` 为 `p`-primary 挠）由「procyclic ＋ 非挠」直接得到。 -/
theorem subsingleton_H2_of_procyclic {I : Type} [Group I] [TopologicalSpace I]
    [IsTopologicalGroup I] [CompactSpace I] [TotallyDisconnectedSpace I]
    (P : Subgroup I) (hP : IsProPSylow p P) (a : P)
    (ha : (Subgroup.closure ({a} : Set P)).topologicalClosure = ⊤) (hfin : ¬ IsOfFinOrder a)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction I M] [ContinuousSMul I M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ I M)) :=
  (inertiaProPSylowData_of_procyclic P hP a ha hfin).subsingleton_H2 M hM



/-- ★★★★★ **「拓扑生成元非挠」由「群无限」给出**：若 `P` 由 `a` 拓扑生成且 `P` 无限，
则 `a` 不是有限阶（`IsOfFinOrder.finite_zpowers` ＋ 有限集在 `T1` 中闭 ＋ 闭包 = 自身）。 -/
-- @source file=scratch/lean-l20261018/serre-p67-prop7-cors.txt locator=line:8 quote="The group G_0/G_1 is cyclic, and is mapped isomorphically by theta_0 onto a subgroup of the group of roots of unity contained in L. Its order is prime to the characteristic of the residue field L."
theorem not_isOfFinOrder_of_infinite {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [T1Space P] (a : P)
    (ha : (Subgroup.closure ({a} : Set P)).topologicalClosure = ⊤) [Infinite P] :
    ¬ IsOfFinOrder a := by
  intro hfo
  -- `closure {a} = zpowers a` 有限
  have hzp : Subgroup.zpowers a = Subgroup.closure ({a} : Set P) := Subgroup.zpowers_eq_closure a
  have hfinT : Finite ↥(Subgroup.closure ({a} : Set P)) := hzp ▸ hfo.finite_zpowers
  have hfin : (Subgroup.closure ({a} : Set P) : Set P).Finite := Set.finite_coe_iff.mpr hfinT
  -- 有限 ⟹ 闭 ⟹ 闭包 = 自身
  have hclosed : IsClosed ((Subgroup.closure ({a} : Set P)) : Set P) := hfin.isClosed
  have hself : (Subgroup.closure ({a} : Set P)).topologicalClosure
      = Subgroup.closure ({a} : Set P) :=
    le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl hclosed)
      (Subgroup.le_topologicalClosure _)
  -- 于是 `⊤` 有限，与 `Infinite P` 矛盾
  rw [hself] at ha
  have htop : Finite ↥(⊤ : Subgroup P) := ha ▸ hfinT
  have hP : Finite P := Finite.of_injective (fun x : P => (⟨x, trivial⟩ : ↥(⊤ : Subgroup P)))
    (fun x y h => Subtype.ext_iff.mp h)
  exact (not_finite_iff_infinite.mpr ‹Infinite P›) hP

/-- ★★★★★ **（★）⟸「Sylow pro-`p` ＋ procyclic ＋ 无限」**（最弱形态的最终版）。 -/
noncomputable def inertiaProPSylowData_of_procyclic_infinite {I : Type} [Group I]
    [TopologicalSpace I] [IsTopologicalGroup I] [CompactSpace I] [TotallyDisconnectedSpace I]
    [T1Space I] (P : Subgroup I) (hP : IsProPSylow p P) [Infinite ↥P] (a : P)
    (ha : (Subgroup.closure ({a} : Set P)).topologicalClosure = ⊤) :
    InertiaProPSylowData I p :=
  inertiaProPSylowData_of_procyclic P hP a ha (not_isOfFinOrder_of_infinite a ha)

end L20261018

#print axioms L20261018.not_isOfFinOrder_of_infinite
#print axioms L20261018.inertiaProPSylowData_of_procyclic_infinite
#print axioms L20261018.padicEquiv_of_procyclic
#print axioms L20261018.inertiaProPSylowData_of_procyclic
#print axioms L20261018.cdLE_of_procyclic
#print axioms L20261018.subsingleton_H2_of_procyclic
