import L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition

/-!
# S64 R18：GS `lemma-coinduced-invariants` 的**前进侧**

`(Coind_⊥^G A)^I`（**右平移**作用的 `I`-不变元）→ `G ⧸ I` 上的函数：`f ↦ (q ↦ f q.out)`。
`I` 正规 ⟹ 良定义（`f (x * i) = f x`）；局部常值用商拓扑（`f` 的每个纤维开且右 `I`-饱和）。

| 声明 | 内容 |
|---|---|
| `coindBot_apply_mul_of_mem` | `f ∈ (·)^I ⟹ f (x * i) = f x` |
| `coindInvFun` | 前进映射 `Quotient.lift (fun x => f x)` |
| `coindInvFun_isLocallyConstant` | 局部常值（商映射连续 ＋ 离散靶） |
| `coindBot_apply_out` | `f q.out = f x`（`q = mk x`），往返要用 |

反向（`F ↦ F ∘ mk`）与 `AddEquiv` 打包：卡点是 `DiscreteCoind (G ⧸ I) ⊥ A` 需要
`DistribMulAction (⊥ : Subgroup (G ⧸ I)) A`（`A` 只有 `G`-作用）⟹ 下一轮用显式平凡作用实例。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G]
variable (I : Subgroup G) [I.Normal]
variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]

/-- `I`-不变元的右平移不变性：`f (x * i) = f x`。 -/
theorem coindBot_apply_mul_of_mem {f : DiscreteCoind G ⊥ A}
    (hf : f ∈ FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A)) (x : G) (i : ↥I) :
    f (x * (i : G)) = f x := by
  have h := (FixedPoints.mem_addSubgroup (↥I) (DiscreteCoind G ⊥ A) f).1 hf i
  have hcoe : f (x * (i : G)) = (i • f) x := by
    rw [Subgroup.smul_def, DiscreteCoind.coe_smul]
  rw [hcoe, h]

/-- 前进映射：`f ↦ (q ↦ f q.out)`（`Quotient.lift` 形式，良定义靠右平移的 `I`-不变性）。 -/
noncomputable def coindInvFun (f : ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))) :
    G ⧸ I → A :=
  Quotient.lift (s := QuotientGroup.leftRel I) (fun x => (f : DiscreteCoind G ⊥ A) x) (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ I := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * ((⟨a⁻¹ * b, hmem⟩ : ↥I) : G) := by
      show b = a * (a⁻¹ * b)
      group
    rw [hb, coindBot_apply_mul_of_mem I f.2])

theorem coindInvFun_isLocallyConstant
    (f : ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))) :
    IsLocallyConstant (coindInvFun (I := I) f) := by
  rw [IsLocallyConstant.iff_continuous]
  have hmk : Topology.IsQuotientMap (QuotientGroup.mk' I) := isQuotientMap_quotient_mk'
  refine hmk.continuous_iff.mpr ?_
  have hcomp : ((coindInvFun (I := I) f) ∘ (QuotientGroup.mk' I))
      = fun x : G => (f : DiscreteCoind G ⊥ A) x := rfl
  rw [hcomp]
  exact ((DiscreteCoind.isLocallyConstant (f : DiscreteCoind G ⊥ A))).continuous

/-- `f` 在陪集代表上的值＝在原点的值。 -/
theorem coindBot_apply_out {f : DiscreteCoind G ⊥ A}
    (hf : f ∈ FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A)) (x : G) :
    f (Quotient.mk (QuotientGroup.leftRel I) x).out = f x := by
  set o : G := (Quotient.mk (QuotientGroup.leftRel I) x).out with ho
  have hmem : o⁻¹ * x ∈ I := by
    rw [ho]
    exact QuotientGroup.leftRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.leftRel I) x)))
  have hx : x = o * ((⟨o⁻¹ * x, hmem⟩ : ↥I) : G) := by
    show x = o * (o⁻¹ * x)
    group
  have hfx : f x = f o := by rw [hx, coindBot_apply_mul_of_mem I hf]
  exact hfx.symm

end L20261018

#print axioms L20261018.coindBot_apply_mul_of_mem
#print axioms L20261018.coindInvFun_isLocallyConstant
#print axioms L20261018.coindBot_apply_out
