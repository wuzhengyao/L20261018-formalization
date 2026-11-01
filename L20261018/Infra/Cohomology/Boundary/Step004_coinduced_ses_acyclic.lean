import L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient
import L20261018.Infra.Cohomology.Boundary.Step001_acyclicity_short_exact

/-!
# R1077（**★ (R2) 建造 H-5-1 完成**）：GS 6.8.5 的短正合列 `0 → A → M^G(A) → C → 0` 与其零调性

GS 6.8.5（`cons-residue-map-finite-coefficients`）的构造需要短正合列
`0 → A → M^G(A) → C → 0`，其中 `M^G(A) = DiscreteCoind G ⊥ A`（余诱导模），`C` 为商。本文件把它造出来：

| 声明 | 内容 |
|---|---|
| **`Q`** | 商 `(DiscreteCoind G ⊥ A) ⧸ coindSub`（类型写成**记法形式**，见下） |
| **`SMul G Q`**／**`smul_mk`**（`rfl`）／**`DistribMulAction G Q`**（四字段） | 商上的 `G`-作用（良定义性 = `coindSub_stable`） |
| **`proj_equivariant`** | 商映射的 `G`-等变 |
| **`coindShortExact`** | **`DiscreteShortExact G A (DiscreteCoind G ⊥ A) Q`**（六项齐全，正中正合由 `proj_eq_zero_iff`） |
| **`subsingleton_cohomology_quot`** | **`H^j(G, C) = 0`（`j ≥ 1`）**，只需 `cd(G)≤1` 的 `hA`（接 `Hyp210`） |

**★ 关键工艺（R1076 诊断的三条结论的落地）**：`SMul`／`DistribMulAction` 实例的类型**必须写成记法形式**
`(DiscreteCoind G ⊥ A) ⧸ (coindSub …)`，**不能**写成 `Quotient (leftRel …)` ——
否则实例搜索在 `.instances` 透明度下不匹配（`def` 不展开），且 `rw [Quotient.map_mk]` 会报
"not type-correct under the `implicit` transparency level"。写成记法形式后，计算规则 `smul_mk` 是 **`rfl`**。
-/

set_option maxHeartbeats 5000000
set_option pp.proofs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018


variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

abbrev Q : Type := (DiscreteCoind G ⊥ A) ⧸ (coindSub (G := G) (A := A))

instance : SMul G (Q (G := G) (A := A)) where
  smul g := Quotient.map (fun m => g • m) (by
    intro m₁ m₂ h
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    have h' : -m₁ + m₂ ∈ coindSub (G := G) (A := A) := QuotientAddGroup.leftRel_apply.mp h
    have h'' := coindSub_stable (G := G) (A := A) g h'
    simpa [smul_add, smul_neg] using h'')

theorem smul_mk (g : G) (m : DiscreteCoind G ⊥ A) :
    (g • (QuotientAddGroup.mk m : Q (G := G) (A := A))) = QuotientAddGroup.mk (g • m) := rfl

instance : DistribMulAction G (Q (G := G) (A := A)) where
  one_smul q := by
    induction q using QuotientAddGroup.induction_on with
    | _ z => rw [smul_mk, one_smul]
  mul_smul g h q := by
    induction q using QuotientAddGroup.induction_on with
    | _ z => rw [smul_mk, smul_mk, smul_mk, mul_smul]
  smul_zero g := by
    rw [show (0 : Q (G := G) (A := A)) = QuotientAddGroup.mk (0 : DiscreteCoind G ⊥ A) from rfl,
      smul_mk, smul_zero]
  smul_add g q r := by
    induction q using QuotientAddGroup.induction_on with
    | _ z =>
      induction r using QuotientAddGroup.induction_on with
      | _ w =>
        rw [show (QuotientAddGroup.mk z + QuotientAddGroup.mk w : Q (G := G) (A := A))
            = QuotientAddGroup.mk (z + w) from rfl, smul_mk, smul_mk, smul_mk, smul_add]
        rfl

theorem proj_equivariant (g : G) (m : DiscreteCoind G ⊥ A) :
    CoindQuot.proj (G := G) (A := A) (g • m) = g • CoindQuot.proj (G := G) (A := A) m :=
  (smul_mk g m).symm

/-- **GS 6.8.5 的短正合列** `0 → A → M^G(A) → C → 0`。 -/
def coindShortExact : ContCohomology.DiscreteShortExact G A (DiscreteCoind G ⊥ A) (Q (G := G) (A := A)) where
  incl := coindIncl (G := G) (A := A)
  proj := CoindQuot.proj (G := G) (A := A)
  incl_equivariant := fun g a => coindIncl_equivariant g a
  proj_equivariant := fun g m => proj_equivariant g m
  incl_injective := coindIncl_injective
  proj_surjective := CoindQuot.proj_surjective
  exact := fun m => CoindQuot.proj_eq_zero_iff (G := G) (A := A) m

/-- **H-5-1 终段**：`H^j(H, C) = 0`（`j ≥ 1`），由 `cd(H) ≤ 1`（`hA`）给出。 -/
theorem subsingleton_cohomology_quot
    (hA : ∀ k, 2 ≤ k → Subsingleton (continuousCohomology k (ofDiscreteModule ℤ G A)))
    {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (continuousCohomology j (ofDiscreteModule ℤ G (Q (G := G) (A := A)))) :=
  subsingleton_cohomology_three_of_coind (A := A) (C := Q (G := G) (A := A))
    (coindShortExact (G := G) (A := A)) hA hj

end L20261018
#print axioms L20261018.subsingleton_cohomology_quot
