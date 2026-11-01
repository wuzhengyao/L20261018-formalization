import L20261018.Infra.Cohomology.Coinduced.Step015_gs617_compatibility_square

/-!
# S65 R4：分片 **4c-ii** —— GS (6.17) 的 **SES1** 实体

```
SES1 :  0 → A^I → B^I → T → 0        （G ⧸ I 上的离散短正合列，T := B^I / A^I）
```

这是 GS (6.17) 的第一条，也是 `Hyp729.delta_map_quotient_T` 所需的 `SN`。
它的关键性质：中项 `B^I` 在 `G ⧸ I` 上**零调**（`Hyp728`），故 SES1 的联络同态 `δ²` 是**同构**。

## 内容

| 声明 | 内容 |
|---|---|
| `inclI` | `A^I →+ B^I`（`a ↦ S.incl ↑a`；`I`-不变性用 `S.incl_equivariant`） |
| `inclI_quotient_smul` | `G ⧸ I`-等变（`Hyp729` 的 `hincl` 的正合来源） |
| `TBI` | `T := B^I ⧸ (A^I 的像)`（`AddSubgroup` 商） |
| 实例 | `TopologicalSpace`／`DiscreteTopology`（离散）＋ `DistribMulAction (G⧸I)`（`quotientDistribMulAction`，稳定性由等变性给） |
| **`sesCoind1`** | ★ `DiscreteShortExact (G ⧸ I) (A^I) (B^I) T`（7 条字段全是标准引理） |
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

/-- `A^I →+ B^I`：`a ↦ S.incl ↑a`（`I`-不变性由 `S.incl` 的等变性给）。 -/
noncomputable def inclI (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal] :
    FixedPoints.addSubgroup (↥I) A →+ FixedPoints.addSubgroup (↥I) B where
  toFun a :=
    ⟨S.incl (a : A), (FixedPoints.mem_addSubgroup (↥I) B _).2 fun i => by
      have h1 : (i : G) • (a : A) = (a : A) := by
        simpa only [Subgroup.smul_def] using
          (FixedPoints.mem_addSubgroup (↥I) A (a : A)).1 a.2 i
      show i • S.incl (a : A) = S.incl (a : A)
      rw [Subgroup.smul_def, ← S.incl_equivariant, h1]⟩
  map_zero' := by
    refine Subtype.ext ?_
    simp only [AddSubgroup.coe_zero]
    exact map_zero S.incl
  map_add' a b := by
    refine Subtype.ext ?_
    simp only [AddSubgroup.coe_add]
    exact map_add S.incl (a : A) (b : A)

/-- `inclI` 的 `G ⧸ I`-等变性。 -/
theorem inclI_quotient_smul (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (q : G ⧸ I) (a : FixedPoints.addSubgroup (↥I) A) :
    inclI S I (q • a) = q • inclI S I a := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    refine Subtype.ext ?_
    show S.incl ((((g : G ⧸ I)) • a : FixedPoints.addSubgroup (↥I) A) : A) =
      (((g : G ⧸ I)) • inclI S I a : FixedPoints.addSubgroup (↥I) B)
    rw [TauCeti.coe_quotient_smul_fixedPoints_addSubgroup,
      TauCeti.coe_quotient_smul_fixedPoints_addSubgroup,
      TauCeti.coe_smul_fixedPoints_addSubgroup,
      TauCeti.coe_smul_fixedPoints_addSubgroup, S.incl_equivariant]
    rfl

/-- `T := B^I ⧸ (A^I 的像)`（GS (6.17) 的中间项）。 -/
noncomputable abbrev TBI (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal] : Type u :=
  FixedPoints.addSubgroup (↥I) B ⧸ (inclI S I).range

namespace TBI

variable (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]

noncomputable instance : TopologicalSpace (TBI S I) := ⊥
noncomputable instance : DiscreteTopology (TBI S I) := ⟨rfl⟩

/-- `(inclI S I).range` 在 `G ⧸ I`-作用下稳定。 -/
theorem range_stable (q : G ⧸ I) {x : FixedPoints.addSubgroup (↥I) B}
    (hx : x ∈ (inclI S I).range) : q • x ∈ (inclI S I).range := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨q • a, inclI_quotient_smul S I q a⟩

noncomputable instance : DistribMulAction (G ⧸ I) (TBI S I) :=
  AddSubgroup.quotientDistribMulAction _ (fun q _ hx => range_stable S I q hx)

end TBI

/-- ★★ **GS (6.17) 的 SES1**：`0 → A^I → B^I → T → 0`（`G ⧸ I` 上的离散短正合列）。 -/
noncomputable def sesCoind1 (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal] :
    DiscreteShortExact (G ⧸ I) (FixedPoints.addSubgroup (↥I) A)
      (FixedPoints.addSubgroup (↥I) B) (TBI S I) where
  incl := inclI S I
  proj := QuotientAddGroup.mk' _
  incl_equivariant := inclI_quotient_smul S I
  proj_equivariant := fun q b => rfl
  incl_injective := fun a b hab => by
    have h : S.incl (a : A) = S.incl (b : A) := congrArg Subtype.val hab
    exact Subtype.ext (S.incl_injective h)
  proj_surjective := QuotientAddGroup.mk'_surjective _
  exact := by
    rw [AddMonoidHom.exact_iff, QuotientAddGroup.ker_mk']

end L20261018

#print axioms L20261018.inclI
#print axioms L20261018.inclI_quotient_smul
#print axioms L20261018.sesCoind1
