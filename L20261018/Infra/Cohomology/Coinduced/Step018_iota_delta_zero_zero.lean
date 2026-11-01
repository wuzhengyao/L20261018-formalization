import L20261018.Infra.Cohomology.Coinduced.Step017_ses1_delta_one_iso

/-!
# S66 R2：分片 **4c-iv** —— `ι : T → Cᴵ` 与 `δ⁰ ∘ proj_* = 0`

`SES1 : 0 → Aᴵ → Bᴵ → T → 0`（`Hyp730.sesCoind1`，`T = TBI S I`）。4d 追图需要第三件：

```
ι : T →+ Cᴵ            （T = Bᴵ / Aᴵ，元素层：ι (mk b) = S.proj b）
M ∘ ι = 0              （M = δ⁰_I，即 SES 限制到 ↥I 后的连结映射）
```

**本件把 `M ∘ ι = 0` 归约成库内一条现成定理**（`L47`：库内已有优先于自建）：

* `M ∘ (proj 的诱导映射) = 0` **就是** `DiscreteShortExact.coeffMap_proj_comp_delta`
  （`HomologySequence.lean:252`：`coeffMap (S.proj) n ≫ S.delta n = 0`，即 `ker δ_n ⊇ im(proj_*)`）；
* 把 `projI`（不变点上的 `S.proj`）与 `coeffMap (S.proj) 0` 接上，用
  `explicitH0Iso_coeffMap`（`ContinuousCohomologyIso.lean:290`，`H⁰` 比较同构与系数映射交换）。

## 为什么**不需要**造 SES2（省空转记录）

`PROMPT-S66` §①-2 曾把 4c-iv 写成「造 `SES2 : 0 → T → Cᴵ → H¹(I,A) → 0` 并证正合」。
本轮侦察发现 **不需要**：`M ∘ ι = 0` 只用到 **`SES1` 与 `S` 自身**，
载体是库内的 `coeffMap_proj_comp_delta` ＋ `H⁰`-比较的系数自然性。
`SES2` 的正合性（`coker = H¹(I,A)`）在 4d 追图里**也用不到** —— 4d 只用 `M ∘ ι = 0`。
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

/-! ## 1 `projI : Bᴵ →+ Cᴵ` -/

/-- ★★ **`S.proj` 在 `I`-不变点上的限制**：`Bᴵ →+ Cᴵ`。
良定义性：`b` 被 `I` 固定 ⟹ `S.proj b` 被 `I` 固定（`S.proj_equivariant`）。 -/
noncomputable def projI (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal] :
    FixedPoints.addSubgroup (↥I) B →+ FixedPoints.addSubgroup (↥I) C where
  toFun b :=
    ⟨S.proj (b : B), (FixedPoints.mem_addSubgroup (↥I) C _).2 fun i => by
      have h1 : (i : G) • (b : B) = (b : B) := by
        simpa only [Subgroup.smul_def] using
          (FixedPoints.mem_addSubgroup (↥I) B (b : B)).1 b.2 i
      show i • S.proj (b : B) = S.proj (b : B)
      rw [Subgroup.smul_def, ← S.proj_equivariant, h1]⟩
  map_zero' := by
    refine Subtype.ext ?_
    simp only [AddSubgroup.coe_zero]
    exact map_zero S.proj
  map_add' x y := by
    refine Subtype.ext ?_
    simp only [AddSubgroup.coe_add]
    exact map_add S.proj (x : B) (y : B)

/-- `projI` 的取值公式。 -/
@[simp]
theorem projI_apply (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (b : FixedPoints.addSubgroup (↥I) B) :
    ((projI S I b : FixedPoints.addSubgroup (↥I) C) : C) = S.proj (b : B) := rfl

/-- `projI` 的 `G ⧸ I`-等变性。 -/
theorem projI_quotient_smul (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (q : G ⧸ I) (b : FixedPoints.addSubgroup (↥I) B) :
    projI S I (q • b) = q • projI S I b := by
  refine Subtype.ext ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    show S.proj ((((g : G ⧸ I)) • b : FixedPoints.addSubgroup (↥I) B) : B)
      = (((g : G ⧸ I)) • projI S I b : FixedPoints.addSubgroup (↥I) C)
    rw [TauCeti.coe_quotient_smul_fixedPoints_addSubgroup,
      TauCeti.coe_quotient_smul_fixedPoints_addSubgroup,
      TauCeti.coe_smul_fixedPoints_addSubgroup,
      TauCeti.coe_smul_fixedPoints_addSubgroup, S.proj_equivariant]
    rfl

/-- `projI ∘ inclI = 0`：`S.proj ∘ S.incl = 0`（`S` 的正合性）。 -/
theorem projI_comp_inclI (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (a : FixedPoints.addSubgroup (↥I) A) :
    projI S I (inclI S I a) = 0 := by
  refine Subtype.ext ?_
  show S.proj (S.incl (a : A)) = (0 : C)
  exact (S.exact (S.incl (a : A))).2 ⟨(a : A), rfl⟩

/-! ## 2 `ι : T →+ Cᴵ`（由 `projI` 过商） -/

/-- ★★★ **`ι : T = Bᴵ/im(Aᴵ) →+ Cᴵ`**（GS (6.17) 的第三项映射；元素层 `ι (mk b) = S.proj b`）。

**注意**：它是 4d 追图里 `M ∘ ι = 0` 的那个 `ι` —— 不是 `SES2` 的入射。 -/
noncomputable def iota (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal] :
    TBI S I →+ FixedPoints.addSubgroup (↥I) C :=
  QuotientAddGroup.lift (inclI S I).range (projI S I) (fun x hx => by
    obtain ⟨a, rfl⟩ := hx
    exact projI_comp_inclI S I a)

/-- `ι` 的取值公式：`ι (mk b) = projI b`。 -/
@[simp]
theorem iota_mk (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (b : FixedPoints.addSubgroup (↥I) B) :
    iota S I (QuotientAddGroup.mk' (inclI S I).range b) = projI S I b :=
  rfl

/-- `ι` 的 `G ⧸ I`-等变性。 -/
theorem iota_quotient_smul (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (q : G ⧸ I) (x : TBI S I) : iota S I (q • x) = q • iota S I x := by
  induction x using QuotientAddGroup.induction_on with
  | H b =>
    change iota S I (QuotientAddGroup.mk' (inclI S I).range (q • b))
      = q • iota S I (QuotientAddGroup.mk' (inclI S I).range b)
    rw [iota_mk, iota_mk, projI_quotient_smul]

/-! ## 3 一般形式：`δ_n ∘ proj_* = 0`（库内 `coeffMap_proj_comp_delta`） -/

/-- ★★★★ **`δ⁰` 杀死 `proj` 的像**：`(S.restrict I).delta 0` 在 `coeffMap (S.proj) 0` 的像上为 0。

这是 `M ∘ ι = 0` 的**全部数学内容**（`M = δ⁰_I`）：直接引用库内
`DiscreteShortExact.coeffMap_proj_comp_delta`。 -/
theorem restrict_delta_zero_comp_projCoeff (S : DiscreteShortExact G A B C)
    (I : Subgroup G) [I.Normal] [CompactSpace ↥I] [ContinuousSMul ↥I B]
    [IsTopologicalAddGroup B] [IsTopologicalAddGroup C]
    (y : ↑(continuousCohomology 0 (ofDiscreteModule ℤ (↥I) B)).toModuleCat) :
    (S.restrict I).delta 0
        ((ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap (S.restrict I).proj.toIntLinearMap
            (S.restrict I).proj_equivariant) 0) y) = 0 := by
  have h := DiscreteShortExact.coeffMap_proj_comp_delta (S.restrict I) 0
  exact ConcreteCategory.congr_hom h y

/-- ★★ **`S.proj` 视作 `↥I`-等变加性映射**（`B →+[↥I] C`）—— `H⁰`-比较的系数自然性需要一个
`G`-等变映射，而 `S.proj` 的等变性本是逐点假设，故在此打包。 -/
noncomputable def projRestr (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal] :
    B →+[↥I] C where
  toFun := S.proj
  map_zero' := map_zero S.proj
  map_add' := map_add S.proj
  map_smul' i b := by
    show S.proj (i • b) = i • S.proj b
    simpa only [Subgroup.smul_def] using S.proj_equivariant (i : G) b

/-- `projI` 与 `coeffMap (S.proj) 0` 在 `H⁰`-比较下一致：
`h0Bridge (projI b) = coeffMap (S.proj) 0 (h0Bridge b)`。

由 `explicitH0Iso_coeffMap`（`H⁰` 比较同构与系数映射交换）＋ `explicitCoeff0` 在不变点上的取值公式
（在不变点上 `explicitCoeff0 (S.proj) ⟨b⟩ = ⟨S.proj b⟩ = projI b`，`rfl` 级）。 -/
theorem h0Bridge_projI (S : DiscreteShortExact G A B C)
    (I : Subgroup G) [I.Normal] [IsTopologicalAddGroup B] [IsTopologicalAddGroup C]
    (b : FixedPoints.addSubgroup (↥I) B) :
    (explicitH0IsoContinuousCohomology (↥I) C).hom (projI S I b)
      = (ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap (projRestr S I).toAddMonoidHom.toIntLinearMap
            (fun i m => map_smul (projRestr S I) i m)) 0)
        ((explicitH0IsoContinuousCohomology (↥I) B).hom b) := by
  rw [explicitH0Iso_coeffMap (↥I) B C (projRestr S I) b]
  congr 1

end L20261018

#print axioms L20261018.projI
#print axioms L20261018.projI_apply
#print axioms L20261018.projI_quotient_smul
#print axioms L20261018.projI_comp_inclI
#print axioms L20261018.iota
#print axioms L20261018.iota_mk
#print axioms L20261018.iota_quotient_smul
#print axioms L20261018.projRestr
#print axioms L20261018.restrict_delta_zero_comp_projCoeff
#print axioms L20261018.h0Bridge_projI
