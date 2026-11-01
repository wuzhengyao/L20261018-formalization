import L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier

/-!
# S46 R2：★★★★★ **连续 (F1)** —— `δ_T ≫ Inf_A = (i ≫ Inf_C) ≫ δ_Γ`

## 这一步在 GS 的哪一句

GS `prop-residue-map-long-exact`（6.8.2）证明**末句**逐字（`raw/GilleSzamuely2017.tex:9538–9541`）：

> The fact that the maps `H^{i}(G/H,A^{H})\to H^{i}(G,A)` are indeed the usual inflation maps
> follows from an easy compatibility between inflations and boundary maps in long exact
> sequences, which readers may check for themselves.

其**机检形态**（离散侧 = `Hyp543.delta_coind_comp_infl`）就是

```
δ_T ≫ Inf_A  =  (i_* ≫ Inf_C) ≫ δ_Γ
```

## 工具（**全部库内，零自建数学**）

| 用 | 件 | 位置 |
|---|---|---|
| **跨群方块** | `TauCeti.ContCohomology.DiscreteShortExact.delta_map` | `ContCohomology/HomologySequence.lean:351` |
| 样板（同构型的连续件，`SN` 版） | `DiscreteShortExact.delta_infl` | `ContCohomology/Inflation/ConnectingMap.lean:69` |
| `I`-不变点的 `Γ⧸I`-作用 | `Subgroup.fixedPoints_subtype_quotientMk_smul` | mathlib |
| `Inf` 的 `coeffMap` 分解 | `coeffMap_ofDiscreteModuleQuotient_comp_infl` | `Inflation/Comparison.lean:95` |
| 商 `lift` | `QuotientAddGroup.lift`／`lift_mk` | mathlib |

## 机检内容

| 声明 | 内容 |
|---|---|
| `contProjInv`／`contProjInv_coe` | `Bᴵ → Cᴵ`（`S.proj` 在不变点上的限制） |
| `contProjInv_smul` | 其 `Γ⧸I`-等变性 |
| `contKI_le_ker_contProjInv` | `S.proj ∘ S.incl = 0` 的 `T`-层形态 |
| **`contITame`** | ★★ **GS (6.17) 左半**：`i : T → Cᴵ`（`S.proj` 经余核下降） |
| `contITame_mk`／`contITame_smul` | 代表元上的值 ＋ `Γ⧸I`-等变性 |
| **`contFC`／`contFC_eq`／`contFC_smul`** | `fC = (Cᴵ ↪ C) ∘ i` ＋ 沿 `φ` 的等变（`hC`） |
| **`contF1`** | ★★★★★ **连续 (F1)**：`δ_T ≫ map φ fA = map φ fC ≫ δ_Γ` |
| **`contF1_infl`** | ★★★ 左端拆成 `coeffMap (quot) ≫ infl`（接 `(d)` 的接口） |

## 诚实边界

* 本件**只拆了左端**：右端的 `map φ fC` 尚未拆成 `i_* ≫ Inf_C`（下一件 `Hyp554`；
  那需要 `ContinuousCohomology.map_comp` ＋ `contFC_eq`）。**没有那步 (d) 还不能收口。**
* 本件**不**含 `i` 的单射性（GS (6.17) 右半所需，`Hyp554` 一并做）。
* 本件**不**用 `H²(I,μ_p) = 0` 一类假设：(F1) 与离散侧一样是**无条件**的。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- ★★★ `Bᴵ → Cᴵ`：`S.proj` 在 `I`-不变点上的限制（`S.proj` 等变 ⟹ 良定义）。 -/
noncomputable def contProjInv : contInvB (F := F) p I →+ contInvC (F := F) p I where
  toFun b :=
    ⟨(contCoindSES (F := F) p).proj (b : contB (F := F) p), by
      rw [FixedPoints.mem_addSubgroup]
      intro i
      show (i : AbsoluteGaloisGroup F) •
          (contCoindSES (F := F) p).proj (b : contB (F := F) p)
        = (contCoindSES (F := F) p).proj (b : contB (F := F) p)
      rw [← (contCoindSES (F := F) p).proj_equivariant (i : AbsoluteGaloisGroup F)
        (b : contB (F := F) p)]
      congr 1
      exact (FixedPoints.mem_addSubgroup (↥I) (contB (F := F) p) (b : contB (F := F) p)).mp b.2 i⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- `contProjInv` 的底层就是 `S.proj`（供下游 `rw`）。 -/
@[simp]
theorem contProjInv_coe (b : contInvB (F := F) p I) :
    ((contProjInv (F := F) p I b : contInvC (F := F) p I) : contC (F := F) p)
      = (contCoindSES (F := F) p).proj (b : contB (F := F) p) := (rfl)

/-- ★★ `contProjInv` 沿 `Γ⧸I`-作用等变。 -/
theorem contProjInv_smul (q : (AbsoluteGaloisGroup F) ⧸ I) (b : contInvB (F := F) p I) :
    contProjInv (F := F) p I (q • b) = q • contProjInv (F := F) p I b := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective I q
  apply Subtype.ext
  change (contCoindSES (F := F) p).proj
      ((FixedPoints.addSubgroup (↥I) (contB (F := F) p)).subtype
        (I.quotientMkContinuousMonoidHom h • b))
    = (FixedPoints.addSubgroup (↥I) (contC (F := F) p)).subtype
        (I.quotientMkContinuousMonoidHom h • contProjInv (F := F) p I b)
  rw [I.fixedPoints_subtype_quotientMk_smul (M := contB (F := F) p),
    I.fixedPoints_subtype_quotientMk_smul (M := contC (F := F) p)]
  exact (contCoindSES (F := F) p).proj_equivariant h (b : contB (F := F) p)

/-- `contKI` 落在 `contProjInv` 的核里（`S.proj ∘ S.incl = 0`）。 -/
theorem contKI_le_ker_contProjInv :
    contKI (F := F) p I ≤ (contProjInv (F := F) p I).ker := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_contKI (F := F) p I).mp hx
  show contProjInv (F := F) p I (contInvIncl (F := F) p I a) = 0
  apply Subtype.ext
  show (contCoindSES (F := F) p).proj
      ((contInvIncl (F := F) p I a : contInvB (F := F) p I) : contB (F := F) p) = 0
  rw [contInvIncl_coe, (contCoindSES (F := F) p).proj_incl]

/-- ★★ **GS (6.17) 的左半**：`i : T = Bᴵ⧸Aᴵ → Cᴵ`，由 `S.proj` 经余核下降得到。 -/
noncomputable def contITame : contT (F := F) p I →+ contInvC (F := F) p I :=
  QuotientAddGroup.lift (contKI (F := F) p I) (contProjInv (F := F) p I)
    (contKI_le_ker_contProjInv (F := F) p I)

/-- `contITame` 在代表元上的值：`i(mk b) = S.proj b`（`lift` 的计算律）。 -/
theorem contITame_mk (b : contInvB (F := F) p I) :
    contITame (F := F) p I (b : contT (F := F) p I) = contProjInv (F := F) p I b := (rfl)

/-- ★★ `contITame` 沿 `Γ⧸I`-作用等变。 -/
theorem contITame_smul (q : (AbsoluteGaloisGroup F) ⧸ I) (c : contT (F := F) p I) :
    contITame (F := F) p I (q • c) = q • contITame (F := F) p I c := by
  induction c using QuotientAddGroup.induction_on with
  | _ b =>
    rw [AddSubgroup.quotientDistribMulAction_smul_mk (contKI (F := F) p I)
      (contKI_stable (F := F) p I) q b, contITame_mk, contITame_mk, contProjInv_smul]

/-- **`fC : T → C`**：`i` 后接 `Cᴵ ↪ C`（`delta_map` 的 `fC`）。 -/
noncomputable def contFC : contT (F := F) p I →+ contC (F := F) p :=
  (FixedPoints.addSubgroup (↥I) (contC (F := F) p)).subtype.comp (contITame (F := F) p I)

/-- `contFC` 的分解式：`fC = (Cᴵ ↪ C) ∘ i`（GS (6.17) 与 (F1) 的接口）。 -/
theorem contFC_eq :
    contFC (F := F) p I
      = (FixedPoints.addSubgroup (↥I) (contC (F := F) p)).subtype.comp
          (contITame (F := F) p I) := (rfl)

/-- ★★ `contFC` 沿 `φ` 等变（`delta_map` 的 `hC`）。 -/
theorem contFC_smul : ∀ (h : AbsoluteGaloisGroup F) (c : contT (F := F) p I),
    contFC (F := F) p I (I.quotientMkContinuousMonoidHom h • c)
      = h • contFC (F := F) p I c := by
  intro h c
  show ((contITame (F := F) p I (I.quotientMkContinuousMonoidHom h • c) :
      contInvC (F := F) p I) : contC (F := F) p)
    = h • ((contITame (F := F) p I c : contInvC (F := F) p I) : contC (F := F) p)
  rw [contITame_smul]
  change (FixedPoints.addSubgroup (↥I) (contC (F := F) p)).subtype
      (I.quotientMkContinuousMonoidHom h • contITame (F := F) p I c)
    = h • (FixedPoints.addSubgroup (↥I) (contC (F := F) p)).subtype
        (contITame (F := F) p I c)
  rw [I.fixedPoints_subtype_quotientMk_smul (M := contC (F := F) p)]

/-- ★★★★★ **连续 (F1)**：`δ_T ≫ map φ fA = map φ fC ≫ δ_Γ`（离散侧 `Hyp543`；见文件头）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:prop-residue-map-long-exact quote="follows from an easy compatibility between inflations and boundary maps in long exact sequences"
theorem contF1 (n : ℕ) :
    (contInvSES (F := F) p I).delta n
        ≫ _root_.ContinuousCohomology.map (I.quotientMkContinuousMonoidHom)
            (ofDiscreteModulePair
              (I.quotientMkContinuousMonoidHom :
                AbsoluteGaloisGroup F →* (AbsoluteGaloisGroup F) ⧸ I)
              (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype.toIntLinearMap
              I.fixedPoints_subtype_quotientMk_smul) (n + 1)
      = _root_.ContinuousCohomology.map (I.quotientMkContinuousMonoidHom)
            (ofDiscreteModulePair
              (I.quotientMkContinuousMonoidHom :
                AbsoluteGaloisGroup F →* (AbsoluteGaloisGroup F) ⧸ I)
              (contFC (F := F) p I).toIntLinearMap (contFC_smul (F := F) p I)) n
        ≫ (contCoindSES (F := F) p).delta n :=
  DiscreteShortExact.delta_map (S := contInvSES (F := F) p I) (T := contCoindSES (F := F) p)
    (φ := I.quotientMkContinuousMonoidHom)
    (fA := (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype)
    (fB := (FixedPoints.addSubgroup (↥I) (contB (F := F) p)).subtype)
    (fC := contFC (F := F) p I)
    (hA := I.fixedPoints_subtype_quotientMk_smul)
    (hB := I.fixedPoints_subtype_quotientMk_smul)
    (hC := contFC_smul (F := F) p I)
    (hincl := fun _ => rfl)
    (hproj := fun _ => rfl) n

/-- ★★★ **`contF1` 的左端拆解**：`map φ fA = coeffMap (quot) ≫ infl`。

这是接 `(d)`（GS 6.8.2 的长正合列）所必需的接口：库内
`coeffMap_ofDiscreteModuleQuotient_comp_infl`（`Inflation/Comparison.lean:95`）的 `rw`。 -/
theorem contF1_infl (n : ℕ) :
    (contInvSES (F := F) p I).delta n
        ≫ TauCeti.ContinuousCohomology.coeffMap
            (ofDiscreteModuleQuotient (AbsoluteGaloisGroup F) (ZMod p) I) (n + 1)
        ≫ TauCeti.ContinuousCohomology.infl I
            (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) (n + 1)
      = _root_.ContinuousCohomology.map (I.quotientMkContinuousMonoidHom)
            (ofDiscreteModulePair
              (I.quotientMkContinuousMonoidHom :
                AbsoluteGaloisGroup F →* (AbsoluteGaloisGroup F) ⧸ I)
              (contFC (F := F) p I).toIntLinearMap (contFC_smul (F := F) p I)) n
        ≫ (contCoindSES (F := F) p).delta n := by
  rw [TauCeti.ContCohomology.coeffMap_ofDiscreteModuleQuotient_comp_infl
    (G := AbsoluteGaloisGroup F) (M := ZMod p) (N := I) (n + 1)]
  exact contF1 (F := F) p I n

end L20261018

#print axioms L20261018.contProjInv_smul
#print axioms L20261018.contITame_smul
#print axioms L20261018.contFC_smul
#print axioms L20261018.contF1
#print axioms L20261018.contF1_infl
