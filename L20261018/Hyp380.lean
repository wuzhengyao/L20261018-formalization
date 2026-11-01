import L20261018.Hyp379
import TauCeti.NumberTheory.LocalField.Unramified.Maximal
import TauCeti.NumberTheory.LocalField.Unramified.ZHat

/-!
# R1294（S37 · GS §6.8 战役 **S1（局部域，无条件）**）：`K_nr` 的伽罗瓦性与 `Gal(K_nr/K) ≅ Ẑ`

## 为什么这一轮能把 `Hyp378` 的假设全部拿掉

GS 2017 §6.8.1（label `sec:cohomology-complete-dv`）的定义是：

> let $K_{nr}$ be the maximal unramified extension of $K$, i.e. the composite of all finite
> unramified extensions of $K$ inside $K_{s}$. The valuation $v$ extends uniquely to a discrete
> valuation of $K_{nr}$ with residue field $\kappa_{s}$ … The extension $K_{nr}|K$ is Galois,
> and the Galois group $G:=\operatorname{Gal}(K_{nr}|K)$ is canonically isomorphic to
> $\operatorname{Gal}(\kappa_{s}|\kappa)$.

即 GS 的 `K_nr` 是**并**（并起来自动伽罗瓦），惯性则是 `Gal(K_s/K_nr)`（**定义上就是固定子群，
自动闭**）。`Hyp375`／`Hyp378` 走的是**对偶**路线（`K_nr := fixedField I*`，`I*` 是剩余作用的核），
于是「闭性」成了额外假设 —— 而它在 mathlib 里**无法陈述**（`ResidueField` 无拓扑）。

本轮按 `L48`（照原文证明路线）回到 GS 的定义：TauCeti 已有机检件

* `TauCeti.maximalUnramifiedExtension K Ω : IntermediateField K Ω`（**任意** `Ω`）；
* **`instance isGalois_maximalUnramifiedExtension : IsGalois K (K^ur)`**（无条件，任意 `Ω`）；
* `InfiniteGalois.fixedField_fixingSubgroup`（`[IsGalois k K]`，**不需要闭性假设**）；
* `InfiniteGalois.fixingSubgroup_isClosed`（固定子群**自动闭**）。

⟹ 取 `Ω := SeparableClosure F`（本战役的载体），**S1 三件全部无条件**，
且与 `Hyp378` 的条件版本**并存**（后者用于一般 `A : ValuationSubring (SepCl F)`）。

## 本轮机检

| 声明 | 内容 | 假设 |
|---|---|---|
| `KnrLoc` | ★ GS 的 `K_nr`：`maximalUnramifiedExtension F (SepCl F)` | — |
| `inertiaLoc` | GS 的惯性 `Gal(K_s/K_nr) = (K_nr).fixingSubgroup` | — |
| `isGalois_KnrLoc` | **`IsGalois F K_nr`**（S1a） | **无** |
| `isClosed_inertiaLoc` | `IsClosed I`（Krull 拓扑） | **无** |
| `normal_inertiaLoc` | `I ◁ G` | **无** |
| **`fixedField_inertiaLoc`** | `fixedField I = K_nr`（**S1b**：GS 的「`I = Gal(K_s/K_nr)`」） | **无** |
| **`galoisGroupKnrLocQuotient`** | `G ⧸ I ≃* Gal(K_nr/K)`（S1c） | **无** |
| **`galoisGroupKnrLocEquivZHat`** | `Gal(K_nr/K) ≃* Ẑ`（GS 的 `≅ Gal(κ_s/κ)` 的 `Ẑ` 形式） | **无** |
| `Knr_eq_KnrLoc` | `inertiaAbs A = I ⟹ Knr A = K_nr`（接 `Hyp378` 的一般口径） | 一条等式 |

## 与 `Hyp378` 的关系（诚实口径）

`Hyp378` 的一般 `A` 版本（任意 `ValuationSubring (SepCl F)`）保留：它把「两个惯性定义相等」
显式作为假设 `inertiaAbs A = inertiaLoc`（见 `Knr_eq_KnrLoc`）。
**该等式** = 「`A` 是 `𝒪_F` 的那个延拓」＋「作用在剩余域上平凡 ⟺ 固定 `K^ur`」，
正是 TauCeti `mem_inertiaSubgroup_iff_pow_natCard_pow_eq_self` 的内容（`AlgebraicClosure` 载体）。
本文件不跨这个载体桥（见 `HANDOFF` 的 S2 侦察节）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ### GS 的定义：`K_nr` := 全部分歧扩张之并 -/

/-- ★★★★★ **GS 的 `K_nr`**：`maximalUnramifiedExtension F (SepCl F)`，即全部有限不分歧扩张的并。
（`Hyp375` 的 `Knr A` 是对偶定义 `fixedField I*`；本文件取 GS 的定义。） -/
noncomputable abbrev KnrLoc : IntermediateField F (SeparableClosure F) :=
  TauCeti.maximalUnramifiedExtension F (SeparableClosure F)

/-- GS 的惯性子群：`I := Gal(K_s/K_nr) = (K_nr).fixingSubgroup`。 -/
noncomputable abbrev inertiaLoc : Subgroup (TauCeti.AbsoluteGaloisGroup F) :=
  (KnrLoc F).fixingSubgroup

/-! ### S1a：`K_nr` 在 `K` 上伽罗瓦 -/

/-- **S1a**：`IsGalois F K_nr`（TauCeti 的 `isGalois_maximalUnramifiedExtension` 是实例）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:sec:cohomology-complete-dv quote="The extension $K_{nr}|K$ is Galois"
instance isGalois_KnrLoc : IsGalois F (KnrLoc F) := inferInstance

/-- `K_nr/K` 正规（`IsGalois` 的场）。 -/
instance normal_KnrLoc : Normal F (KnrLoc F) := inferInstance

/-! ### S1b：`I` 闭、正规，且 `fixedField I = K_nr` -/

/-- **`I` 在 Krull 拓扑下闭**（固定子群自动闭）。 -/
theorem isClosed_inertiaLoc :
    IsClosed ((inertiaLoc F : Subgroup (TauCeti.AbsoluteGaloisGroup F)) :
      Set (TauCeti.AbsoluteGaloisGroup F)) :=
  InfiniteGalois.fixingSubgroup_isClosed _

/-- `I ◁ G`。 -/
instance normal_inertiaLoc : (inertiaLoc F).Normal := inferInstance

/-- **S1b**：`fixedField I = K_nr`（即 `Gal(K_s/K_nr) = I` 的另一半；GS 的「`K_nr` 是不分歧部分」）。 -/
theorem fixedField_inertiaLoc :
    IntermediateField.fixedField (inertiaLoc F) = KnrLoc F :=
  InfiniteGalois.fixedField_fixingSubgroup _

/-- `K_nr` 的固定子群就是 `I`（定义层）。 -/
theorem fixingSubgroup_KnrLoc : (KnrLoc F).fixingSubgroup = inertiaLoc F := rfl

/-! ### S1c：`Gal(K_nr/K) ≅ G ⧸ I` 与 `≅ Ẑ` -/

/-- **S1c**：`G ⧸ I ≃* Gal(K_nr/K)`（无限伽罗瓦对应：闭正规子群）。 -/
noncomputable def galoisGroupKnrLocQuotient :
    TauCeti.AbsoluteGaloisGroup F ⧸ inertiaLoc F ≃* Gal(↥(KnrLoc F)/F) := by
  have h : IntermediateField.fixedField (inertiaLoc F) = KnrLoc F := fixedField_inertiaLoc F
  rw [← h]
  exact InfiniteGalois.normalAutEquivQuotient ⟨inertiaLoc F, isClosed_inertiaLoc F⟩

/-- ★★★★★ **GS 6.8.1 的「`G ≅ Gal(κ_s/κ)`」的 `Ẑ` 形式**：`Gal(K_nr/K) ≃* Ẑ`。

（`Gal(κ_s/κ) ≅ Ẑ` 对有限剩余域 `κ` 也成立；本条只做 `K_nr` 一侧，
见 `TauCeti.maximalUnramifiedGaloisGroupEquivZHat`。） -/
noncomputable def galoisGroupKnrLocEquivZHat :
    Gal(↥(KnrLoc F)/F) ≃* TauCeti.zHat :=
  TauCeti.maximalUnramifiedGaloisGroupEquivZHat F (SeparableClosure F)

/-- 合成：`G ⧸ I ≃* Ẑ`。 -/
noncomputable def galoisQuotientInertiaEquivZHat :
    TauCeti.AbsoluteGaloisGroup F ⧸ inertiaLoc F ≃* TauCeti.zHat :=
  (galoisGroupKnrLocQuotient F).trans (galoisGroupKnrLocEquivZHat F)

/-! ### 与 `Hyp378` 的一般 `A` 口径接线 -/

/-- 若「一般 `A` 的惯性像」`inertiaAbs A` 与 GS 口径的 `I` 相等，则两个 `K_nr` 定义一致。 -/
theorem Knr_eq_KnrLoc (A : ValuationSubring (SeparableClosure F))
    (hA : inertiaAbs (K := F) A = inertiaLoc F) : Knr (K := F) A = KnrLoc F := by
  rw [Knr_def, hA, ← fixedField_inertiaLoc]

/-- ★★★★★ **在此等式下，`Hyp378` 的闭性假设被免费满足** ⟹ 一般 `A` 的 S1 也**无条件**。 -/
theorem isClosed_inertiaAbs_of_eq (A : ValuationSubring (SeparableClosure F))
    (hA : inertiaAbs (K := F) A = inertiaLoc F) :
    IsClosed ((inertiaAbs (K := F) A : Subgroup (TauCeti.AbsoluteGaloisGroup F)) :
      Set (TauCeti.AbsoluteGaloisGroup F)) := by
  rw [hA]; exact isClosed_inertiaLoc F

/-- ★★★★★ **一般 `A` 的 S1a 无条件化**：`IsGalois F (Knr A)`。 -/
theorem isGalois_Knr_uncond (A : ValuationSubring (SeparableClosure F))
    (hA : inertiaAbs (K := F) A = inertiaLoc F) : IsGalois F (Knr (K := F) A) := by
  have hN : (inertiaAbs (K := F) A).Normal := by rw [hA]; infer_instance
  exact isGalois_Knr A hN

/-- ★★★★★ **一般 `A` 的 S1b 无条件化**：`(Knr A).fixingSubgroup = inertiaAbs A`。 -/
theorem fixingSubgroup_Knr_uncond (A : ValuationSubring (SeparableClosure F))
    (hA : inertiaAbs (K := F) A = inertiaLoc F) :
    (Knr (K := F) A).fixingSubgroup = inertiaAbs (K := F) A :=
  fixingSubgroup_Knr A (isClosed_inertiaAbs_of_eq F A hA)

/-- ★★★★★ **一般 `A` 的 S1c 无条件化**：`G ⧸ inertiaAbs A ≃* Gal(Knr A/K)`。 -/
noncomputable def galoisGroupKnrQuotient_uncond (A : ValuationSubring (SeparableClosure F))
    (hA : inertiaAbs (K := F) A = inertiaLoc F)
    (hN : (inertiaAbs (K := F) A).Normal) :
    TauCeti.AbsoluteGaloisGroup F ⧸ inertiaAbs (K := F) A ≃* Gal(↥(Knr (K := F) A)/F) :=
  galoisGroupKnrQuotient A (isClosed_inertiaAbs_of_eq F A hA) hN

/-- `hA` 自动给出正规性（供 `galoisGroupKnrQuotient_uncond` 使用）。 -/
theorem normal_inertiaAbs_of_eq (A : ValuationSubring (SeparableClosure F))
    (hA : inertiaAbs (K := F) A = inertiaLoc F) : (inertiaAbs (K := F) A).Normal := by
  rw [hA]; exact normal_inertiaLoc F

end L20261018

#print axioms L20261018.isClosed_inertiaLoc
#print axioms L20261018.fixedField_inertiaLoc
#print axioms L20261018.galoisGroupKnrLocEquivZHat
#print axioms L20261018.isGalois_Knr_uncond
#print axioms L20261018.fixingSubgroup_Knr_uncond
