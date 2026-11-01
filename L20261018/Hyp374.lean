import Hyp373

/-!
# R1287（S36 · GS §6.8 战役 #1）：惯性子群的**正合序列第一段**

`PLAN-GS68.md` §5 第 1 件：「一般 Hensel DVR 的 `K_nr` ＋ `Gal(K_nr/K) ≅ G_κ`」。
本轮侦察结论（写入 `HANDOFF`）：mathlib 的 `Mathlib/RingTheory/Valuation/RamificationGroup.lean`
**只有两个定义**（`decompositionSubgroup`、`inertiaSubgroup`），**没有**任何关于它们的引理
（正规性、商、与剩余域自同构的关系一概没有）。故正合列

```
1 → I → D → Gal(κ_L/κ)
```

必须自建。本文件给出最基础的一段（对 `L := SeparableClosure K`、任意 `A : ValuationSubring L`）：

| 声明 | 内容 |
|---|---|
| `inertiaSubgroup_normal` | `I ◁ D`（它是到剩余域自同构的核） |
| **`decompQuotToResidue`** | ★★★★ `D ⧸ I →* (κ_A ≃+* κ_A)`（`Gal(K_nr/K)` 的雏形） |
| **`decompQuotToResidue_injective`** | ★★★★★ 该映射**单射**（核恰为 `I` 的像） |

下一步（下一轮）：`κ_A = κ_s` 时该映射**满射**（= Hensel 提升剩余自同构），
即可得 `Gal(K_nr/K) ≅ Gal(κ_s/κ)`。
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

variable {K : Type*} [Field K]

/-- `A` 的惯性子群在分解子群中正规（`inertiaSubgroup` 是到 `Aut(κ_A)` 的同态的核）。 -/
instance inertiaSubgroup_normal (A : ValuationSubring (SeparableClosure K)) :
    (A.inertiaSubgroup K).Normal :=
  MonoidHom.normal_ker _

/-- 分解子群在剩余域上的作用（`D →* Aut(κ_A)`）。 -/
noncomputable def decompToResidue (A : ValuationSubring (SeparableClosure K)) :
    A.decompositionSubgroup K →* RingAut (IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

/-- ★★★★★ **`D ⧸ I ≃* range(D →* Aut(κ_A))`** —— 「`Gal(K_nr/K)` ↔ 剩余域伽罗瓦群」的第一半
（对 `A : ValuationSubring (SeparableClosure K)` 完全一般；`I` 的定义就是该同态的核）。 -/
noncomputable def decompQuotEquivRange (A : ValuationSubring (SeparableClosure K)) :
    (A.decompositionSubgroup K) ⧸ (A.inertiaSubgroup K) ≃* (decompToResidue (K := K) A).range :=
  QuotientGroup.quotientKerEquivRange (decompToResidue (K := K) A)

/-- ★★★★★ **单射性**：`D ⧸ I` 嵌入 `Aut(κ_A)`。 -/
theorem decompQuotToResidue_injective (A : ValuationSubring (SeparableClosure K)) :
    Function.Injective (fun x : (A.decompositionSubgroup K) ⧸ (A.inertiaSubgroup K) =>
      ((decompQuotEquivRange (K := K) A) x : RingAut (IsLocalRing.ResidueField A))) :=
  fun _ _ h => (decompQuotEquivRange (K := K) A).injective (Subtype.ext h)

end L20261018

#print axioms L20261018.inertiaSubgroup_normal
#print axioms L20261018.decompQuotToResidue_injective
