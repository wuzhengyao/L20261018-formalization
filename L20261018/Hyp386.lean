import L20261018.Hyp385
import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Rational

/-!
# R1300（S37 第 8 轮）：**GS 6.8.1 的 `r_v^i` —— 给定系数正合列时的机检装配**

## 这一轮在补什么

GS 2017 §6.8.1（label `sec:cohomology-complete-dv`）的剩余映射是

```
r_v^i : H^i(G, K_nr^×) → H^{i-1}(G, Q/Z),      0 → H^i(G,U_nr) → H^i(G,K_nr^×) →r_v^i→ H^{i-1}(G,Q/Z) → 0
```

它由两个**已被本战役机检的**部件与一个**系数正合列**拼成：

| 部件 | 状态 |
|---|---|
| `H^i(G,ℤ) ≅ H^{i-1}(G,Q/Z)`（S3） | ✓ `Hyp379.ratOverZDimShift` |
| 长正合列的**核/像**（蛇引理的 exactness） | ✓ TauCeti `DiscreteShortExact.longExact_exact₂` |
| `0 → U_nr → K_nr^× → ℤ → 0`（GS (6.1)） | ✗ **缺**（`GS68-LEDGER.md` §E 的 G2：`K_nr` 的赋值对象层） |

⟹ 本轮把前两件**装成 `r_v^i`**，并把第三件作**唯一参数** `S : DiscreteShortExact G U M (ULift ℤ)`
传下去。这样 GS 6.8.1 的剩余映射在**结构层面**已机检：
**只要**给出系数正合列（G2），**就有** `r_v^{n+2} : H^{n+2}(M) → H^{n+1}(Q/Z)` 且

```
im(H^{n+2}(U) → H^{n+2}(M)) = ker (r_v^{n+2})          -- 「核 = 不分歧部分」
```

## 本轮机检

| 声明 | 内容 |
|---|---|
| **`residueMap`** | ★★★★★ `r_v^{n+2} := (S3 的维数平移) ∘ H^{n+2}(v)` |
| **`residueMap_exact`** | ★★★★★ `Exact (H^{n+2}(U) → H^{n+2}(M)) (r_v^{n+2})` |
| **`residueMap_comp_eq_zero`** | ★★★★ `r_v^{n+2} ∘ (H^{n+2}(U) → H^{n+2}(M)) = 0` |

## 口径（诚实）

* 这是**条件**装配：`S` 是假设（＝ GS (6.1)，本仓无对象，见 ledger §E 的 G2）。
* 它**不**声称 `ker r_v = H^i(G,κ_s^×)` 的**识别**（那需要 S2 的系数比较 `B1`）。
  它只机检 `ker r_v = im(H^i(U) → H^i(M))` —— 即 GS 那句 "As regards the kernel of the residue map"
  之前的**结构**部分。
* 度数用 GS 的 `i = n + 2` 形式（`H^i(ℤ)` 与 `H^{i-1}(Q/Z)` 之间的平移在库里是 `n+1 ↦ n+2`）。
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

variable {F : Type} [Field F]

variable {U M : Type}
  [AddCommGroup U] [TopologicalSpace U] [DiscreteTopology U]
  [DistribMulAction (TauCeti.AbsoluteGaloisGroup F) U]
  [SMulCommClass (TauCeti.AbsoluteGaloisGroup F) ℤ U] [ContinuousSMul ℤ U]
  [ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) U]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction (TauCeti.AbsoluteGaloisGroup F) M]
  [SMulCommClass (TauCeti.AbsoluteGaloisGroup F) ℤ M] [ContinuousSMul ℤ M]
  [ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) M]

-- GS (6.1) 的系数正合列 `0 → U → M → ℤ → 0`（`U = U_nr`、`M = K_nr^×` 时即原文）
variable (S : DiscreteShortExact (TauCeti.AbsoluteGaloisGroup F) U M (ULift.{0} ℤ))

/-- 维数平移那一步（`H^{n+2}(ℤ) → H^{n+1}(Q/Z)`），取连续线性等价以便直接得到单射性。 -/
noncomputable def dimShiftEquiv (n : ℕ) :
    continuousCohomology (n + 1 + 1)
        (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ)) ≃L[ℤ]
      continuousCohomology (n + 1)
        (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F) QoverZdisc) :=
  (ratOverZDimShift (F := F) n).symm.toContinuousLinearEquiv

theorem dimShiftEquiv_injective (n : ℕ) : Function.Injective (dimShiftEquiv (F := F) n) :=
  (dimShiftEquiv (F := F) n).injective

/-- ★★★★★ **GS 6.8.1 的剩余映射** `r_v^{n+2} : H^{n+2}(G,M) → H^{n+1}(G,Q/Z)`：
由「`H^{n+2}(G,v)`」与「S3 的维数平移 `H^{n+2}(G,ℤ) ≅ H^{n+1}(G,Q/Z)`」复合而成。 -/
noncomputable def residueMap (n : ℕ) :
    continuousCohomology (n + 2) (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F) M) →
      continuousCohomology (n + 1)
        (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F) QoverZdisc) :=
  fun x => dimShiftEquiv (F := F) n
    (⇑(CategoryTheory.ConcreteCategory.hom
      (ContinuousCohomology.coeffMap
        (TauCeti.ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) (n + 2))) x)

/-- ★★★★★ **`r_v^{n+2}` 的核 = 不分歧部分**：`im(H^{n+2}(U) → H^{n+2}(M)) = ker (r_v^{n+2})`。

即 GS 6.8.1 在「核的识别」之前的那句结构陈述。来源：TauCeti 的长正合列 `longExact_exact₂`
（`U → M → ℤ` 的正合性）＋ 维数平移是同构。 -/
theorem residueMap_exact (n : ℕ) :
    Function.Exact
      (fun x => ⇑(CategoryTheory.ConcreteCategory.hom
        (ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 2))) x)
      (residueMap (F := F) S n) := by
  have h₂ := DiscreteShortExact.longExact_exact₂ S (n + 2)
  rw [Function.Exact] at h₂
  intro y
  have key : residueMap (F := F) S n y = 0 ↔
      ⇑(CategoryTheory.ConcreteCategory.hom
        (ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap S.proj.toIntLinearMap S.proj_equivariant) (n + 2))) y = 0 := by
    constructor
    · intro h
      refine dimShiftEquiv_injective (F := F) n ?_
      simp only [residueMap] at h ⊢
      rw [h, map_zero]
    · intro h
      simp only [residueMap, h, map_zero]
  exact key.trans (h₂ y)

/-- ★★★★ **`r_v^{n+2}` 在 `H^{n+2}(U)` 的像上为零**（`ker = im` 的直接推论）。 -/
theorem residueMap_comp_eq_zero (n : ℕ) (x : continuousCohomology (n + 2)
      (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F) U)) :
    residueMap (F := F) S n
      (⇑(CategoryTheory.ConcreteCategory.hom
        (ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap S.incl.toIntLinearMap S.incl_equivariant) (n + 2))) x) = 0 := by
  have h := residueMap_exact (F := F) S n
  rw [Function.Exact] at h
  exact (h _).mpr ⟨x, rfl⟩

end L20261018

#print axioms L20261018.dimShiftEquiv_injective
#print axioms L20261018.residueMap_exact
#print axioms L20261018.residueMap_comp_eq_zero
