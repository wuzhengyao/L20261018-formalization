import L20261018.Hyp511
import TauCeti.NumberTheory.LocalField.Tame.Quotient

/-!
# S42 R15（S3 的**模型层**）：驯模 `∏_{ℓ≠p}ℤ_ℓ` 由一元拓扑生成

## 本件在（★）的哪一格

R12–R13 把（★）化为：`I_K`（惯性群）的 ℓ-Sylow（ℓ ≠ char κ）≅ `ℤ_ℓ`。
（R13 的 `Hyp511` 已把战役载体 `inertiaLoc` 与 TauCeti 的 `inertiaSubgroup` 对齐。）
本件把 **S3 的「procyclic」那一半**在**模型层**钉死：

```
TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top (K) :
  ∃ τ, (Subgroup.zpowers (inertiaTameCharacter K τ)).topologicalClosure = ⊤
```

即 **`PrimeToPTateModule p (AlgClosure K)`（≅ `∏_{ℓ≠p}ℤ_ℓ`，`p = ringChar κ`）由一元拓扑生成**。
本件把它改写成**下游要的形态**（`closure {a}` 而非 `zpowers`），供 Sylow 商引理直接消费。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`exists_generator_primeToPTateModule`** | ★★★★★ **模型群 procyclic**：`∃ a, (closure {a}).topologicalClosure = ⊤` |
（下一轮补：模型的**每个闭子群 procyclic** —— 需「循环群的闭子群循环」引理，件未定位）|

## 诚实边界（S3 剩下的部分）

* 本件给的是**模型层的 procyclic 性**；**尚未**给「模型的 ℓ-Sylow ≅ `ℤ_ℓ`」——
  后者需要 limit 计算：`PrimeToPTateModule p E = lim←_{m, (m,p)=1} μ_m`，其 ℓ-部分 ≅ `ℤ_ℓ`（无限）。
* 也**尚未**把 `I_K` 的 ℓ-Sylow 化到 `tameInertia`（S2）。
* **本轮未完成项（登记）**：`循环群 ⟹ 闭子群循环`——TauCeti 有 `Profinite/Procyclic.lean`（闭 procyclic 子群理论），
  须下一轮 `#check` 定位（规则 27 ⑤：不盲试）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- `p := ringChar κ`（TauCeti 的驯模参数）。 -/
noncomputable abbrev residueChar : ℕ :=
  ringChar (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)

/-- ★★★★★ **驯模 procyclic**：`PrimeToPTateModule p (AlgebraicClosure K)` 由一个元素拓扑生成
（TauCeti 的 `exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top` ＋
`Subgroup.zpowers_eq_closure`）。 -/
-- @source file=scratch/lean-l20261018/serre-p67-prop7-cors.txt locator=line:8 quote="The group G_0/G_1 is cyclic, and is mapped isomorphically by theta_0 onto a subgroup of the group of roots of unity contained in L. Its order is prime to the characteristic of the residue field L."
theorem exists_generator_primeToPTateModule :
    ∃ a : PrimeToPTateModule (residueChar K) (AlgebraicClosure K),
      (Subgroup.closure ({a} : Set (PrimeToPTateModule (residueChar K) (AlgebraicClosure K)))).topologicalClosure
        = ⊤ := by
  obtain ⟨τ, hτ⟩ := exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K
  refine ⟨inertiaTameCharacter K τ, ?_⟩
  rw [Subgroup.zpowers_eq_closure] at hτ
  exact hτ

end L20261018

#print axioms L20261018.exists_generator_primeToPTateModule
