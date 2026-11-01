import L20261018.Ch2.Hensel.UnitsCupVanish.Step035_kummer_cocycle_properties

/-!
# S52 R25：**N3 第一块** —— `𝒪[F] → 𝒪_W` 的环同态与剩余域映射 `κ → κ̄`

## 0 目标

N3（`Γ_F/I ≅ Gal(κ̄/κ)`）的第一件事是**把 `κ` 看成 `κ̄` 的子域**：

```
hO : 𝒪_W = 𝒪bar   ⟹   𝒪[F] ⊆ 𝒪_W   ⟹   ↥𝒪[F] →+* ↥𝒪_W
   ⟹   ResidueField ↥𝒪[F] →+* ResidueField ↥𝒪_W    （即 κ → κ̄）
```

## 1 数学（两行）

* `x ∈ 𝒪[F]` ⟹ `algebraMap x ∈ integralClosure ↥𝒪[F] F̄`（`isIntegral_algebraMap`）⟹ 由 `hO` **在 `𝒪_W` 里**；
* 于是 `x ↦ ⟨algebraMap x, _⟩` 是环同态 `↥𝒪[F] →+* ↥𝒪_W`；过 `ResidueField.map` 即得 `κ →+* κ̄`。

## 2 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| **`algebraMap_mem_valuationSubring`** | ★★★★ `x : ↥𝒪[F]` ⟹ `algebraMap x ∈ 𝒪_W` |
| **`toValuationSubring`** | ★★★★ 环同态 `↥𝒪[F] →+* ↥𝒪_W` |
| `toValuationSubring_coe` | 与 `algebraMap` 的相容（`rfl` 级） |
| **`residueFieldMap`** | ★★★★★ **剩余域映射 `κ →+* κ̄`**（`ResidueField.map`）；⚠ 名字避开战役已有的 `residueMap`（`Hyp386`，别的对象） |
| **`residueFieldMap_residue`** | 接口引理：`residueFieldMap (residue x) = residue (toValuationSubring x)` |

## 3 诚实边界（★ 一条**新登记的假设**）

* **`hLoc : IsLocalHom (toValuationSubring …)` 仍是假设**。它是「`v` 与 `W` 在极大理想层相容」的载体化：
  要证它需要 `ValCompat (F := F) v`（把 `v x > 0` 与 `W (algebraMap x) < 1` 对上），**本轮未做**。
  ⟹ 本件**不声称**已得 `κ ↪ κ̄`（单射性还需该相容性 ＋ `ResidueField.map` 的单射判据）。
* **未做**：`residueFieldMap` 的单射性／`κ̄` 在 `κ` 上可分闭／`κ̄^I = κ`（N3 的后半）。
* 本件**不动** `(CI)`；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section ResidueEmbedding

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))

include hO in
/-- ★★★★ **`x ∈ 𝒪[F]` ⟹ `algebraMap x ∈ 𝒪_W`**（`hO` 的第一次使用）。 -/
theorem algebraMap_mem_valuationSubring (x : ↥𝒪[F]) :
    (algebraMap ↥𝒪[F] (SeparableClosure F)) x ∈ W.valuationSubring :=
  (hO _).mpr (algebraMap_mem_integralClosure x)

include hO in
/-- ★★★★ **环同态 `↥𝒪[F] →+* ↥𝒪_W`**。 -/
noncomputable def toValuationSubring : ↥𝒪[F] →+* ↥W.valuationSubring where
  toFun x := ⟨(algebraMap ↥𝒪[F] (SeparableClosure F)) x, algebraMap_mem_valuationSubring W hO x⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

include hO in
@[simp] theorem toValuationSubring_coe (x : ↥𝒪[F]) :
    ((toValuationSubring W hO x : ↥W.valuationSubring) : SeparableClosure F)
      = (algebraMap ↥𝒪[F] (SeparableClosure F)) x := rfl

end ResidueEmbedding

section ResidueMap

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hLoc : IsLocalHom (toValuationSubring W hO))

include hO hLoc in
/-- ★★★★★ **剩余域映射 `κ →+* κ̄`**：`ResidueField ↥𝒪[F] →+* ResidueField ↥𝒪_W`。

⚠ 需要 `hLoc : IsLocalHom (toValuationSubring W hO)`（＝ `v` 与 `W` 在极大理想层相容，
应由 `ValCompat` 供给；本轮作为假设）。 -/
noncomputable def residueFieldMap :
    IsLocalRing.ResidueField ↥𝒪[F] →+* IsLocalRing.ResidueField ↥W.valuationSubring :=
  IsLocalRing.ResidueField.map (toValuationSubring W hO)

include hO hLoc in
/-- **接口引理**：`residueMap` 在 `residue x` 上的取值是 `residue (toValuationSubring x)`。 -/
theorem residueFieldMap_residue (x : ↥𝒪[F]) :
    residueFieldMap W hO hLoc (IsLocalRing.residue ↥𝒪[F] x)
      = IsLocalRing.residue ↥W.valuationSubring (toValuationSubring W hO x) :=
  IsLocalRing.ResidueField.map_residue _ _

end ResidueMap

end L20261018

#print axioms L20261018.algebraMap_mem_valuationSubring
#print axioms L20261018.toValuationSubring
#print axioms L20261018.residueFieldMap
#print axioms L20261018.residueFieldMap_residue
