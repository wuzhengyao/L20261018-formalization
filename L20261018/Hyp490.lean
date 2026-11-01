import L20261018.Hyp489

/-!
# S41 R1（收口）：**义务的「一条 `d` ＋ 三条性质」正范式** —— 与 `∃d` 形式**双向等价**

## 为什么需要本件

`Hyp488.knrResidueReduced` 把 `Hyp479.KnrResidueObligation`（`∃ d, …`）**显式化**到
S40 造的那条具体 `d`（`dPartialLin`）上。但 `Hyp489` 机检了那条 `d` 的载体是错的
（`r_v ∘ (μ_p ↪ K_nr^×)_* = 0`，见该件文件头），故 `KnrResidueReduced` **对这条 `d` 为假**。
⇒ `Hyp488` 的归约**不能**当成朝目标的进展。

本件把归约**脱离具体 `d`**，给出**与 `∃d` 形式双向等价**的正范式：

```lean
KnrResidueObligation F p v π hpF  ↔
  ∃ d : GaloBase.H2 F p →ₗ[ZMod p] GaloBase.V F p,
    (∀ x, v̄ (d x) = 0) ∧                                   -- (A) 落在 ker v̄ 内
    (∀ y z : VKG, d (y ⌣ z) = 0) ∧                          -- (B) ③b
    (∀ y : VKG, d (y ⌣ (π)) = y)                            -- (C) ③c
```

**两向都机检**（`knrResidueObligation_iff_exists_three`）：正向取 `d := VKG.subtype ∘ d'`、
`(A)` 由子类型成员给出；反向用 `LinearMap.codRestrict`。⟹ 这是**同一命题的另一种写法**
（`rfl` 级的方向 ＋ 一次 `codRestrict`），不损失任何信息。

## 用途（对 S42 起的路线）

1. **剩下的事被精确地表述为：造一条 `d` 使 (A)(B)(C) 成立。** 不再有任何「存在性」的模糊空间；
2. `Hyp488` 的 `KnrResidueReduced` 只是「取 `d := dPartialLin`」的特化
   （`knrResidueObligation_of_reduced_regression`：本件给出**第二条证明**，作为回归对照 L43）；
3. 新 `d`（GS §6.8 的 `∂_v`，见 `S41-STATUS.md` §4）落到同一个 `(A)(B)(C)` 槽位上即可。

## 机检件

| 声明 | 内容 |
|---|---|
| **`knrResidueObligation_iff_exists_three`** | ★★★★★ **`∃d` 形式 ⟺ 「一条 `d` ＋ (A)(B)(C)」**（双向） |
| `knrResidueObligation_of_three` | 单向（反向方向的可直接用形式） |
| `knrResidueObligation_of_reduced_regression` | `Hyp488.knrResidueObligation_of_reduced` 的**第二条证明**（L43 回归对照） |
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

variable {F : Type} [Field F] (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
  (v : Fˣ →* Multiplicative ℤ) (π : Fˣ)

/-- ★★★★★ **单向（可直接用形式）**：一条满足 (A)(B)(C) 的 `d` ⟹ 义务。

`(A)` 是「`d` 落在 `ker v̄ = VKG` 内」；`(B)`／`(C)` 是论文 `:1050` 的两条杯积公式
（`(C)` 写在 `GaloBase.V` 里，进入子类型由 `Subtype.ext` 完成）。 -/
-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem knrResidueObligation_of_three (hpF : IsUnit (p : F))
    (d : GaloBase.H2 F p →ₗ[ZMod p] GaloBase.V F p)
    (hA : ∀ x : GaloBase.H2 F p, valLinOf (F := F) (p := p) v hpF (d x) = 0)
    (hB : ∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (hC : ∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = (y : GaloBase.V F p)) :
    KnrResidueObligation F p v π hpF := by
  refine ⟨d.codRestrict (LinearMap.ker (valLinOf (F := F) (p := p) v hpF)) hA, ?_, ?_⟩
  · intro y z
    exact Subtype.ext (hB y z)
  · intro y
    exact Subtype.ext (hC y)

/-- ★★★★★ **双向等价**：义务的 `∃d` 形式 ⟺「一条 `d` 满足 (A)(B)(C)」。

正向：取 `d := (VKG ↪ V) ∘ d'`，`(A)` 由子类型成员 `d' x` 的第二分量给出。
反向：`knrResidueObligation_of_three`。 -/
theorem knrResidueObligation_iff_exists_three (hpF : IsUnit (p : F)) :
    KnrResidueObligation F p v π hpF ↔
      ∃ d : GaloBase.H2 F p →ₗ[ZMod p] GaloBase.V F p,
        (∀ x : GaloBase.H2 F p, valLinOf (F := F) (p := p) v hpF (d x) = 0) ∧
        (∀ y z : VKG F p v hpF,
          d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0) ∧
        (∀ y : VKG F p v hpF,
          d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
            (KummerBridge.kummerClass F p hpF π)) = (y : GaloBase.V F p)) := by
  constructor
  · rintro ⟨d', hB, hC⟩
    refine ⟨(LinearMap.ker (valLinOf (F := F) (p := p) v hpF)).subtype.comp d', ?_, ?_, ?_⟩
    · intro x
      exact (d' x).2
    · intro y z
      exact congrArg Subtype.val (hB y z)
    · intro y
      exact congrArg Subtype.val (hC y)
  · rintro ⟨d, hA, hB, hC⟩
    exact knrResidueObligation_of_three (F := F) p v π hpF d hA hB hC

/-- **回归对照（L43）**：`Hyp488.knrResidueObligation_of_reduced` 的**第二条证明** ——
即 `KnrResidueReduced`（关于 `dPartialLin` 的三条）经 `knrResidueObligation_of_three` 的实例化。
两条证明的陈述类型**逐字相同**，故任何一边改动都会使另一边失配（类型锁定）。 -/
theorem knrResidueObligation_of_reduced_regression (hpF : IsUnit (p : F)) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (h : KnrResidueReduced (F := F) p v π hpF hζ) :
    KnrResidueObligation F p v π hpF :=
  knrResidueObligation_of_three (F := F) p v π hpF
    (dPartialLin (F := F) p hpF hζ) h.1 h.2.1 h.2.2

end L20261018

#print axioms L20261018.knrResidueObligation_of_three
#print axioms L20261018.knrResidueObligation_iff_exists_three
#print axioms L20261018.knrResidueObligation_of_reduced_regression
