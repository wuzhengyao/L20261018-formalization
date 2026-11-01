import L20261018.Hyp543

/-!
# S45 R4：★★★★ **`i_* ≫ deltaZeroBar = 0`**（把 (F2) 从 `ModuleCat` 层抬到 `Rep k (G⧸S)` 层）＋ `δ_{Y'}` 单

## 本件做什么

(F1)（`Hyp543.delta_coind_comp_infl`）已给出
`δ_{Y'} ≫ Inf₂ = i_* ≫ Inf_{C,1} ≫ δ_A`。
(d) ＝ `Inf₂ ≫ deltaTwo_minimal = 0` 的收口还差两件：

| # | 件 | 本件 |
|---|---|---|
| ① | **`iTame ≫ deltaZeroBar = 0`** | 把 `Hyp541.coindCompDeltaZeroBar_eq_zero`（`ModuleCat k` 层：`deltaZeroBar` 的底层在 `T` 上为零）**抬到 `Rep k (G⧸S)` 层** |
| ② | **`Mono δ_{Y'}`** | `groupCohomology.mono_δ_of_isZero` ＋ `isZero_quotientToInvariants_coindBot_succ S A.V 0`（`(Coind A)^S` 在 `G⧸S` 上无环） |

## (F2) → (d) 的逻辑链（下一轮只需 `cancel_mono`）

```
δ_{Y'} ≫ (d) = δ_{Y'} ≫ Inf₂ ≫ δ_A⁻¹ ≫ Inf_{C,1}⁻¹ ≫ M
             = (i_* ≫ Inf_{C,1}) ≫ Inf_{C,1}⁻¹ ≫ M        -- (F1)
             = i_* ≫ M = map (id) (iTame ≫ deltaZeroBar) 1 = 0   -- 本件 ①
⟹ (d) = 0                                                    -- 本件 ②
```

## 机检内容

| 声明 | 内容 |
|---|---|
| `cokerSES_X₂` | 载体锁定：`Y'.X₂ = (Rep.coindBot k G A.V).quotientToInvariants S` |
| **`qSES_g_comp_deltaZeroBar`** | ★★★★ `qSES.g ≫ deltaZeroBar = 0` |
| **`iTame_comp_deltaZeroBar`** | ★★★★★ `iTame ≫ deltaZeroBar = 0`（用 `cokernel.π` 是 epi 消去） |
| **`mono_δ_cokerSES`** | ★★★★ `Mono (δ_{Y'} 1 2)`,**零假设** |

## 诚实边界

* 本件**不**组装 `(d)` 本体（那是下一轮 `Hyp545`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- 载体锁定：`Y'` 的中项就是 `(Coind A)^S`。 -/
theorem cokerSES_X₂ :
    (cokerSES A S).X₂ = (Rep.coindBot k G A.V).quotientToInvariants S := (rfl)

/-- ★★★★ **`(F2)` 抬到 `Rep k (G⧸S)` 层**：`qSES.g ≫ deltaZeroBar = 0`。

即「`deltaZeroBar` 在 `T = range(A^S 不动元 ↪ (Coind A)^S 不动元 的像 …)` 上为零」
（`Hyp541.coindCompDeltaZeroBar_eq_zero` 的 `Rep` 层形态）。 -/
theorem qSES_g_comp_deltaZeroBar :
    (qSES A S).g ≫ deltaZeroBar A S (innerConjTrivialIn_one A S) = 0 := by
  rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff]
  have heq : (Rep.Hom.hom ((qSES A S).g ≫ deltaZeroBar A S (innerConjTrivialIn_one A S))).toLinearMap
      = ModuleCat.Hom.hom ((Rep.invariantsFunctor k S).map (dimShiftSES A S).g
          ≫ (groupCohomology.H0Iso (dimShiftSES A S).X₃).inv
          ≫ deltaZero_coindBot A S) := by
    ext x
    rfl
  rw [heq, coindCompDeltaZeroBar_eq_zero (k := k) (G := G) A S]
  simp

/-- ★★★★★ **`i_* ≫ deltaZeroBar = 0`** —— (d) 收口所需的 (F2) 形态。

`π : (Coind A)^S ↠ T` 是满的（`cokernel.π`），而 `qSES.g = π ≫ iTame`，故由
`qSES_g_comp_deltaZeroBar` 与 `cancel_epi` 即得。 -/
theorem iTame_comp_deltaZeroBar :
    iTame A S ≫ deltaZeroBar A S (innerConjTrivialIn_one A S) = 0 := by
  have h1 : cokernel.π (qSES A S).f
      ≫ (iTame A S ≫ deltaZeroBar A S (innerConjTrivialIn_one A S)) = 0 := by
    rw [← Category.assoc, cokernelπ_comp_iTame, qSES_g_comp_deltaZeroBar]
  exact (cancel_epi (cokernel.π (qSES A S).f)).mp
    (h1.trans (comp_zero (f := cokernel.π (qSES A S).f)).symm)

/-- ★★★★ **`δ_{Y'}` 单（零假设）**：`(Coind A)^S` 在 `G⧸S` 上 $H^1$ 为零，故连接映射单。 -/
theorem mono_δ_cokerSES :
    Mono (groupCohomology.δ (cokerSES_shortExact A S) 1 2 rfl) :=
  groupCohomology.mono_δ_of_isZero (cokerSES_shortExact A S) 1
    (TauCeti.groupCohomology.isZero_quotientToInvariants_coindBot_succ S A.V 0)

end L20261018

#print axioms L20261018.cokerSES_X₂
#print axioms L20261018.qSES_g_comp_deltaZeroBar
#print axioms L20261018.iTame_comp_deltaZeroBar
#print axioms L20261018.mono_δ_cokerSES
