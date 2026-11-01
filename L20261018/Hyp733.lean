import Hyp732
import Hyp722

/-!
# S66 R2b：分片 **4c-iv 的战役级收口** —— `contM ∘ ι = 0`

`Hyp732` 给了三条几何件（`projI`／`iota`／`projRestr`）与两条数学件
（`restrict_delta_zero_comp_projCoeff` ＝ `δ⁰∘proj_* = 0`、`h0Bridge_projI` ＝ `H⁰` 比较的系数自然性）。
本件把 `M = contM` 的定义式（`Hyp576.contM_eq`：`h1Bridge(contM x) = δ⁰_{S_I}(h0Bridge x)`）插进去，
得到 4d 需要的**唯一一条**：

```
contM (ι x) = 0        (x : T = Bᴵ/im(Aᴵ))
```

## 记号对齐（`M12` 方向在此已核）

* `contM = h1Bridge⁻¹ ∘ contDeltaZeroBar I ∘ h0Bridge`，而 `contDeltaZeroBar I = (contDimShiftSES p I).delta 0`
  ＝ `((contCoindSES p).restrict I).delta 0`（`restrict` 是库内构造）；
* `ι (mk b) = projI S I b = ⟨S.proj b, ·⟩ = H⁰(S.proj)(b)`；
* 故 `contM(ι (mk b)) = 0` **就是** `δ⁰_{S_I}(H⁰(proj)(b)) = 0` —— `ker δ⁰ = range(H⁰(proj))` 的平凡方向。
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

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [CompactSpace ↥I]
  [IsClosed (I : Set (AbsoluteGaloisGroup F))]

/-! ## 1 `δ⁰` 在 `projRestr` 拼写下的消零（`Hyp732` 拼写的对接版） -/

/-- ★★★ **`δ⁰_{S_I}` 杀死 `coeffMap (S.proj) 0` 的像** —— `projRestr` 拼写。

与 `Hyp732.restrict_delta_zero_comp_projCoeff` 同一件事，只是系数映射走
`projRestr (B →+[↥I] C)` 的打包形态（`h0Bridge_projI` 的输出形状），故两处可**直接对接**。 -/
theorem delta_zero_comp_projRestrCoeff
    (y : ↑(continuousCohomology 0 (ofDiscreteModule ℤ (↥I) (contB (F := F) p))).toModuleCat) :
    (contDimShiftSES (F := F) p I).delta 0
        ((ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap
            (projRestr (contCoindSES (F := F) p) I).toAddMonoidHom.toIntLinearMap
            (fun i m => map_smul (projRestr (contCoindSES (F := F) p) I) i m)) 0) y) = 0 :=
  restrict_delta_zero_comp_projCoeff (S := contCoindSES (F := F) p) I y

/-! ## 2 `contM ∘ projI = 0` -/

/-- ★★★★ **`M` 杀死 `proj` 的像**：`contM (projI b) = 0`。

插入 `contM` 的定义式（`contM_eq`）后，只需 `H⁰` 比较的自然性（`h0Bridge_projI`）
＋ `δ⁰` 消零（`delta_zero_comp_projRestrCoeff`）。 -/
theorem contM_comp_projI (b : FixedPoints.addSubgroup (↥I) (contB (F := F) p)) :
    contM (F := F) p I (projI (contCoindSES (F := F) p) I b) = 0 := by
  refine (explicitH1AddEquivContinuousCohomology (↥I) (ZMod p)).map_eq_zero_iff.mp ?_
  rw [contM_eq]
  rw [h0Bridge_projI (S := contCoindSES (F := F) p) I b]
  exact delta_zero_comp_projRestrCoeff (F := F) p I _

/-! ## 3 4c-iv 的最终形态：`contM ∘ ι = 0` -/

/-- ★★★★★ **`M ∘ ι = 0`**（4c-iv）：`contM` 在 `ι : T → Cᴵ` 的像上恒为 0。

这是 4d 追图里除 `Hyp731`（`δ¹_{SES1}` 可逆）之外**唯一**的输入。 -/
theorem contM_comp_iota (x : TBI (contCoindSES (F := F) p) I) :
    contM (F := F) p I (iota (contCoindSES (F := F) p) I x) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H b =>
    show contM (F := F) p I (iota (contCoindSES (F := F) p) I
      (QuotientAddGroup.mk' (inclI (contCoindSES (F := F) p) I).range b)) = 0
    rw [iota_mk]
    exact contM_comp_projI (F := F) p I b

end L20261018

#print axioms L20261018.delta_zero_comp_projRestrCoeff
#print axioms L20261018.contM_comp_projI
#print axioms L20261018.contM_comp_iota
