import L20261018.Infra.Cohomology.Coinduced.Step009_c2_f_interface

/-!
# S64 R12：★★★★★ **战役载体上的 `∂²` 装配完成**

```
∂² : H²(Γ, μ_p) → H¹(Γ⧸I, H¹(I, μ_p))
  = Hyp719.deltaTwoShift（前两因子）≫ Hyp722.contM_coeffMap（第三因子）
```

* **前两因子**（`deltaTwoShift`）：`H²(Γ,μ_p) ≃+ H1 (Γ⧸I) (Cᴵ)`
  —— (6.15) 维数平移（`Hyp492` ＋ 余诱导两度零调）＋ 膨胀同构（`Hyp717`，输入 `H¹(I,C)=0`）；
* **第三因子**（`contM_coeffMap`）：`H1 (Γ⧸I)(Cᴵ) →+ H1 (Γ⧸I)(H¹(I,μ_p))`（`Hyp722`）。

**两条显式假设**（都可兑现，见下）：
* `hC : Subsingleton (H¹(I, C))` —— C 步；由 `Hyp716.subsingleton_H1_quot_subgroup_of_isClosed`
  把假设卸到 `H²(I,μ_p) = 0`，而后者由 **`Hyp517` 的无条件 `cd_ℓ(I) ≤ 1`** 给；
* `[ContinuousSMul (Γ⧸I) (H1 ↥I (ZMod p))]` —— 靶侧商作用连续；由 `Hyp520`／`Hyp521`（`H¹(I,μ_p) ≅ ℤ/p` 有限）兑现。
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

/-- ★★★★★ **战役载体上的 `∂²`**：`H²(Γ, μ_p) →+ H¹(Γ⧸I, H¹(I, μ_p))`。

即 GS 6.8.1 的 `∂²`（`i = 2`）：维数平移 ∘ 膨胀同构 ∘ 系数映射 `M = δ⁰`。 -/
noncomputable def deltaTwoCarrier
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ I) (H1 ↥I (ZMod p))]
    (hC : Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥I (contC (F := F) p)))) :
    continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) →+
      H1 (AbsoluteGaloisGroup F ⧸ I) (H1 ↥I (ZMod p)) :=
  (contM_coeffMap (F := F) p I).comp
    (deltaTwoShift (H := I) (A := ZMod p) (B := contB (F := F) p) (C := contC (F := F) p)
      (contCoindSES (F := F) p)
      (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
        (AbsoluteGaloisGroup F) (ZMod p) 0)
      (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
        (AbsoluteGaloisGroup F) (ZMod p) 1)
      hC).toAddMonoidHom

end L20261018

#print axioms L20261018.deltaTwoCarrier
