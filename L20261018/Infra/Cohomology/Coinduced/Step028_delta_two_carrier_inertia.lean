import L20261018.Infra.Cohomology.Coinduced.Step027_continuous_smul_criterion
import L20261018.Infra.Cohomology.Coinduced.Step011_hc_inertia_discharged

/-!
# S67 R2：**C4 战役级收口** —— `deltaTwoCarrierInertia ∘ Inf₂ = 0`

`Hyp741.deltaTwoShift_comp_infl_eq_zero`（抽象的 `∂² ∘ Inf₂ = 0`，6 步链）在战役载体上的实例化：

```
S := contCoindSES p,  I := inertiaLoc F,  A := ZMod p,  B := contB,  C := contC,
N' := contMHom,      hzero := contM_comp_iota
```

## 输入表（全部机检件）

| 需要 | 件 |
|---|---|
| `hB1`／`hB2`（`H^1`／`H^2(Γ⧸I, Bᴵ) = 0`） | `Hyp728.subsingleton_H_quot_coindBot_invariants`（`i = 1`／`2`） |
| `hA1`／`hA2`（`H^1`／`H^2(Γ, B) = 0`） | `TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int` `0`／`1` |
| `hC`（`H¹(I, C) = 0`） | `Hyp724.inertiaLoc_subsingleton_H1_contC` |
| `N'`／`hN'` | `Hyp722.contMHom`／`continuous_of_discreteTopology` |
| `hzero`（`contM ∘ ι = 0`） | `Hyp733.contM_comp_iota` |

## 三条**技术实例**假设（非数学假设；如实登记）

1. `[ContinuousSMul (Γ⧸I) (H¹(I,μ_p))]` —— 战役既有口径（`Hyp722`／`Hyp723`／`Hyp724` 都带），
   由 `H¹(I,μ_p)` 的**有限性**（`Hyp520`／`Hyp521`）兑现；
2. `[DiscreteTopology (H¹(I,μ_p))]` —— 同一有限性的拓扑面（`Hyp741` 的 `P` 槽要求）；
3. `[ContinuousSMul (Γ⧸I) (TBI (contCoindSES p) (inertiaLoc F))]` —— `TBI` 拓扑 ＝ `⊥`，
   库内无商作用连续性实例；**证法已定**（`Hyp742.continuous_smul_of_forall_continuous` ＋ 沿 `mk'` 下降），
   两个实例歧义坑见 `S67-4D-NOTES.md` §3.2。
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

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime]

/-- ★★★★★ **C4 战役级收口**：`∂² (Inf₂ y) = 0`（`inertiaLoc` 载体，`∂² = deltaTwoCarrierInertia`）。

这就是 GS 6.8.1 正合性中 `ker ∂² ⊇ im Inf₂` 的那一半（论文第 4 章 `hd_infl` 的代数内核）。 -/
theorem deltaTwoCarrierInertia_comp_infl_eq_zero
    (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    (y : ↑(continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))).toModuleCat) :
    deltaTwoCarrierInertia (F := F) p q hcop
      ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
        (TauCeti.ofDiscreteModulePair
          (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F) :
            AbsoluteGaloisGroup F →* AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype.toIntLinearMap
          (inertiaLoc F).fixedPoints_subtype_quotientMk_smul) 2) y) = 0 := by
  haveI hcl : IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
  have hB1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ
      (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F))
        (contB (F := F) p)))).toModuleCat :=
    subsingleton_H_quot_coindBot_invariants (G := AbsoluteGaloisGroup F) (A := ZMod p)
      (I := inertiaLoc F) 1 (le_refl 1)
  have hB2 : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ
      (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F))
        (contB (F := F) p)))).toModuleCat :=
    subsingleton_H_quot_coindBot_invariants (G := AbsoluteGaloisGroup F) (A := ZMod p)
      (I := inertiaLoc F) 2 (by omega)
  have hA1 : Subsingleton ↑(continuousCohomology 1
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contB (F := F) p))).toModuleCat :=
    subsingleton_continuousCohomology_discreteCoind_bot_int (AbsoluteGaloisGroup F) (ZMod p) 0
  have hA2 : Subsingleton ↑(continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contB (F := F) p))).toModuleCat :=
    subsingleton_continuousCohomology_discreteCoind_bot_int (AbsoluteGaloisGroup F) (ZMod p) 1
  have hC : Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (contC (F := F) p))) :=
    inertiaLoc_subsingleton_H1_contC (F := F) p q hcop
  exact deltaTwoShift_comp_infl_eq_zero (S := contCoindSES (F := F) p) (I := inertiaLoc F)
    hB1 hB2 hA1 hA2 hC (N' := contMHom (F := F) p (inertiaLoc F))
    continuous_of_discreteTopology
    (fun x => contM_comp_iota (F := F) p (inertiaLoc F) x) y

end L20261018

#print axioms L20261018.deltaTwoCarrierInertia_comp_infl_eq_zero
