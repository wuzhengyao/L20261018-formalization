import L20261018.Infra.Cohomology.Coinduced.Step034_delta_two_map_phi_zero
import L20261018.Infra.Cohomology.Coinduced.Step029_second_carrier_square
import L20261018.Ch2.Hensel.Inertia.Step033_unramified_kummer_hyp
import L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level

/-!
# S69 R2：**A-2 的代数内核** —— `∂² (cup y z) = 0`（`y z ∈ VKG`）

`hd_infl` 的数学内容：`d (cup y z) = 0`（`y z ∈ ker v̄`）。分解：

```
y z ∈ VKG  ⟹  cup y z ∈ residueSpan            （Hyp161.cup_mem_residueSpan）
           ⟹  cup y z ∈ range infl₂            （Hyp744 ＋ Hyp749.unramifiedKummer）
           ⟹  cup y z = infl₂ w
           ⟹  ∂² (infl₂ w) = 0                 （Hyp750.infl2Res_eQ2 ＋ Hyp755 Delta）
```

## `∂²` 的载体代号（本件新定义 `deltaTwoGaloBase'`）

`Hyp725.deltaTwoGaloBase` 用 `ofDiscreteModuleRestrictScalarsIntIso.symm.hom`
（里面有一个 `eqToHom` 载体 cast）；本件的 `deltaTwoGaloBase'` 改用**元素级**的
`restrictScalarsIntEquiv.symm`，与其**只差一个 cast**。好处：`h2ToGaloBase` 的定义也用
`restrictScalarsIntEquiv`，故 `∂² (h2ToGaloBase u) = ∂²_ℤ (e₂ u)` 是纯 `AddEquiv` 推理。

## 交付

| 声明 | 内容 |
|---|---|
| **`deltaTwoGaloBase'`** | `∂²` 在 `GaloBase.H2 F p` 上（元素级桥版本） |
| `deltaTwoGaloBase'_h2ToGaloBase` | `∂² (h2ToGaloBase u) = ∂²_ℤ (e₂ u)` |
| **`deltaTwoGaloBase'_infl2Res_eq_zero`** | `∂² (infl₂ w) = 0` |
| **`deltaTwoGaloBase'_cup_eq_zero`** | ★★★★★ `y z ∈ VKG ⟹ ∂² (cup y z) = 0`（`hd_infl` 的代数内核） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology
attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
  (hcop : p.Coprime q)

/-- ★★★★★ **`∂²` 的 `GaloBase.H2` 载体版**（元素级标量限制桥）。

与 `Hyp725.deltaTwoGaloBase` 只差一个 `eqToHom` 载体 cast（见文件头）。 -/
noncomputable def deltaTwoGaloBase'
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))] :
    GaloBase.H2 F p →+
      H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p)) :=
  (deltaTwoCarrierInertia (F := F) p q hcop).comp
    (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2).symm.toAddMonoidHom

/-- 定义展开（逐点）。 -/
theorem deltaTwoGaloBase'_apply
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    (u : GaloBase.H2 F p) :
    deltaTwoGaloBase' (F := F) p q hcop u
      = deltaTwoCarrierInertia (F := F) p q hcop
          ((restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2).symm u) :=
  rfl

/-- ★★★★ **`∂² ∘ h2ToGaloBase = ∂²_ℤ ∘ e₂`**（`h2ToGaloBase` 的定义 ⟹ 一步 `symm_apply_apply`）。 -/
theorem deltaTwoGaloBase'_h2ToGaloBase
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    (u : H2 (AbsoluteGaloisGroup F) (ZMod p)) :
    deltaTwoGaloBase' (F := F) p q hcop (h2ToGaloBase (F := F) (p := p) u)
      = deltaTwoCarrierInertia (F := F) p q hcop
          (explicitH2AddEquivContinuousCohomology
            (G := AbsoluteGaloisGroup F) (M := ZMod p) u) := by
  rw [deltaTwoGaloBase'_apply]
  have h1 : h2ToGaloBase (F := F) (p := p) u
      = restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2
          (explicitH2AddEquivContinuousCohomology
            (G := AbsoluteGaloisGroup F) (M := ZMod p) u) := rfl
  rw [h1, AddEquiv.symm_apply_apply]

/-- ★★★★★ **`∂² (infl₂ w) = 0`**（`Hyp750` 方阵 ＋ `Hyp755` 的 `Delta`）。 -/
theorem deltaTwoGaloBase'_infl2Res_eq_zero
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    (w : ResH2Type (F := F) p (inertiaLoc F)) :
    deltaTwoGaloBase' (F := F) p q hcop (infl2Res (F := F) p (inertiaLoc F) w) = 0 := by
  haveI hcl : IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
  set x : H2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) :=
    (eQ2 (F := F) (p := p) (inertiaLoc F)).symm w with hx
  have hw : eQ2 (F := F) (p := p) (inertiaLoc F) x = w := by
    rw [hx]; exact AddEquiv.apply_symm_apply _ _
  rw [← hw, infl2Res_eQ2, deltaTwoGaloBase'_h2ToGaloBase]
  rw [← explicitH2AddEquivContinuousCohomology_map
    (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F) (M := ZMod p)
    (H := AbsoluteGaloisGroup F) (N := ZMod p)
    (φ := Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
    (f := AddMonoidHom.id (ZMod p)) (hf := fun _ _ => rfl) x]
  exact deltaTwoCarrierInertia_map_pair_id_eq_zero (F := F) (p := p) (q := q) (hcop := hcop)
    (explicitH2AddEquivContinuousCohomology
      (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F) (M := ZMod p) x)

/-- ★★★★★★ **`hd_infl` 的代数内核**：`y z ∈ ker v̄ ⟹ ∂² (y ∪ z) = 0`。

（`Hyp749.unramifiedKummer` ⟹ `residueSpan ≤ range infl₂`；`Hyp750`＋`Hyp755` ⟹ `∂²` 在像上为零。） -/
theorem deltaTwoGaloBase'_cup_eq_zero
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    (hpF : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    {v : Fˣ →* Multiplicative ℤ} (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (y z : VKG F p v hpF) :
    deltaTwoGaloBase' (F := F) p q hcop
      (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 := by
  have hmem : GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)
      ∈ residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF) :=
    cup_mem_residueSpan _ _ y z
  have hle := residueSpan_le_range_infl2Res_of_kummer (F := F) (p := p)
    (I := inertiaLoc F) (v := v) hpF
    (unramifiedKummer (F := F) (p := p) hpF hpq v hv hπ)
  obtain ⟨w, hw⟩ := hle hmem
  rw [← hw]
  exact deltaTwoGaloBase'_infl2Res_eq_zero (F := F) (p := p) (q := q) (hcop := hcop) w

end L20261018

#print axioms L20261018.deltaTwoGaloBase'
#print axioms L20261018.deltaTwoGaloBase'_h2ToGaloBase
#print axioms L20261018.deltaTwoGaloBase'_infl2Res_eq_zero
#print axioms L20261018.deltaTwoGaloBase'_cup_eq_zero
