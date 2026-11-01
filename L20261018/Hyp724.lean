import Hyp723
import Hyp380

/-!
# S64 R13：**`hC` 在惯性群上兑现**（`Hyp723` 的第一条假设消失）

`Hyp723.deltaTwoCarrier`（战役载体上的 `∂²`）带两条假设，其中
`hC : Subsingleton (H¹(I, C))` 是 GS 的 C 步输入。本件在 `I = inertiaLoc F` 上**无条件**给出它：

```
hA2 : Subsingleton (H²(I, μ_p))     ⟸ Hyp517.inertiaLoc_subsingleton_Hq（n ≥ 2 无条件消失）
hC  : Subsingleton (H¹(I, C))       ⟸ Hyp716.subsingleton_H1_quot_subgroup_of_isClosed（B 步 ＋ LES）
```

| 声明 | 内容 |
|---|---|
| `isPPrimaryTorsion_zmod_p` | ★★★ `IsPPrimaryTorsion p (ZMod p)`（可复用；`Hyp628` 里原本是内联三行） |
| **`inertiaLoc_subsingleton_H1_contC`** | ★★★★★ **C 步（惯性载体）：`Subsingleton (H¹(I, contC))`** |
| **`deltaTwoCarrierInertia`** | ★★★★★ `∂² : H²(Γ,μ_p) →+ H1 (Γ⧸I) (H¹(I,μ_p))`，**只剩 `ContinuousSMul` 一条技术假设** |
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

/-- `IsPPrimaryTorsion p (ZMod p)`：`ZMod p` 的元素都被 `p` 杀掉（元素层证法，见 `Hyp628`）。 -/
theorem isPPrimaryTorsion_zmod_p (p : ℕ) [Fact p.Prime] : IsPPrimaryTorsion p (ZMod p) := by
  rw [isPPrimaryTorsion_iff]
  intro m
  exact ⟨1, by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul (ZMod p) p m, ZMod.natCast_self p, zero_smul]⟩

section Inertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime]

/-- ★★★★★ **C 步（惯性载体）**：`H¹(I, C) = 0`，`I = inertiaLoc F`，`C = CoindQuotient Γ ⊥ μ_p`。

两条输入都无条件：
* `H²(I, μ_p) = 0` —— `Hyp517.inertiaLoc_subsingleton_Hq`（`n ≥ 2` 消失）；
* B 步 —— `Hyp716.subsingleton_H1_quot_subgroup_of_isClosed`（`Hyp715`＋`Hyp716`）。 -/
theorem inertiaLoc_subsingleton_H1_contC (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) :
    Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (contC (F := F) p))) := by
  haveI : IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
  have hA2 : Subsingleton (continuousCohomology 2
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (ZMod p))) :=
    inertiaLoc_subsingleton_Hq (F := F) q p hcop (ZMod p) (isPPrimaryTorsion_zmod_p p) (n := 2) (le_refl 2)
  exact subsingleton_H1_quot_subgroup_of_isClosed (G := AbsoluteGaloisGroup F) (A := ZMod p)
    (inertiaLoc F) hA2

/-- ★★★★★ **惯性载体上的 `∂²`**：`H²(Γ,μ_p) →+ H¹(Γ⧸I, H¹(I,μ_p))`。

`Hyp723.deltaTwoCarrier` 的 `hC` 已由 `inertiaLoc_subsingleton_H1_contC` 兑现，
**只剩 `[ContinuousSMul (Γ⧸I) (H¹(I,μ_p))]` 一条技术假设**（由 `Hyp520`／`Hyp521` 的有限性给出）。 -/
noncomputable def deltaTwoCarrierInertia (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))] :
    continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) →+
      H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p)) := by
  haveI : IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
  exact deltaTwoCarrier (F := F) p (inertiaLoc F)
    (inertiaLoc_subsingleton_H1_contC (F := F) p q hcop)

end Inertia

end L20261018

#print axioms L20261018.isPPrimaryTorsion_zmod_p
#print axioms L20261018.inertiaLoc_subsingleton_H1_contC
#print axioms L20261018.deltaTwoCarrierInertia
