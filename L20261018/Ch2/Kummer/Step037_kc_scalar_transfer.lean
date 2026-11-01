import L20261018.Ch2.Kummer.Step036_kc_scalar_from_coefficient

/-!
# R1214（标量传递：完成）

`PLAN-VALCOMPAT-HBRIDGE.md` §K：残式 `k • z = c • z` 的修法 =
把半环显式给 `Nat.cast_smul_eq_nsmul`。

## 本轮
| 声明 | 内容 |
|---|---|
| `smulHom` | `y ↦ c • y` 作为 `G`-等变加法同态 |
| **`kummerH1Equiv_eq_smul_canon`** | ★★★★★ `∃ c ≠ 0, kummerH1Equiv = c • kummerH1EquivCanon` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section ScalarTransfer

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- `y ↦ c • y` 作为 `G`-等变加法同态（`G` 在 `ZMod p` 上作用定义性平凡）。 -/
noncomputable def smulHom (c : ZMod p) :
    ZMod p →+[AbsoluteGaloisGroup F] ZMod p where
  toFun := fun y => c • y
  map_zero' := smul_zero c
  map_add' := fun a b => smul_add c a b
  map_smul' := fun _ _ => rfl

/-- ★★★★★ **标量从系数层传到 `H¹` 层**：`KummerBridge.kummerH1Equiv` 与规范版
`kummerH1EquivCanon` 只差 `Hyp311` 的那个非零标量。 -/
theorem kummerH1Equiv_eq_smul_canon (hp : IsUnit (p : F)) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ x : ContCohomology.H1 (AbsoluteGaloisGroup F) (KummerCoeff F p),
      KummerBridge.kummerH1Equiv F p hp x
        = c • (kummerH1EquivCanon (p := p) (F := F) hζ x) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_smul_kummerCoeffLinearEquiv (F := F) (p := p) hζ hp
  set k : ℕ := c.val with hkdef
  have hk : (k : ZMod p) = c := by rw [hkdef]; exact ZMod.natCast_zmod_val c
  have hcv : ∀ y : ZMod p, c • y = k • y := by
    intro y
    rw [← hk, Nat.cast_smul_eq_nsmul]
  refine ⟨c, hc0, fun x => ?_⟩
  set f : KummerCoeff F p →+[AbsoluteGaloisGroup F] ZMod p :=
    { (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv.toAddMonoidHom with
      map_smul' := fun g m => by rw [smul_kummerCoeff_eq_self hζ g m]; rfl }
  set f₀ : KummerCoeff F p →+[AbsoluteGaloisGroup F] ZMod p :=
    { (SymbolCupBridge.kummerCoeffLinearEquiv (p := p) (ζ := ζ) hζ).toAddEquiv.toAddMonoidHom with
      map_smul' := fun g m => by rw [smul_kummerCoeff_eq_self hζ g m]; rfl }
  have hfq : f = (smulHom (F := F) (p := p) c).comp f₀ := by
    ext m
    exact hc m
  have hstep : ∀ y : ContCohomology.H1 (AbsoluteGaloisGroup F) (KummerCoeff F p),
      ContCohomology.explicitCoeff1 (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p)
        f continuous_of_discreteTopology y
      = c • (ContCohomology.explicitCoeff1 (G := AbsoluteGaloisGroup F)
          (M := KummerCoeff F p) f₀ continuous_of_discreteTopology y) := by
    intro y
    rw [hfq,
      ContCohomology.explicitCoeff1_comp (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p)
        (N := ZMod p) (P := ZMod p) f₀ (smulHom (F := F) (p := p) c)
        continuous_of_discreteTopology continuous_of_discreteTopology,
      AddMonoidHom.comp_apply,
      ContCohomology.explicitCoeff1_eq_nsmul (G := AbsoluteGaloisGroup F) (M := ZMod p)
        (smulHom (F := F) (p := p) c) continuous_of_discreteTopology (k := k) hcv,
      ← Nat.cast_smul_eq_nsmul (ZMod p) k
        (ContCohomology.explicitCoeff1 (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p)
          f₀ continuous_of_discreteTopology y),
      hk]
  calc KummerBridge.kummerH1Equiv F p hp x
      = ContCohomology.explicitCoeff1 (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p)
          f continuous_of_discreteTopology x := rfl
    _ = c • (ContCohomology.explicitCoeff1 (G := AbsoluteGaloisGroup F)
          (M := KummerCoeff F p) f₀ continuous_of_discreteTopology x) := hstep x
    _ = c • (kummerH1EquivCanon (p := p) (F := F) hζ x) := rfl

end ScalarTransfer

end L20261018

#print axioms L20261018.kummerH1Equiv_eq_smul_canon
