import L20261018.Hyp364

/-!
# R1276（S36 C 项）：muNRep 层的 `(kc_T 2) ∪ (kc_T π) ≠ 0`

`HANDOFF` §R1275 补记的配方：4.3(1) 的 `hne` 需要**显式对** `(2, π)` 的非零杯积，
而 `FqD.pi` **不是** `kc_T π`（实测 `rfl` 失败），故不能用 `FqD.tame_u_pi` 直接取。
**改用 `res` 的非零性**（全程只用 `HenselResidueData` 的结构字段）：

```
split (kc_T π) = infl x₀ + m • FqD.pi
  val 侧：val(kc_T π) = (toAdd (zval π) : ZMod 3) = 1、val(infl x₀) = 0、val(D.pi) = 1 ⟹ m = 1
  res 侧：res (cup (inf y) (kc_T π)) = res (cup (inf y) (inf x₀)) + 1 • res (cup (inf y) D.pi)
                                    = 0 + y = y ≠ 0        -- tame_uu、tame_u_pi
⟹ (cup) (kc_T 2) (kc_T π) ≠ 0。
```

| 声明 | 内容 |
|---|---|
| **`val_kc_pi`** | `FqD.val (kc_T π) = 1` |
| **`hcupT_pi`** | ★★★★★★ **`(cup) (kc_T 2) (kc_T π) ≠ 0`**（muNRep 载体） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity (LaurentSeries (ZMod 7)) 3 :=
  hasEnoughRootsOfUnity_laurentSeries_zmod7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `muNRep` 载体的 `kc_T π`。 -/
noncomputable def piT :
    ↑(continuousCohomology 1
      (ClassFieldTheory.muNRep 3 (LaurentSeries (ZMod 7)))).toModuleCat :=
  ClassFieldTheory.kummerClass (LaurentSeries (ZMod 7)) three_isUnit_laurentSeries
    (pi : (LaurentSeries (ZMod 7))ˣ)

/-- ★★★★ **`val (kc_T π) = 1`**。 -/
theorem val_kc_pi : FqD.val piT = (1 : ZMod 3) := by
  rw [FqD_val]
  show valH1Gen (p := 3) (vCompatHom (F := LaurentSeries (ZMod 7)))
    three_isUnit_laurentSeries piT = 1
  rw [show piT = ClassFieldTheory.kummerClass (LaurentSeries (ZMod 7))
    three_isUnit_laurentSeries (pi : (LaurentSeries (ZMod 7))ˣ) from rfl, valH1Gen_kummerClass]
  rw [show vCompatHom (F := LaurentSeries (ZMod 7)) (pi : (LaurentSeries (ZMod 7))ˣ)
    = Multiplicative.ofAdd (1 : ℤ) from pi_hπ]
  rfl

/-- ★★★★★★ **`(kc_T 2) ∪ (kc_T π) ≠ 0`**（`muNRep` 载体）。

取 `x = kc_T 2`、`y` 使 `inf y = x`（`y ≠ 0`）。由 `split`：`kc_T π = inf x₀ + m • D.pi`，
`val` 侧给出 `m = 1`；于是 `res (cup (inf y) (kc_T π)) = 0 + y = y ≠ 0`，
故 `cup (kc_T 2) (kc_T π) ≠ 0`。 -/
theorem hcupT_pi :
    ((ClassFieldTheory.kummerCupPairing zetaF zetaF_spec).cup 1 1) xF piT ≠ 0 := by
  -- `x = kc_T 2` 在 `ker v̄` 中，取 `y` 使 `inf y = x`
  have hxval : FqD.val xF = 0 := by
    rw [FqD_val]
    show valH1Gen (p := 3) (vCompatHom (F := LaurentSeries (ZMod 7)))
      three_isUnit_laurentSeries xF = 0
    rw [show xF = ClassFieldTheory.kummerClass (LaurentSeries (ZMod 7))
      three_isUnit_laurentSeries twoUnitF from rfl, valH1Gen_kummerClass]
    have hz : zval (F := LaurentSeries (ZMod 7)) twoUnitF = 0 :=
      zval_unit_eq_zero (F := LaurentSeries (ZMod 7)) two_isUnit_O
    rw [show vCompatHom (F := LaurentSeries (ZMod 7)) twoUnitF
      = Multiplicative.ofAdd (zval (F := LaurentSeries (ZMod 7)) twoUnitF) from rfl, hz]
    simp
  obtain ⟨y, hy⟩ := (exact_infl_val FqD xF).mp hxval
  have hyne : y ≠ 0 := by
    intro h0
    exact xF_ne_zero (by rw [← hy, h0, map_zero])
  -- `split`：`kc_T π = inf x₀ + m • D.pi`，且 `m = 1`
  obtain ⟨x₀, m, hsplit⟩ := FqD.split piT
  have hm : m = 1 := by
    have hval := congrArg FqD.val hsplit
    rw [map_add, map_smul, FqD.val_infl, FqD.val_pi, val_kc_pi] at hval
    simpa using hval.symm
  -- `res` 侧
  have hres : FqD.res (((ClassFieldTheory.kummerCupPairing zetaF zetaF_spec).cup 1 1) xF piT)
      = y := by
    conv_lhs => rw [hsplit]
    simp only [map_add, map_smul, ← hy, FqD.tame_uu, FqD.tame_u_pi, hm, one_smul, zero_add]
  intro h0
  rw [h0, map_zero] at hres
  exact hyne hres.symm

end FqXt
end L20261018

#print axioms L20261018.FqXt.val_kc_pi
#print axioms L20261018.FqXt.hcupT_pi
