import L20261018.Infra.Cohomology.Coinduced.Step041_infl_inverse_cup

/-!
# S76 R2：**把第 3 步接到 `∂²`** —— `∂²(π ⌣ Inf y) = contM (z₀ ⌣ y)` 的显式取值

## 本件做什么

`GAP3-PLAN` §11.3 的第 3 步（`Hyp788`）给出 `Infl⁻¹((Inf z₀) ⌣ (Inf y)) = z₀ ⌣ y`。
本件把它**接进** `∂²` 的分解：

```
∂² = contM_coeffMap ∘ deltaTwoShift
deltaTwoShift = inflStep ∘ h1BridgeQ ∘ δ⁻¹        （Hyp781.deltaTwoShift_apply，定义级）
```

于是（`z₃ := cup01 (e₀ (Inf z)) (e₁ (Inf y))`、`δ¹ z₃ = π ⌣ Inf y`）：

```
∂²(π ⌣ Inf y) = contM_coeffMap ( inflStep (h1BridgeQ z₃) )
              = contM_coeffMap ( explicitCup01 (Inf z) (Inf y) )   ← 本件 h1BridgeQ_cup01
              = contM_coeffMap ( Inf(z ⌣ y) )                     ← Hyp788（第 3 步）
```

## 交付

| 声明 | 内容 |
|---|---|
| **`h1BridgeQ_cup01`** | ★★★★ `h1BridgeQ (cup01 (e₀ m) (e₁ y)) = explicitCup01 m y` |
| **`h1BridgeQ_cup01_of_infl`** | ★★★★ 同上，`m` 取 `explicitInfl0 z`（下游要的形状） |
| **`deltaTwoCarrierInertia_cup_eq`** | ★★★★★ **`∂²(π ⌣ Inf y) = contM(z₀ ⌣ y)`**（`δ⁰(Inf z) = π`） |

## 诚实边界

本件是**第 3 步的装配**：数学内容全在 `Hyp788` ＋ `Hyp781`／`Hyp787`，本件只做搬运。
**仍缺**（R3 起）：第 4 步（`contM` 与杯积的相容，`coeffMap contM 1 (z₀ ⌣ y) = (contM z₀) ⌣ y`）
与第 5 步（非零性）。
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

/-! ## 0 四个载体缩写（与 `Hyp787` 同口径；用 `abbrev` 而非 `notation`，避免投影记法报错） -/

/-- 显式 `H0 Γ C` → 连续 `H⁰(Γ, C)`。 -/
noncomputable abbrev h0Emb (m : ↥(H0 (AbsoluteGaloisGroup F) (contC (F := F) p))) :
    continuousCohomology 0 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)) :=
  (CategoryTheory.ConcreteCategory.hom
    (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom) m

/-- 连续模型的 `(0,1)` 杯积 `H⁰(Γ,C) × H¹(Γ,μ_p) → H¹(Γ,C)`。 -/
noncomputable abbrev cup01C
    (x : continuousCohomology 0 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)))
    (y : continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p))) :
    continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)) :=
  ((ofDiscreteModulePairing (smulPairingC (F := F) p) (smulPairingC_equivariant (F := F) p)).cup 0 1) x y

/-- 连续模型的 `(1,1)` 杯积 `H¹(Γ,μ_p) × H¹(Γ,μ_p) → H²(Γ,μ_p)`。 -/
noncomputable abbrev cup11A
    (x y : continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p))) :
    continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) :=
  ((ofDiscreteModulePairing (mulPairing (p := p)) (mulPairing_equivariant (F := F) p)).cup 1 1) x y

/-! ## 1 `h1BridgeQ` 把连续 `cup01` 换成显式 `explicitCup01` -/

/-- ★★★★ **`h1BridgeQ` 与 `(0,1)` 杯积相容**：`h1BridgeQ (cup01 (e₀ m) (e₁ y)) = explicitCup01 m y`。

即 `Cup/Comparison.explicitAddEquiv_cup01`（`e₁ (m ⌣ y) = (e₀ m) ⌣ (e₁ y)`）的**反向使用**：
`h1BridgeQ` 就是 `e₁.symm`。 -/
theorem h1BridgeQ_cup01 (m : ↥(H0 (AbsoluteGaloisGroup F) (contC (F := F) p)))
    (y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    h1BridgeQ (C := contC (F := F) p)
        (cup01C (F := F) p (h0Emb (F := F) p m)
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) y))
      = explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p)
          (contC (F := F) p) (smulPairingC (F := F) p) continuous_of_discreteTopology
          (smulPairingC_equivariant (F := F) p) m y := by
  rw [show cup01C (F := F) p (h0Emb (F := F) p m)
      (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) y)
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)
          (explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p)
            (contC (F := F) p) (smulPairingC (F := F) p) continuous_of_discreteTopology
            (smulPairingC_equivariant (F := F) p) m y) from
    explicitAddEquiv_cup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p)
      (contC (F := F) p) (smulPairingC (F := F) p) (smulPairingC_equivariant (F := F) p) m y]
  exact AddEquiv.symm_apply_apply _ _

section Inertia

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- 技术实例（非数学假设）：`I = inertiaLoc F` 闭 ⟹ 紧。见 `PROMPT-S76` §3。 -/
local instance instClosedInertiaLocS76 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS76 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 紧（由闭 ＋ `Γ` 紧）。 -/
local instance instCompactInertiaLocS76 : CompactSpace ↥(inertiaLoc F) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaLoc F).isCompact

/-- ★★★★ 下游要的形状：`m = explicitInfl0 z`（`z : H⁰(Γ⧸I, Cᴵ)`）。

与 `h1BridgeQ_cup01` 相同，只是把 `m` 写成膨胀 —— 于是下面可以直接喂 `Hyp788`。 -/
theorem h1BridgeQ_cup01_of_infl
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    h1BridgeQ (C := contC (F := F) p)
        (cup01C (F := F) p
          (h0Emb (F := F) p
            (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) y))
      = explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p)
          (contC (F := F) p) (smulPairingC (F := F) p) continuous_of_discreteTopology
          (smulPairingC_equivariant (F := F) p)
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z) y :=
  h1BridgeQ_cup01 (F := F) p _ y

/-! ## 2 主定理：`∂²(π ⌣ Inf y) = contM(z₀ ⌣ y)` -/

/-- ★★★★★ **`∂²` 在 `π ⌣ Inf y` 上的显式取值**：

设 `z : H⁰(Γ⧸I, Cᴵ)`、`y ∈ H¹(Γ⧸I, μ_p)`、`π ∈ H¹(Γ, μ_p)`，且
`δ⁰(Inf z) = π`（可取到，`Hyp786`）。则

```
∂²(π ⌣ Inf y) = contM ( Inf z ⌣ Inf y )  =  contM ( z ⌣ y )
```

**这是 GS 6.8.4 的 `p = q = 1` 支在本战役的机检形态**，第 4 步（把 `contM` 推进杯积）
只差 `contM` 的加性。 -/
theorem deltaTwoCarrierInertia_cup_eq
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (H1 (↥(inertiaLoc F)) (ZMod p))]
    (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q)
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (y : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (π : continuousCohomology 1
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)))
    (hπ : ((contCoindSES (F := F) p).delta 0).hom
        (h0Emb (F := F) p
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z)) = π) :
    deltaTwoCarrierInertia (F := F) p q hcop
        (cup11A (F := F) p π
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
            (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y)))
      = contM_coeffMap (F := F) p (inertiaLoc F)
          (explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))
            ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
            ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))
            ((inertiaLoc F).fixedPointsPairing (smulPairingC (F := F) p)
              (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F)))
            (Subgroup.continuous_fixedPointsPairing (inertiaLoc F) (smulPairingC (F := F) p)
              (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F))
              continuous_of_discreteTopology)
            (Subgroup.fixedPointsPairing_quotient_smul (inertiaLoc F) (smulPairingC (F := F) p)
              (smulPairingC_equivariant (F := F) p)) z y) := by
  show contM_coeffMap (F := F) p (inertiaLoc F)
      (deltaTwoShift (H := inertiaLoc F) (A := ZMod p) (B := contB (F := F) p)
        (C := contC (F := F) p) (contCoindSES (F := F) p)
        (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
          (AbsoluteGaloisGroup F) (ZMod p) 0)
        (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
          (AbsoluteGaloisGroup F) (ZMod p) 1)
        (inertiaLoc_subsingleton_H1_contC (F := F) p q hcop)
        (cup11A (F := F) p π
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
            (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y))))
    = contM_coeffMap (F := F) p (inertiaLoc F) _
  congr 1
  have hδ : ((contCoindSES (F := F) p).delta 1).hom
      (cup01C (F := F) p
        (h0Emb (F := F) p
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
        (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y)))
      = cup11A (F := F) p π
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
            (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y)) := by
    rw [contLeibniz_cup01_cont (F := F) p, hπ]
  rw [← hδ]
  refine deltaTwoShift_eq_of_delta_eq (H := inertiaLoc F) (C := contC (F := F) p)
    (S := contCoindSES (F := F) p)
    (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
      (AbsoluteGaloisGroup F) (ZMod p) 0)
    (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
      (AbsoluteGaloisGroup F) (ZMod p) 1)
    (inertiaLoc_subsingleton_H1_contC (F := F) p q hcop)
    (cup01C (F := F) p
      (h0Emb (F := F) p
        (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
        (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y)))
    ?_
  rw [h1BridgeQ_cup01_of_infl (F := F) p z
    (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y)]
  exact inflStep_cup01_infl (F := F) p
    (inertiaLoc_subsingleton_H1_contC (F := F) p q hcop) z y

end Inertia

end L20261018

#print axioms L20261018.h1BridgeQ_cup01
#print axioms L20261018.h1BridgeQ_cup01_of_infl
#print axioms L20261018.deltaTwoCarrierInertia_cup_eq
