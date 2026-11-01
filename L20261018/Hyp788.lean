import Hyp787
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Inflation
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# S76 R1：**`Infl⁻¹` 与杯积的相容**（`GAP3-PLAN` §11.3 的**第 3 步**）

## 这一步在 GS 6.8.4 里的位置

`GAP3-PLAN` §11.3 的五步打法，第 1–2 步已由 `Hyp786`／`Hyp785`／`Hyp787` 闭环：

```
Hyp786   δ⁰ : H⁰(Γ,C) ↠ H¹(Γ,μ_p)                      （取 z₀）
Hyp785   δ¹(z₀ ⌣ y) = δ⁰ z₀ ⌣ y                         （连续槽的 Leibniz）
Hyp787   ∀ π y, ∃ z, δ¹ z = cup11 π y                   （准入件）
```

第 3 步是：**`z = cup01 z₀ (Inf a)` 必须落在 `Infl` 的像里，从而 `Infl⁻¹ z = z₀ ⌣ a`。**
本件把它机检为一条等式（`inflStep` 就是 `Infl⁻¹` 的载体，见 `Hyp719`）。

## 交付

| 声明 | 内容 |
|---|---|
| **`inflStep_explicitCup01`** | ★★★★★ **`Infl⁻¹((Inf z₀) ⌣ (Inf y)) = z₀ ⌣ y`**（一般形，任意系数模 `C`） |
| **`h0_exists_preimage`** | ★★★ `H⁰(Γ,C)` 的每个元素都是某个 `H⁰(Γ⧸I, Cᴵ)` 元素的膨胀（`explicitInfl0_surjective`） |
| **`inflStep_cup01_infl`** | ★★★★★ 惯性载体特化（`C = contC p`、`A = μ_p`、`I = inertiaLoc F`） |

## 证明结构（**零自建数学**，两步）

```
explicitInfl1_explicitCup01   Inf(z₀ ⌣ y) = (Inf z₀) ⌣ (Inf y)              ← 库内（Cup/Inflation:96）
inflStep_explicitInfl1        Infl⁻¹(Inf w) = w                              ← Hyp719 定义级
⟹ Infl⁻¹((Inf z₀) ⌣ (Inf y)) = z₀ ⌣ y
```

`h0_exists_preimage` 使下游不必在 `C`（`Γ`-模）与 `Cᴵ`（`Γ⧸I`-模）之间搬 subtype：
`H0 (Γ⧸I) (Cᴵ)` 与 `H0 Γ C` 的**底层元素**相同（都由 `explicitInfl0` 连接），
`explicitInfl0_surjective` 直接给出原像。
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

/-! ## 1 一般形：`Infl⁻¹` 与杯积的相容 -/

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G] [TotallyDisconnectedSpace G]
variable (N : Subgroup G) [N.Normal] [IsClosed (N : Set G)]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C] [ContinuousSMul G C]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable [ContinuousSMul (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) C)]
  [ContinuousSMul (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) A)]

/-- ★★★★★ **`Infl⁻¹` 与杯积相容**（**GS 6.8.4 的 "cup 与膨胀相容" 那一步**）：

`Infl⁻¹((Inf z₀) ⌣ (Inf y)) = z₀ ⌣ y`。

证明是两步搬运：`explicitInfl1_explicitCup01`（库内）把左边写成 `Infl(Inf⁻¹)`，
`inflStep_explicitInfl1`（`Hyp719` 定义级）消去 `Infl⁻¹ ∘ Infl`。 -/
theorem inflStep_explicitCup01
    (hC : Subsingleton
      ↑(continuousCohomology 1 (ofDiscreteModule ℤ (↥N) C)).toModuleCat)
    (μ : C →+ A →+ C) (hμ : Continuous fun p : C × A => μ p.1 p.2)
    (hequiv : ∀ (g : G) (c : C) (a : A), μ (g • c) (g • a) = g • μ c a)
    (z : ↥(H0 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) C)))
    (y : H1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) A)) :
    inflStep (H := N) (C := C) hC
        (explicitCup01 G C A C μ hμ hequiv
          (explicitInfl0 G C N z) (explicitInfl1 G A N y))
      = explicitCup01 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) C)
          ↥(FixedPoints.addSubgroup (↥N) A) ↥(FixedPoints.addSubgroup (↥N) C)
          (N.fixedPointsPairing μ (fun n => hequiv (n : G)))
          (Subgroup.continuous_fixedPointsPairing N μ (fun n => hequiv (n : G)) hμ)
          (Subgroup.fixedPointsPairing_quotient_smul N μ hequiv) z y := by
  rw [← explicitInfl1_explicitCup01 (G := G) (M := C) (A := A) (P := C) (N := N)
    (μ := μ) (hμ := hμ) (hequiv := hequiv) z y]
  exact inflStep_explicitInfl1 (H := N) (C := C) hC _

end General

/-! ## 2 `H⁰` 侧：`H0 Γ C` 的元素都是膨胀 -/

section DegreeZero

variable {G : Type} [Group G]
variable (N : Subgroup G) [N.Normal]
variable {C : Type} [AddCommGroup C] [DistribMulAction G C]

/-- ★★★ **`H⁰` 侧的膨胀满射**：`H0 G C` 的每个元素都是 `H0 (G⧸N) (Cᴺ)` 某个元素的膨胀。

即 `H⁰(Γ, C) = H⁰(Γ⧸I, Cᴵ)`（底层元素相同）。下游据此把 `δ⁰` 的原像 `z₀` **无损地**搬到
`Γ⧸I` 的 `H⁰` 里，从而能喂给 `inflStep_explicitCup01`。 -/
theorem h0_exists_preimage (z : ↥(H0 G C)) :
    ∃ z' : ↥(H0 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) C)),
      explicitInfl0 G C N z' = z :=
  explicitInfl0_surjective G C N z

end DegreeZero

/-! ## 3 惯性载体特化（论文数据：`Γ = G_F`、`I = inertiaLoc F`、`C = contC p`） -/

section Inertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime]
variable (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
  (hcop : p.Coprime q)

/-- ★★★★★ **惯性载体的第 3 步**：`z ∈ H⁰(Γ⧸I, Cᴵ)`、`y ∈ H¹(Γ⧸I, μ_p)` 时

`Infl⁻¹((Inf z) ⌣ (Inf y)) = z ⌣ y`

（左边 `Infl` 到 `H¹(Γ, C)`，右边住在 `H¹(Γ⧸I, Cᴵ)`）。

`hC` 由 `inertiaLoc_subsingleton_H1_contC`（`Hyp724`）无条件兑现，本里作为显式输入以保持通用性。 -/
theorem inflStep_cup01_infl
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))]
    (hC : Subsingleton
      ↑(continuousCohomology 1
        (ofDiscreteModule ℤ (↥(inertiaLoc F)) (contC (F := F) p))).toModuleCat)
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (y : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) :
    inflStep (H := inertiaLoc F) (C := contC (F := F) p) hC
        (explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p)
          (contC (F := F) p) (smulPairingC (F := F) p) continuous_of_discreteTopology
          (smulPairingC_equivariant (F := F) p)
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z)
          (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y))
      = explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))
          ((inertiaLoc F).fixedPointsPairing (smulPairingC (F := F) p)
            (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F)))
          (Subgroup.continuous_fixedPointsPairing (inertiaLoc F) (smulPairingC (F := F) p)
            (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F))
            continuous_of_discreteTopology)
          (Subgroup.fixedPointsPairing_quotient_smul (inertiaLoc F) (smulPairingC (F := F) p)
            (smulPairingC_equivariant (F := F) p)) z y := by
  haveI : IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
  exact inflStep_explicitCup01 (G := AbsoluteGaloisGroup F) (N := inertiaLoc F)
    (C := contC (F := F) p) (A := ZMod p)
    hC (smulPairingC (F := F) p) continuous_of_discreteTopology
    (smulPairingC_equivariant (F := F) p) z y

end Inertia

end L20261018

#print axioms L20261018.inflStep_explicitCup01
#print axioms L20261018.h0_exists_preimage
#print axioms L20261018.inflStep_cup01_infl
