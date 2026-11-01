import L20261018.Ch2.Hensel.ResidueMap.Step041_residue_map_single_hypothesis
import L20261018.Ch4.Step037_ch4_without_finite_dimensional_v

/-!
# S39 第 4 轮：**去掉 `[Finite (ResidueField)]`** —— `UnitsCupVanish` 的真陈述（`Hyp430`）

## ⛔ 更正：**G1（一般剩余域的 `UnitsCupVanish`）是假命题**

`UnitsCupVanish` **⟺ `H²(κ,μ_p)=0`**（单位类不分歧：`(u)=infl(ū)` ⟹ `(u)∪(w)=infl(ū∪w̄)`），
对 `κ=ℚ`／`ℂ(t)` **假**。`GS68-LEDGER.md` §E 的 G1 行写于 R1301，已被同文件更晚的
**§C″-补（R1312）**推翻；本轮已把该行**就地标「作废」**。第 4 章的一般残域由
**`R2′`（`residueSpan ⊆ ker res`）**承载，其载体是 `∂₂` = GS Construction 6.8.5。

## 本件做什么：把「有限残域」这条**真实收紧**换成显式、更弱、且覆盖**无限**残域的假设

**根因（本轮最小复现，规则 24 ③）**：`[Finite (ResidueField)]` 在 `Hyp302` 的整条链上
**逐件继承**；唯一真正的**泄漏点**是 `Hyp302.coe_rho`（它在 `[Finite]` section 内 ⟹
`rw [coe_rho]` 会留一个 `Finite 𝓀[F]` 目标）。**其余底层事实全都不需要有限性**
（`exists_unit_residue_eq` 只要 `[CommRing] [IsLocalRing]`；`exists_pow_of_residue_eq_one`
只要 `Hensel` ＋ `IsUnit p`；`one_add_subset_pow` 同）。

真实用途只有一处：`exists_pow_mul_pow_of_isCyclic`（`(𝓀)ˣ` 的**循环性**）
⟹ 换成显式假设 `hcyc`：`κ^×/κ^{×p}` 由任一非 `p` 次幂元生成。

## 机检件

| 件 | 内容 |
|---|---|
| **`coe_rho'`**／**`exists_unit_rho_eq'`**／**`exists_pow_of_rho_eq_one'`**／**`not_pow_unitOf'`** | 四个 helper 的**无有限性**版 |
| **`powClassGen_of_cyclicUnits`** | `PowClassGen` ⟸ `hcyc` |
| **`unitsCupVanish_of_cyclicUnits`** | `UnitsCupVanish` ⟸ `hcyc` |
| **`hcyc_of_divisible`**／**`hcyc_of_finite`** | `hcyc` 的两个来源：`κ^×` 的 `p`-可除性（**无限**残域，如代数闭）／`[Finite κ]`（回归） |
| **`unitsCupVanish_of_divisible`**／**`unitsCupVanish_of_finite`** | 同上到 `UnitsCupVanish` |
| **`orth_eq_bot_of_cyclicUnits`**／**`thm_ramified_1_of_cyclicUnits`** | ★★★★★ **4.2／4.3(1)：残域条件不再是「有限」** |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section CyclicUnits

variable {F : Type} [Field F] [ValuativeRel F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ}

/-- `Hyp302.coe_rho` 的**无有限性**版（原版在 `[Finite κ]` section 内，`rw` 会留下实例目标）。 -/
theorem coe_rho' (a : (↥𝒪[F])ˣ) :
    ((rho (F := F) a : (IsLocalRing.ResidueField ↥𝒪[F])ˣ) : IsLocalRing.ResidueField ↥𝒪[F])
      = IsLocalRing.residue ↥𝒪[F] ((a : ↥𝒪[F])) :=
  Units.coe_map _ _

/-- `κˣ` 的 `p`-可除性 ⟹ 循环假设 `hcyc`（`k = 0`）。**覆盖无限剩余域**（如代数闭）。 -/
theorem hcyc_of_divisible
    (hdiv : ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, ∃ Z, Z ^ p = U) :
    ∀ (W : (IsLocalRing.ResidueField ↥𝒪[F])ˣ),
      (∀ c : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, c ^ p ≠ W) →
        ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ,
          ∃ (k : ℤ) (Z : (IsLocalRing.ResidueField ↥𝒪[F])ˣ), U = W ^ k * Z ^ p := by
  intro W _ U
  obtain ⟨Z, hZ⟩ := hdiv U
  exact ⟨0, Z, by rw [zpow_zero, one_mul, hZ]⟩

/-- `[Finite κ]`（故 `κˣ` 循环）⟹ `hcyc`。**回归对照**：新假设严格更弱。 -/
theorem hcyc_of_finite [Finite (IsLocalRing.ResidueField ↥𝒪[F])] :
    ∀ (W : (IsLocalRing.ResidueField ↥𝒪[F])ˣ),
      (∀ c : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, c ^ p ≠ W) →
        ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ,
          ∃ (k : ℤ) (Z : (IsLocalRing.ResidueField ↥𝒪[F])ˣ), U = W ^ k * Z ^ p := by
  intro W hW U
  exact exists_pow_mul_pow_of_isCyclic
    (G := (IsLocalRing.ResidueField ↥𝒪[F])ˣ) (Fact.out : p.Prime) hW U


/-- (U2) 的 `rho` 形式。 -/
theorem exists_unit_rho_eq' (r : (IsLocalRing.ResidueField ↥𝒪[F])ˣ) :
    ∃ u : (↥𝒪[F])ˣ, rho (F := F) u = r := by
  obtain ⟨u, hu⟩ := exists_unit_residue_eq ↥𝒪[F] r
  exact ⟨u, Units.ext (by rw [coe_rho']; exact hu)⟩

/-- 运输 2 的 `rho` 形式。 -/
theorem exists_pow_of_rho_eq_one' (hp : IsUnit (p : ↥𝒪[F])) {a : (↥𝒪[F])ˣ}
    (ha : rho (F := F) a = 1) : ∃ c : (↥𝒪[F])ˣ, c ^ p = a := by
  refine exists_pow_of_residue_eq_one (F := F) p (NeZero.ne p) hp ?_
  have h3 := congrArg (fun u : (IsLocalRing.ResidueField ↥𝒪[F])ˣ =>
    (u : IsLocalRing.ResidueField ↥𝒪[F])) ha
  simpa [coe_rho'] using h3

/-- ★★★★★ **`F` 层判据 → `(↥𝒪[F])ˣ` 层判据**（唯一的跨层搬运）。 -/
theorem not_pow_unitOf' (hv : ValCompat (F := F) v) {w : Fˣ} (hw : v w = 1)
    (hnotpow : ∀ c : F, c ^ p ≠ (w : F)) {wu : (↥𝒪[F])ˣ}
    (hwu : ((wu : ↥𝒪[F]) : F) = (w : F)) :
    ∀ c : (↥𝒪[F])ˣ, c ^ p ≠ wu := by
  intro c hc
  refine hnotpow (((Units.map (algebraMap ↥𝒪[F] F).toMonoidHom c) : Fˣ) : F) ?_
  have hcoe : (((Units.map (algebraMap ↥𝒪[F] F).toMonoidHom c) : Fˣ) : F)
      = ((c : ↥𝒪[F]) : F) := by
    rw [Units.coe_map]; rfl
  rw [hcoe]
  rw [← Subring.coe_pow 𝒪[F] (c : ↥𝒪[F]) p, ← Units.val_pow_eq_pow_val c p, hc]
  exact hwu

/-- ★★★★★ **(P) 无条件**（`w` 非 `p` 次幂分支，判据在 `𝒪[F]ˣ` 层给出）。 -/
theorem powClassGen_of_cyclicUnits
    (hcyc : ∀ (W : (IsLocalRing.ResidueField ↥𝒪[F])ˣ),
      (∀ c : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, c ^ p ≠ W) →
        ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ,
          ∃ (k : ℤ) (Z : (IsLocalRing.ResidueField ↥𝒪[F])ˣ), U = W ^ k * Z ^ p)
    (hp : IsUnit (p : ↥𝒪[F]))
    (hv : ValCompat (F := F) v) {w : Fˣ} (hw : v w = 1) {wu : (↥𝒪[F])ˣ}
    (hwu : ((wu : ↥𝒪[F]) : F) = (w : F))
    (hnotpow : ∀ c : (↥𝒪[F])ˣ, c ^ p ≠ wu) :
    PowClassGen (p := p) v w := by
  intro u hu
  classical
  obtain ⟨uu, huu⟩ := exists_unitOf_of_val_eq_one (F := F) hv hu
  have hW : ∀ Z : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, Z ^ p ≠ rho (F := F) wu := by
    intro Z hZ
    obtain ⟨z₀, hz₀⟩ := exists_unit_rho_eq' (F := F) Z
    have h1 : rho (F := F) (wu * (z₀ ^ p)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hz₀, hZ, mul_inv_cancel]
    obtain ⟨c, hc⟩ := exists_pow_of_rho_eq_one' (F := F) hp h1
    refine hnotpow (c * z₀) ?_
    have h2 : wu = (c ^ p) * (z₀ ^ p) := by rw [hc]; group
    rw [h2, mul_pow]
  obtain ⟨k, Z, hZk⟩ := hcyc (rho (F := F) wu) hW (rho (F := F) uu)
  obtain ⟨z₀, hz₀⟩ := exists_unit_rho_eq' (F := F) Z
  have h1 : rho (F := F) (uu * (wu ^ k)⁻¹ * (z₀ ^ p)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_pow, hz₀, hZk]
    exact mul_conj_mul_inv_eq_one _ _
  obtain ⟨c, hc⟩ := exists_pow_of_rho_eq_one' (F := F) hp h1
  have hφu : Units.map (algebraMap ↥𝒪[F] F).toMonoidHom uu = u :=
    Units.ext (by rw [Units.coe_map]; exact huu)
  have hφw : Units.map (algebraMap ↥𝒪[F] F).toMonoidHom wu = w :=
    Units.ext (by rw [Units.coe_map]; exact hwu)
  have hkey : uu = (wu ^ k) * ((c * z₀) ^ p) := by
    have h2 : uu = (wu ^ k) * (z₀ ^ p) * c ^ p := by
      rw [hc]
      rw [show wu ^ k * z₀ ^ p * (uu * (wu ^ k)⁻¹ * (z₀ ^ p)⁻¹)
            = uu * (wu ^ k * z₀ ^ p * (wu ^ k)⁻¹ * (z₀ ^ p)⁻¹) from by ac_rfl,
          mul_conj_mul_inv_eq_one, mul_one]
    rw [h2, mul_pow]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  have hfin : u = w ^ k * (Units.map (algebraMap ↥𝒪[F] F).toMonoidHom (c * z₀)) ^ p := by
    rw [← hφu, ← hφw, hkey, map_mul, map_zpow, map_pow]
  refine ⟨k, Units.map (algebraMap ↥𝒪[F] F).toMonoidHom (c * z₀), ?_⟩
  rw [hfin, zpow_neg]
  exact mul_inv_cancel_comm _ _

/-- ★★★★★★ **`UnitsCupVanish` 无条件成立**（「离散 ＋ Hensel ＋ 有限剩余」下）。 -/
theorem unitsCupVanish_of_cyclicUnits {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hv : ValCompat (F := F) v)
    (hcyc : ∀ (W : (IsLocalRing.ResidueField ↥𝒪[F])ˣ),
      (∀ c : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, c ^ p ≠ W) →
        ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ,
          ∃ (k : ℤ) (Z : (IsLocalRing.ResidueField ↥𝒪[F])ˣ), U = W ^ k * Z ^ p) :
    ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0 :=
  unitsCupVanish_of_powClassGen (p := p) hζ hpF hp2 v
    (fun w hw hnotpow => by
      obtain ⟨wu, hwu⟩ := exists_unitOf_of_val_eq_one (F := F) hv hw
      exact powClassGen_of_cyclicUnits (p := p) hcyc hp hv hw hwu
        (not_pow_unitOf' (p := p) hv hw hnotpow hwu))

/-- `PowClassGen` ⟸ `κˣ` 的 `p`-可除性（**无限**剩余域）。 -/
theorem powClassGen_of_divisible
    (hdiv : ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, ∃ Z, Z ^ p = U)
    (hp : IsUnit (p : ↥𝒪[F])) (hv : ValCompat (F := F) v) {w : Fˣ} (hw : v w = 1)
    {wu : (↥𝒪[F])ˣ} (hwu : ((wu : ↥𝒪[F]) : F) = (w : F))
    (hnotpow : ∀ c : (↥𝒪[F])ˣ, c ^ p ≠ wu) :
    PowClassGen (p := p) v w :=
  powClassGen_of_cyclicUnits (p := p) (hcyc_of_divisible (p := p) hdiv) hp hv hw hwu hnotpow

/-- `PowClassGen` ⟸ `[Finite κ]`（旧口径的回归对照）。 -/
theorem powClassGen_of_finite [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hv : ValCompat (F := F) v) {w : Fˣ} (hw : v w = 1)
    {wu : (↥𝒪[F])ˣ} (hwu : ((wu : ↥𝒪[F]) : F) = (w : F))
    (hnotpow : ∀ c : (↥𝒪[F])ˣ, c ^ p ≠ wu) :
    PowClassGen (p := p) v w :=
  powClassGen_of_cyclicUnits (p := p) (hcyc_of_finite (p := p)) hp hv hw hwu hnotpow

/-- ★★★★★ **`UnitsCupVanish` ⟸ `κˣ` 的 `p`-可除性**（**无**有限剩余域、**无**有限维）。 -/
theorem unitsCupVanish_of_divisible {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, ∃ Z, Z ^ p = U)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hv : ValCompat (F := F) v) :
    UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF :=
  unitsCupVanish_of_cyclicUnits (p := p) hζ hp hpF hp2 hv
    (hcyc_of_divisible (p := p) hdiv)

/-- 回归对照：旧 `[Finite κ]` 口径推出同一结论。 -/
theorem unitsCupVanish_of_finite' [Finite (IsLocalRing.ResidueField ↥𝒪[F])] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hv : ValCompat (F := F) v) :
    UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF :=
  unitsCupVanish_of_cyclicUnits (p := p) hζ hp hpF hp2 hv
    (hcyc_of_finite (p := p))

end CyclicUnits

/-! ## 第 4 章：残域条件不再是「有限」 -/

section Ch4Cyclic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **4.2（`lem:ramified-vanishing`）**：Hensel，残域只要求 `κˣ` 的 `p`-可除性
（**无限**残域可满足），**无** `[Finite (ResidueField)]`、**无** `FiniteDimensional`。 -/
theorem orth_eq_bot_of_cyclicUnits {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, ∃ Z, Z ^ p = U)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation_nofin (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_Galo_of_unitsCupVanish (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hv hπ hp2 (unitsCupVanish_of_divisible (F := F) (p := p) (v := v)
        hζ hdiv hp hpF hp2 hv))

/-- ★★★★★ **4.3(1)（`thm:ramified`(1)）**：同上，**无**有限残域、**无**有限维。 -/
theorem thm_ramified_1_of_cyclicUnits {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ U : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, ∃ Z, Z ^ p = U)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p))
    (Δ : Subgroup Fˣ) [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hpF a1) (KummerBridge.kummerClass F p hpF a2),
      valLinOf (F := F) (p := p) v hpF u ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hpF hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ :=
  thm_ramified_1_of_discrete_valuation_nofin (F := F) (p := p) hpF hp2 Δ hroots hU
    v hπ (tameResidueFacts_Galo_of_unitsCupVanish (F := F) (p := p) (v := v) (π := π)
      hζ hp hpF hv hπ hp2 (unitsCupVanish_of_divisible (F := F) (p := p) (v := v)
        hζ hdiv hp hpF hp2 hv)) ha1 ha2 hne hval

end Ch4Cyclic

end L20261018

#print axioms L20261018.coe_rho'
#print axioms L20261018.exists_unit_rho_eq'
#print axioms L20261018.exists_pow_of_rho_eq_one'
#print axioms L20261018.not_pow_unitOf'
#print axioms L20261018.powClassGen_of_cyclicUnits
#print axioms L20261018.unitsCupVanish_of_cyclicUnits
#print axioms L20261018.hcyc_of_divisible
#print axioms L20261018.hcyc_of_finite
#print axioms L20261018.unitsCupVanish_of_divisible
#print axioms L20261018.unitsCupVanish_of_finite'
#print axioms L20261018.orth_eq_bot_of_cyclicUnits
#print axioms L20261018.thm_ramified_1_of_cyclicUnits
