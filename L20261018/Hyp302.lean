import L20261018.Hyp301

/-!
# R1192（**收口：`UnitsCupVanish` 无条件成立**）

按 `PLAN-R2` §H-44 第一–四次补记的全部结论装配。三处记法修法均已经最小复现实测：
* `Subring.coe_pow 𝒪[F] x p : ↑(x^p) = ↑x ^ p`（**带显式参数**）；
* `Units.val_pow_eq_pow_val c p : ↑(c^p) = ↑c ^ p`（**带显式参数**）；
* **凡目标含 ℕ 幂，禁用 `group`**（它会把 ℕ 幂归一成 ℤ 幂后自己处理不了），改用
  `mul_inv_cancel_comm` ＋ `mul_inv_cancel`／`ac_rfl`。

判据分层：装配定理的判据在 `(↥𝒪[F])ˣ` 层，`F` 层的翻译集中在 `not_pow_unitOf`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Final

variable {F : Type} [Field F] [ValuativeRel F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ}

/-- 单位群层的剩余映射。 -/
noncomputable def rho : (↥𝒪[F])ˣ →* (IsLocalRing.ResidueField ↥𝒪[F])ˣ :=
  Units.map (IsLocalRing.residue ↥𝒪[F]).toMonoidHom

theorem coe_rho (a : (↥𝒪[F])ˣ) :
    ((rho (F := F) a : (IsLocalRing.ResidueField ↥𝒪[F])ˣ) : IsLocalRing.ResidueField ↥𝒪[F])
      = IsLocalRing.residue ↥𝒪[F] ((a : ↥𝒪[F])) :=
  Units.coe_map _ _

/-- (U2) 的 `rho` 形式。 -/
theorem exists_unit_rho_eq (r : (IsLocalRing.ResidueField ↥𝒪[F])ˣ) :
    ∃ u : (↥𝒪[F])ˣ, rho (F := F) u = r := by
  obtain ⟨u, hu⟩ := exists_unit_residue_eq ↥𝒪[F] r
  exact ⟨u, Units.ext (by rw [coe_rho]; exact hu)⟩

/-- 运输 2 的 `rho` 形式。 -/
theorem exists_pow_of_rho_eq_one (hp : IsUnit (p : ↥𝒪[F])) {a : (↥𝒪[F])ˣ}
    (ha : rho (F := F) a = 1) : ∃ c : (↥𝒪[F])ˣ, c ^ p = a := by
  refine exists_pow_of_residue_eq_one (F := F) p (NeZero.ne p) hp ?_
  have h3 := congrArg (fun u : (IsLocalRing.ResidueField ↥𝒪[F])ˣ =>
    (u : IsLocalRing.ResidueField ↥𝒪[F])) ha
  simpa [coe_rho] using h3

/-- ★★★★★ **`F` 层判据 → `(↥𝒪[F])ˣ` 层判据**（唯一的跨层搬运）。 -/
theorem not_pow_unitOf (hv : ValCompat (F := F) v) {w : Fˣ} (hw : v w = 1)
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

/-- 交换子恒等式：`a * b * a⁻¹ * b⁻¹ = 1`（CommGroup）。

**不用 `group`** —— 它会把 ℕ 幂归一成 ℤ 幂后自己处理不了（`PLAN-R2` §H-44 第四次补记）。 -/
theorem mul_conj_mul_inv_eq_one {G : Type*} [CommGroup G] (a b : G) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_inv_cancel_comm, mul_inv_cancel]

/-- ★★★★★ **(P) 无条件**（`w` 非 `p` 次幂分支，判据在 `𝒪[F]ˣ` 层给出）。 -/
theorem powClassGen_of_hensel (hp : IsUnit (p : ↥𝒪[F]))
    (hv : ValCompat (F := F) v) {w : Fˣ} (hw : v w = 1) {wu : (↥𝒪[F])ˣ}
    (hwu : ((wu : ↥𝒪[F]) : F) = (w : F))
    (hnotpow : ∀ c : (↥𝒪[F])ˣ, c ^ p ≠ wu) :
    PowClassGen (p := p) v w := by
  intro u hu
  classical
  obtain ⟨uu, huu⟩ := exists_unitOf_of_val_eq_one (F := F) hv hu
  have hW : ∀ Z : (IsLocalRing.ResidueField ↥𝒪[F])ˣ, Z ^ p ≠ rho (F := F) wu := by
    intro Z hZ
    obtain ⟨z₀, hz₀⟩ := exists_unit_rho_eq (F := F) Z
    have h1 : rho (F := F) (wu * (z₀ ^ p)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hz₀, hZ, mul_inv_cancel]
    obtain ⟨c, hc⟩ := exists_pow_of_rho_eq_one (F := F) hp h1
    refine hnotpow (c * z₀) ?_
    have h2 : wu = (c ^ p) * (z₀ ^ p) := by rw [hc]; group
    rw [h2, mul_pow]
  obtain ⟨k, Z, hZk⟩ := exists_pow_mul_pow_of_isCyclic
    (G := (IsLocalRing.ResidueField ↥𝒪[F])ˣ) (Fact.out : p.Prime) hW (rho (F := F) uu)
  obtain ⟨z₀, hz₀⟩ := exists_unit_rho_eq (F := F) Z
  have h1 : rho (F := F) (uu * (wu ^ k)⁻¹ * (z₀ ^ p)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_pow, hz₀, hZk]
    exact mul_conj_mul_inv_eq_one _ _
  obtain ⟨c, hc⟩ := exists_pow_of_rho_eq_one (F := F) hp h1
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
theorem unitsCupVanish {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hv : ValCompat (F := F) v) :
    ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0 :=
  unitsCupVanish_of_powClassGen (p := p) hζ hpF hp2 v
    (fun w hw hnotpow => by
      obtain ⟨wu, hwu⟩ := exists_unitOf_of_val_eq_one (F := F) hv hw
      exact powClassGen_of_hensel (p := p) hp hv hw hwu
        (not_pow_unitOf (p := p) hv hw hnotpow hwu))

end Final

end L20261018

#print axioms L20261018.mul_conj_mul_inv_eq_one
#print axioms L20261018.not_pow_unitOf
#print axioms L20261018.powClassGen_of_hensel
#print axioms L20261018.unitsCupVanish
