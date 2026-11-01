import Hyp748
import Hyp187

/-!
# S68 R4：★★★ **`UnramifiedKummer` 在论文口径下（`ValCompat` ＋ `v π = 1`，`v` 任意）**

## 结果

`unramifiedKummer`：
```
(hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
(v : Fˣ →* Multiplicative ℤ) (hv : ValCompat v) (hπ : v π = ofAdd 1)
⟹ UnramifiedKummer (F := F) p (inertiaLoc F) (v := v) hp
```
⟹ **`Hyp744.UnramifiedKummer` 不再是假设**：论文 `prop:prelim-kummer-valuation`(2) 的
「`ker v̄ ⊆ range infl`」一半在 `Hyp342`／`Hyp610` 的实际假设下成立。

## 与 `Hyp748` 的分工

| 件 | `v` 的口径 |
|---|---|
| `Hyp748.unramifiedKummer_of_inertia` | `v = normalizedValuation F` |
| **`Hyp749.unramifiedKummer`** | **`ValCompat v` ＋ `v π = 1`**（论文口径，本件） |

## 关键：下游真正需要的只是**两条单位判据**（不需 `v = nv`）

| 判据 | 件 |
|---|---|
| `u ∈ unitFiltration F 0 ⟹ v u = 1` | `val_eq_one_of_mem_unitFiltration_zero` |
| `v u = 1 ⟹ u ∈ unitFiltration F 0` | `mem_unitFiltration_zero_of_val_eq_one` |

`Hyp747` 的 `valLinOf` 侧证明原本靠 `v = nv`；本件把这两处换成上述两条 ⟹ 得
`valLinOf_eq_zero_iff_exists_unit_of_valCompat`（`v` 任意）与 `valLinOf_eq_zero_iff_res1V_eq_zero_of_valCompat`。

## 下界证明的一句话

「`v u < 0` ⟹ `v (u⁻¹) > 0` ⟹ `u⁻¹ ∈ 𝔪`（`ValCompat.mem_maximalIdeal`），而 `u⁻¹` 是 `𝒪_F` 的单位，
与 `notMem_maximalIdeal` 矛盾。」——**不需要** `v = normalizedValuation F`，也不需要
「`v` 与 `normalizedValuation` 只差正倍数」。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

section ValCompatUnits

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {v : Fˣ →* Multiplicative ℤ}

/-- `𝒪_F^× ↪ F^×`（沿 `Subring.subtype` 的 `Units.map`；`TauCeti.unitFiltration` 的内部口径）。 -/
noncomputable def unitsCoe (F : Type) [Field F] [ValuativeRel F] : 𝒪[F]ˣ →* Fˣ :=
  Units.map (Subring.subtype 𝒪[F]).toMonoidHom

/-- `unitsCoe` 的底层元素。 -/
theorem unitsCoe_apply (F : Type) [Field F] [ValuativeRel F] (w : 𝒪[F]ˣ) :
    ((unitsCoe F w : Fˣ) : F) = ((w : 𝒪[F]) : F) := rfl

/-- ★★★★ **`ValCompat` 下 `v = 0` 的 `Fˣ` 元素给出 `𝒪_F` 的单位**：
`v u = 1` ⟹ 存在 `w : 𝒪_F^×` 使 `w = u`。 -/
theorem exists_valuationRing_unit_of_val_eq_one (hv : ValCompat (F := F) v) {u : Fˣ}
    (hu : v u = 1) : ∃ w : 𝒪[F]ˣ, ((w : 𝒪[F]) : F) = (u : F) := by
  have h0 : 0 ≤ Multiplicative.toAdd (v u) := by rw [hu]; rfl
  have hO : (u : F) ∈ 𝒪[F] := hv.mem_integer u h0
  have hnot : (⟨(u : F), hO⟩ : 𝒪[F]) ∉ IsLocalRing.maximalIdeal ↥𝒪[F] := by
    rw [hv.mem_maximalIdeal u hO]
    rw [hu]
    exact not_lt.mpr le_rfl
  have hunit : IsUnit (⟨(u : F), hO⟩ : 𝒪[F]) := notMem_maximalIdeal.mp hnot
  exact ⟨hunit.unit, by simp⟩

/-- ★★★★★ **`ValCompat` 下 `unitFiltration F 0` 上 `v` 为零**（`𝒪_F` 的单位有 `v = 0`）。 -/
theorem val_eq_one_of_mem_unitFiltration_zero (hv : ValCompat (F := F) v) {u : Fˣ}
    (hu : u ∈ unitFiltration F 0) : v u = 1 := by
  have hval : valuation F (u : F) = 1 := (mem_unitFiltration_zero u).mp hu
  have hO : (u : F) ∈ 𝒪[F] := (Valuation.mem_integer_iff (valuation F) (u : F)).mpr (le_of_eq hval)
  have hunit : IsUnit (⟨(u : F), hO⟩ : 𝒪[F]) :=
    (Valuation.integer.integers (valuation F)).isUnit_of_one' hval
  set w : 𝒪[F]ˣ := hunit.unit with hwdef
  have hw : ((w : 𝒪[F]) : F) = (u : F) := by simp [hwdef]
  have hcoe : unitsCoe F w = u := Units.ext (by rw [unitsCoe_apply, hw])
  -- 上界：`¬ 0 < v u`
  have hle : ¬ (0 < Multiplicative.toAdd (v u)) := by
    rw [← hv.mem_maximalIdeal u hO]
    refine notMem_maximalIdeal.mpr ?_
    have hWeq : (⟨(u : F), hO⟩ : 𝒪[F]) = (w : 𝒪[F]) := Subtype.ext hw.symm
    rw [hWeq]
    exact w.isUnit
  -- 下界：`0 ≤ v u`，用 `w⁻¹`
  have hge : 0 ≤ Multiplicative.toAdd (v u) := by
    by_contra hlt
    rw [not_le] at hlt
    set w' : 𝒪[F]ˣ := w⁻¹ with hw'def
    have hcoe' : unitsCoe F w' = u⁻¹ := by
      rw [hw'def, map_inv, hcoe]
    have hinv : Multiplicative.toAdd ((v u)⁻¹) = - Multiplicative.toAdd (v u) := by simp
    have hpos : 0 < Multiplicative.toAdd (v (unitsCoe F w')) := by
      rw [hcoe', map_inv, hinv]
      omega
    have hO' : ((unitsCoe F w' : Fˣ) : F) ∈ 𝒪[F] := hv.mem_integer _ (le_of_lt hpos)
    have hcoeF : ((unitsCoe F w' : Fˣ) : F) = ((w' : 𝒪[F]) : F) := unitsCoe_apply F w'
    have hmem : (w' : 𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
      have : (⟨((unitsCoe F w' : Fˣ) : F), hO'⟩ : 𝒪[F]) = (w' : 𝒪[F]) := Subtype.ext hcoeF.symm
      rw [← this]
      exact (hv.mem_maximalIdeal (unitsCoe F w') hO').mpr hpos
    exact notMem_maximalIdeal.mpr w'.isUnit hmem
  have hzero : Multiplicative.toAdd (v u) = 0 := le_antisymm (not_lt.mp hle) hge
  exact Multiplicative.toAdd.injective (by simpa using hzero)

/-- ★★★★★ **反向：`v u = 1` ⟹ `u ∈ unitFiltration F 0`**
（`unitFiltration F 0` ＝ `𝒪_F^×`，`TauCeti.mem_unitFiltration_zero`）。 -/
theorem mem_unitFiltration_zero_of_val_eq_one (hv : ValCompat (F := F) v) {u : Fˣ}
    (hu : v u = 1) : u ∈ unitFiltration F 0 := by
  obtain ⟨w, hw⟩ := exists_valuationRing_unit_of_val_eq_one hv hu
  refine (mem_unitFiltration_zero u).mpr ?_
  have hwval : valuation F (((w : 𝒪[F]) : F)) = 1 :=
    (Valuation.integer.integers (valuation F)).valuation_unit w
  rw [← hw]
  exact hwval

end ValCompatUnits

section ValCompatKummer

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **`v̄` 的零点集（`ValCompat` 版，`v` 任意）**：
`v̄ y = 0 ⟺ y` 是某个 `𝒪_F^×` 元素的 Kummer 类。

（`Hyp747.valLinOf_eq_zero_iff_exists_unit` 假设了 `v = normalizedValuation F`；本件把它换成
`Hyp187.ValCompat v` ＋ `v π = 1`，即下游 `Hyp342`／`Hyp610` 的实际口径。） -/
theorem valLinOf_eq_zero_iff_exists_unit_of_valCompat
    (hp : IsUnit (p : F)) (v : Fˣ →* Multiplicative ℤ) (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (y : GaloBase.V F p) :
    valLinOf (F := F) (p := p) v hp y = 0
      ↔ ∃ u ∈ unitFiltration F 0, KummerBridge.kummerClass F p hp u = y := by
  classical
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := KummerV.kummerClass_surjective (F := F) (p := p) hp y
    have hva : ((Multiplicative.toAdd (v a) : ℤ) : ZMod p) = 0 := by
      have h0 : valLinOf (F := F) (p := p) v hp
          (KummerBridge.kummerClass F p hp a) = 0 := by rw [ha]; exact hy
      rwa [valLinOf_kummerClass] at h0
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hva
    -- `u := a · (π^{-k})^p`：与 `a` 差一个 `p` 次幂，且 `v u = 0`
    have h1 : π ^ (-k) * π ^ k = 1 := by
      rw [zpow_neg]; exact inv_mul_cancel _
    have hfactor : a = (a * (π ^ (-k)) ^ p) * (π ^ k) ^ p := by
      rw [mul_assoc, ← mul_pow, h1, one_pow, mul_one]
    have hzero : KummerBridge.kummerClass F p hp ((π ^ k) ^ p) = 0 := by
      rw [KummerBridge.kummerClass_eq_zero_iff]
      exact ⟨π ^ k, rfl⟩
    have hk_eq : KummerBridge.kummerClass F p hp a
        = KummerBridge.kummerClass F p hp (a * (π ^ (-k)) ^ p) := by
      conv_lhs => rw [hfactor]
      rw [KummerV.kummerClass_mul, hzero, add_zero]
    have hvu : v (a * (π ^ (-k)) ^ p) = 1 := by
      have h2 : Multiplicative.toAdd (v ((π ^ (-k)) ^ p))
          = (p : ℤ) * ((-k) * Multiplicative.toAdd (v π)) := by
        rw [map_pow, toAdd_pow', map_zpow, toAdd_zpow, zsmul_eq_mul]
        push_cast
        ring
      have hval : Multiplicative.toAdd (v (a * (π ^ (-k)) ^ p)) = 0 := by
        rw [map_mul, toAdd_mul', h2, hπ, hk]
        simp
      exact Multiplicative.toAdd.injective (by simpa using hval)
    refine ⟨a * (π ^ (-k)) ^ p, mem_unitFiltration_zero_of_val_eq_one hv hvu, ?_⟩
    rw [← ha]
    exact hk_eq.symm
  · rintro ⟨u, hu, huy⟩
    rw [← huy, valLinOf_kummerClass]
    have hvu : v u = 1 := val_eq_one_of_mem_unitFiltration_zero hv hu
    unfold valOfUnitOf
    rw [hvu, toAdd_one, Int.cast_zero]

/-- ★★★★★ **`ker v̄ = ker res₁`（`ValCompat` 版）**。 -/
theorem valLinOf_eq_zero_iff_res1V_eq_zero_of_valCompat
    (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    (v : Fˣ →* Multiplicative ℤ) (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (y : GaloBase.V F p) :
    valLinOf (F := F) (p := p) v hp y = 0 ↔ res1V (F := F) (p := p) y = 0 := by
  rw [valLinOf_eq_zero_iff_exists_unit_of_valCompat (p := p) hp v hv hπ,
    res1V_eq_zero_iff_exists_unit (p := p) hp hpq]

/-- ★★★★★★ **`Hyp744.UnramifiedKummer` 是定理**（`I = inertiaLoc F`，`v` 满足 `ValCompat` ＋ `v π = 1`）。

这是论文 `prop:prelim-kummer-valuation`(2) 的「`ker v̄ ⊆ range infl`」一半，
**不再有任何具名假设**。 -/
theorem unramifiedKummer (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    (v : Fˣ →* Multiplicative ℤ) (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    UnramifiedKummer (F := F) p (inertiaLoc F) (v := v) hp := by
  intro y
  have hres : res1V (F := F) (p := p) (y : GaloBase.V F p) = 0 :=
    (valLinOf_eq_zero_iff_res1V_eq_zero_of_valCompat (p := p) hp hpq v hv hπ
      (y : GaloBase.V F p)).mp y.2
  rw [res1V_apply, ← AddMonoidHom.mem_ker, ← explicitInfRes_exact,
    AddMonoidHom.mem_range] at hres
  obtain ⟨w, hw⟩ := hres
  refine ⟨eQ (F := F) (p := p) (inertiaLoc F)
    (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
      (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
      (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ inertiaLoc F))
      (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
      continuous_of_discreteTopology
      (coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F)) w), ?_⟩
  rw [infl1Res_eQ, ← explicitInfl1_eq_comp_coeff (p := p) (I := inertiaLoc F) w, hw,
    AddEquiv.apply_symm_apply]

end ValCompatKummer

end L20261018

#print axioms L20261018.valLinOf_eq_zero_iff_exists_unit_of_valCompat
#print axioms L20261018.valLinOf_eq_zero_iff_res1V_eq_zero_of_valCompat
#print axioms L20261018.unramifiedKummer
