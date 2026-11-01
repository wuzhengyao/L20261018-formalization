import L20261018.Ch2.Hensel.Inertia.Step034_inertia_restriction_res1
import L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness
import L20261018.Ch2.Hensel.Inertia.Step016_inertia_loc_carrier_alignment

/-!
# S68 R2：**`ker v̄ = ker res₁`** —— `UnramifiedKummer` 的代数心

## 本件做什么

`S68-HYP744-PLAN.md` 的 G1＋G2。把 `Hyp746.res1V`（惯性限制）与 `Hyp162.valLinOf`（`v̄ = v mod p`）
的**零点集**都算成同一个东西：

> **`res₁ y = 0` ⟺ `v̄ y = 0` ⟺ `y` 是某个单位 `u ∈ unitFiltration F 0` 的 Kummer 类**

* `res₁` 侧：`TauCeti.explicitRes1_eq_zero_iff_exists_kummerMap`
  （「惯性上消失 ⟺ 单位类」，`NumberTheory/LocalField/Unramified/Kummer.lean`）
  经 `Hyp746.explicitRes1_explicitCoeff1Equiv_comp`（系数等价与限制交换）
  与 `Hyp511.map_inertiaSubgroup_eq_inertiaLoc`（战役惯性 ＝ TauCeti 惯性）搬到战役载体；
* `v̄` 侧：`Hyp162.valLinOf_kummerClass`（`v̄((a)) = v(a) mod p`）＋ 一致化元分解
  `TauCeti.mul_zpow_neg_mem_unitFiltration_zero`。

## 诚实边界（写死）

本件把 `v` 取成 **`TauCeti.normalizedValuation F`**（`hv`）。这是**归约而非损失**：
`Hyp187.ValCompat v` ＋ `v π = 1` 就刻画 `v = normalizedValuation F`（同一赋值环、同一归一化），
该归约的机检是**下一件**（`Hyp748`）。**不用** `v = nv` 之外的东西 —— 本件不碰 `ValCompat`。

## 交付

| 声明 | 内容 |
|---|---|
| `explicitRes1_inertiaLoc_eq_zero_iff` | TauCeti「惯性上消失 ⟺ 单位类」在 `inertiaLoc` 上的形态 |
| `explicitRes1_inertiaLoc_kummerMap_eq_zero_iff` | 同上，`p ∣ nv(a)` 形态 |
| `kummerCoeffInertiaEquiv` | `KummerCoeff → ZMod p` 系数比较搬到惯性层（加法等价） |
| `res1V_kummerClass_eq_zero_iff` | ★★★★ `res₁((a)) = 0 ⟺ p ∣ nv(a)` |
| **`res1V_eq_zero_iff_exists_unit`** | ★★★★★ `res₁ y = 0 ⟺ ∃ u ∈ unitFiltration F 0, (u) = y` |
| **`valLinOf_eq_zero_iff_exists_unit`** | ★★★★★ `v̄ y = 0 ⟺ ∃ u ∈ unitFiltration F 0, (u) = y` |
| **`valLinOf_eq_zero_iff_res1V_eq_zero`** | ★★★★★ `ker v̄ = ker res₁`（逐点等价） |
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

namespace L20261018

section Kernel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ## 1 TauCeti 的不分歧 Kummer 定理，搬到 `inertiaLoc` -/

/-- ★★★★ **「惯性上消失 ⟺ 单位类」在战役惯性 `inertiaLoc F` 上的形态**
（TauCeti 的定理是对 `(inertiaSubgroup F).map (absoluteGaloisGroupRestrictEquiv F)` 陈述的，
`Hyp511.map_inertiaSubgroup_eq_inertiaLoc` 把两者认成同一个子群）。 -/
theorem explicitRes1_inertiaLoc_eq_zero_iff (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) (c : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p)) :
    explicitRes1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (inertiaLoc F) c = 0
      ↔ ∃ u ∈ unitFiltration F 0, (kummerMap F p hp u).toAdd = c := by
  rw [← map_inertiaSubgroup_eq_inertiaLoc (F := F)]
  exact explicitRes1_eq_zero_iff_exists_kummerMap (K := F) (n := p) hp hpq c

/-- ★★★★ 上条的 `p ∣ v(a)` 形态（TauCeti `explicitRes1_kummerMap_eq_zero_iff`）。 -/
theorem explicitRes1_inertiaLoc_kummerMap_eq_zero_iff (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) (a : Fˣ) :
    explicitRes1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (inertiaLoc F)
        (kummerMap F p hp a).toAdd = 0
      ↔ (p : ℤ) ∣ (normalizedValuation F a).toAdd := by
  rw [← map_inertiaSubgroup_eq_inertiaLoc (F := F)]
  exact explicitRes1_kummerMap_eq_zero_iff F hp hpq a

/-- `KummerCoeff F p → ZMod p` 的系数比较，拉到惯性 `↥(inertiaLoc F)` 上
（`TauCeti.kummerCoeffLinearEquiv` ＋ `explicitCoeff1Equiv`；`μ_p ⊂ F` 使 `G_F`-作用平凡）。 -/
noncomputable def kummerCoeffInertiaEquiv (hp : IsUnit (p : F)) :
    H1 ↥(inertiaLoc F) (KummerCoeff F p) ≃+ H1 ↥(inertiaLoc F) (ZMod p) :=
  explicitCoeff1Equiv ↥(inertiaLoc F) (KummerCoeff F p)
    (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun s m => by
      show (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv
          ((s : AbsoluteGaloisGroup F) • m)
        = (s : AbsoluteGaloisGroup F) •
            (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv m
      rw [smul_kummerCoeff_eq_self (KummerBridge.primitiveRoot_spec F p)
        (s : AbsoluteGaloisGroup F) m]
      rfl)

/-- `kummerCoeffInertiaEquiv` 就是 `explicitCoeff1Equiv`（定义式）。 -/
theorem kummerCoeffInertiaEquiv_apply (hp : IsUnit (p : F))
    (x : H1 ↥(inertiaLoc F) (KummerCoeff F p)) :
    kummerCoeffInertiaEquiv (F := F) (p := p) hp x
      = explicitCoeff1Equiv ↥(inertiaLoc F) (KummerCoeff F p)
          (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv
          continuous_of_discreteTopology continuous_of_discreteTopology
          (fun s m => by
            show (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv
                ((s : AbsoluteGaloisGroup F) • m)
              = (s : AbsoluteGaloisGroup F) •
                  (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv m
            rw [smul_kummerCoeff_eq_self (KummerBridge.primitiveRoot_spec F p)
              (s : AbsoluteGaloisGroup F) m]
            rfl) x :=
  rfl

/-! ## 2 `res₁` 的零点集 -/

/-- ★★★★ **`res₁((a)) = 0 ⟺ p ∣ v(a)`**（`Hyp746.res1V_kummerClass_eq` ＋ 系数交换律 ＋ TauCeti）。 -/
theorem res1V_kummerClass_eq_zero_iff (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) (a : Fˣ) :
    res1V (F := F) (p := p) (KummerBridge.kummerClass F p hp a) = 0
      ↔ (p : ℤ) ∣ (normalizedValuation F a).toAdd := by
  have h1 : res1V (F := F) (p := p) (KummerBridge.kummerClass F p hp a)
      = kummerCoeffInertiaEquiv (F := F) (p := p) hp
          (explicitRes1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (inertiaLoc F)
            (kummerMap F p hp a).toAdd) := by
    rw [res1V_kummerClass_eq]
    exact explicitRes1_explicitCoeff1Equiv_comp (inertiaLoc F)
      (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv
      continuous_of_discreteTopology continuous_of_discreteTopology _ _
  rw [h1, AddEquiv.map_eq_zero_iff,
    explicitRes1_inertiaLoc_kummerMap_eq_zero_iff (p := p) hp hpq]

/-- ★★★★★ **`res₁ y = 0 ⟺ y` 是某个单位的 Kummer 类**。 -/
theorem res1V_eq_zero_iff_exists_unit (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) (y : GaloBase.V F p) :
    res1V (F := F) (p := p) y = 0
      ↔ ∃ u ∈ unitFiltration F 0, KummerBridge.kummerClass F p hp u = y := by
  classical
  set c : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p) :=
    (KummerBridge.kummerH1Equiv (F := F) (p := p) hp).symm
      ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm y) with hc
  have hsymm : (KummerBridge.h1ToVEquiv (F := F) (p := p)).symm y
      = KummerBridge.kummerH1Equiv (F := F) (p := p) hp c := by
    rw [hc]; exact (AddEquiv.apply_symm_apply _ _).symm
  have h1 : res1V (F := F) (p := p) y
      = kummerCoeffInertiaEquiv (F := F) (p := p) hp
          (explicitRes1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (inertiaLoc F) c) := by
    rw [res1V_apply, hsymm]
    exact explicitRes1_explicitCoeff1Equiv_comp (inertiaLoc F)
      (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv
      continuous_of_discreteTopology continuous_of_discreteTopology _ _
  have hiff : res1V (F := F) (p := p) y = 0
      ↔ ∃ u ∈ unitFiltration F 0, (kummerMap F p hp u).toAdd = c := by
    rw [h1, AddEquiv.map_eq_zero_iff,
      explicitRes1_inertiaLoc_eq_zero_iff (p := p) hp hpq]
  rw [hiff]
  constructor
  · rintro ⟨u, hu, huc⟩
    refine ⟨u, hu, ?_⟩
    rw [KummerBridge.kummerClass, huc, ← hsymm, AddEquiv.apply_symm_apply]
  · rintro ⟨u, hu, huy⟩
    refine ⟨u, hu, ?_⟩
    have hA : KummerBridge.h1ToVEquiv (F := F) (p := p)
        (KummerBridge.kummerH1Equiv (F := F) (p := p) hp ((kummerMap F p hp u).toAdd)) = y := by
      rw [← huy, KummerBridge.kummerClass]
    have hB : KummerBridge.h1ToVEquiv (F := F) (p := p)
        (KummerBridge.kummerH1Equiv (F := F) (p := p) hp c) = y := by
      rw [← hsymm, AddEquiv.apply_symm_apply]
    exact (KummerBridge.kummerH1Equiv (F := F) (p := p) hp).injective
      ((KummerBridge.h1ToVEquiv (F := F) (p := p)).injective (hA.trans hB.symm))

/-! ## 3 `v̄` 的零点集 -/

/-- ★★★★★ **`v̄ y = 0 ⟺ y` 是某个单位的 Kummer 类**（`v = normalizedValuation F` 归约下）。

* `⟹`：`y = (a)`（满射）且 `p ∣ v(a)`，取 `u = a·π^{-v(a)}`（一致化元 `π`），
  则 `v(u) = 0` 故 `u` 是单位、且 `a = u·(π^k)^p` 故 Kummer 类不变；
* `⟸`：单位 `u` 有 `v(u) = 0`，故 `v̄((u)) = 0`。 -/
theorem valLinOf_eq_zero_iff_exists_unit (hp : IsUnit (p : F))
    (y : GaloBase.V F p) :
    valLinOf (F := F) (p := p) (normalizedValuation F) hp y = 0
      ↔ ∃ u ∈ unitFiltration F 0, KummerBridge.kummerClass F p hp u = y := by
  classical
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := KummerV.kummerClass_surjective (F := F) (p := p) hp y
    have hva : ((Multiplicative.toAdd (normalizedValuation F a) : ℤ) : ZMod p) = 0 := by
      have h0 : valLinOf (F := F) (p := p) (normalizedValuation F) hp
          (KummerBridge.kummerClass F p hp a) = 0 := by rw [ha]; exact hy
      rwa [valLinOf_kummerClass] at h0
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hva
    obtain ⟨π, hπu⟩ := exists_isUniformizer (K := F)
    have hπ : normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ) :=
      (isUniformizer_def π).1 hπu
    -- `u := a · (π^{-k})^p`：与 `a` 差一个 `p` 次幂，故 Kummer 类相同
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
    refine ⟨a * (π ^ (-k)) ^ p, ?_, ?_⟩
    · refine (mem_unitFiltration_zero (K := F) _).mpr ?_
      rw [← normalizedValuation_eq_one_iff]
      refine Multiplicative.toAdd.injective ?_
      rw [map_mul, toAdd_mul', map_pow, toAdd_pow',
        normalizedValuation_zpow_of_eq_ofAdd_one hπ, toAdd_ofAdd, hk, toAdd_one]
      push_cast
      ring
    · rw [← ha]
      exact hk_eq.symm
  · rintro ⟨u, hu, huy⟩
    rw [← huy, valLinOf_kummerClass]
    have hvu : normalizedValuation F u = 1 :=
      (normalizedValuation_eq_one_iff u).mpr ((mem_unitFiltration_zero (K := F) u).mp hu)
    unfold valOfUnitOf
    rw [hvu, toAdd_one, Int.cast_zero]

/-- ★★★★★ **`ker v̄ = ker res₁`（逐点形态）**：`v̄` 与惯性限制 `res₁` 有同一个零点集。

这就是 `UnramifiedKummer` 的**全部代数内容**：余下的只是
`ker res₁ = range infl₁`（膨胀-限制正合列）那一条载体搬运（见 `S68-HYP744-PLAN.md` G3）。 -/
theorem valLinOf_eq_zero_iff_res1V_eq_zero (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) (v : Fˣ →* Multiplicative ℤ)
    (hv : v = normalizedValuation F) (y : GaloBase.V F p) :
    valLinOf (F := F) (p := p) v hp y = 0 ↔ res1V (F := F) (p := p) y = 0 := by
  subst hv
  rw [valLinOf_eq_zero_iff_exists_unit (p := p) hp,
    res1V_eq_zero_iff_exists_unit (p := p) hp hpq]

end Kernel

end L20261018

#print axioms L20261018.explicitRes1_inertiaLoc_eq_zero_iff
#print axioms L20261018.explicitRes1_inertiaLoc_kummerMap_eq_zero_iff
#print axioms L20261018.kummerCoeffInertiaEquiv
#print axioms L20261018.kummerCoeffInertiaEquiv_apply
#print axioms L20261018.res1V_kummerClass_eq_zero_iff
#print axioms L20261018.res1V_eq_zero_iff_exists_unit
#print axioms L20261018.valLinOf_eq_zero_iff_exists_unit
#print axioms L20261018.valLinOf_eq_zero_iff_res1V_eq_zero
