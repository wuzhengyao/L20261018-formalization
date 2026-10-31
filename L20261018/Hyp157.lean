import Hyp156

/-!
# R1005：**单载体化**（论文层级，类无关）—— 4.3(2) 搬到显式载体，与 4.3(1) 合成论文的 `thm:ramified`

论文的 `thm:ramified` 是**单一 `V = H^1(F,\mu_p)`** 上的 (1)(2)；
本战役的 (1) 与 (2) 此前分居两载体（(1) 显式 `H1`、(2) `GaloBase.V`）。

**本轮**：把 `Hyp147` 的交换方块／值域搬运**类无关化**（用 `Hyp156` 的 `cup_compat_theta_free`、
`theta1_free_kummerClass`），于是 `rank Φ` 两载体相等，4.3(2) 的 `3 ≤ rank Φ` 可写成**显式载体**版；
再与 4.3(1) 合成**同一载体上的** `thm:ramified`。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-! ## 1. 显式非零杯积 ⟹ `GaloBase` 非零杯积（类无关） -/

theorem cup_kummerClass_ne_zero_free (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0 := by
  intro h0
  apply hne
  have h := cup_compat_theta_free (F := F) (p := p)
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2)
  rw [h0, map_zero, theta1_free_kummerClass, theta1_free_kummerClass] at h
  exact h.symm

/-! ## 2. 交换方块与值域搬运（类无关） -/

/-- 点态交换方块：`(Θ₂×Θ₂)(Φ_Galo w) = Φ_exp (Θ₁ w)`。 -/
theorem Bex_Phi_theta_free (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (w : GaloBase.V F p) :
    ((theta2_free (F := F) p).prodCongr (theta2_free (F := F) p))
        ((biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero_free (F := F) (p := p) hp hne)).Phi w)
      = (Theo352.Bex (F := F) (p := p) hp hne).Phi (theta1_free (F := F) p w) := by
  refine Prod.ext ?_ ?_
  · show theta2_free (F := F) p
        (GaloBase.cup (K := F) (p := p) w (KummerBridge.kummerClass F p hp a1))
      = Theo352.cupLin (F := F) (p := p) (theta1_free (F := F) p w)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
    rw [cup_compat_theta_free, theta1_free_kummerClass]
  · show theta2_free (F := F) p
        (GaloBase.cup (K := F) (p := p) w (KummerBridge.kummerClass F p hp a2))
      = Theo352.cupLin (F := F) (p := p) (theta1_free (F := F) p w)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2)
    rw [cup_compat_theta_free, theta1_free_kummerClass]

/-- 线性映射等式（交换方块）。 -/
theorem phi_comp_free (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    (((theta2_free (F := F) p).prodCongr (theta2_free (F := F) p)).toLinearMap).comp
        (biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero_free (F := F) (p := p) hp hne)).Phi
      = (Theo352.Bex (F := F) (p := p) hp hne).Phi.comp
          (theta1_free (F := F) p).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  exact Bex_Phi_theta_free (F := F) (p := p) hp hne w

/-- **值域搬运**：`(Θ₂×Θ₂)(range Φ_Galo) = range Φ_exp`。 -/
theorem phi_range_map_free (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    Submodule.map ((theta2_free (F := F) p).prodCongr (theta2_free (F := F) p)).toLinearMap
        (biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero_free (F := F) (p := p) hp hne)).Phi.range
      = (Theo352.Bex (F := F) (p := p) hp hne).Phi.range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy⟩ := (LinearMap.mem_range
      (f := (biKummerDataKummer F p hp a1 a2
        (cup_kummerClass_ne_zero_free (F := F) (p := p) hp hne)).Phi)).mp hw
    refine LinearMap.mem_range.mpr ⟨theta1_free (F := F) p y, ?_⟩
    rw [← hy]
    exact (Bex_Phi_theta_free (F := F) (p := p) hp hne y).symm
  · rintro _ ⟨v, rfl⟩
    refine Submodule.mem_map.mpr ⟨(biKummerDataKummer F p hp a1 a2
      (cup_kummerClass_ne_zero_free (F := F) (p := p) hp hne)).Phi
        ((theta1_free (F := F) p).symm v), LinearMap.mem_range_self _ _, ?_⟩
    exact (Bex_Phi_theta_free (F := F) (p := p) hp hne ((theta1_free (F := F) p).symm v)).trans
      (by rw [LinearEquiv.apply_symm_apply])

/-- **`Module.rank` 搬运**：两载体 `Φ` 值域同秩。 -/
theorem rank_range_eq_free (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    Module.rank (ZMod p)
        ↥(biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero_free (F := F) (p := p) hp hne)).Phi.range
      = Module.rank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range := by
  rw [← phi_range_map_free (F := F) (p := p) hp hne]
  exact LinearEquiv.rank_eq
    (((theta2_free (F := F) p).prodCongr (theta2_free (F := F) p)).submoduleMap _)

/-! ## 3. **4.3(2) 的显式载体版** ＋ **单载体 `thm:ramified`** -/

-- @source file=raw/L20261018.tex locator=line:1637 quote="共同杯积映射满足 $\rank(\Phi)\ge3$。"
/-- **4.3(2)（显式载体，类无关）**：`3 ≤ rank(Φ)`，`Φ = Φ_{Bex}`。 -/
theorem thm_ramified_2_explicit (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2) :
    (3 : Cardinal) ≤ Module.rank (ZMod p)
      ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range := by
  have h3 := thm_ramified_2 (F := F) (p := p) hp hp2
    (cup_kummerClass_ne_zero_free (F := F) (p := p) hp hne) b1 b2 hD
  rwa [rank_range_eq_free (F := F) (p := p) hp hne] at h3

-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
/-- **单载体 `thm:ramified`（论文层级）**：`(1)` 与 `(2)` 在**同一载体**（显式 `H1`）上一次陈述。 -/
theorem thm_ramified_combined {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p)))
    (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      D.val u ≠ 0)
    (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ ∧
      (3 : Cardinal) ≤ Module.rank (ZMod p)
        ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range := by
  obtain ⟨h1, h2⟩ := thm_ramified_1_of_D_free (F := F) (p := p) D hp hp2 Δ hroots hU
    ha1 ha2 hne hval
  exact ⟨h1, h2, thm_ramified_2_explicit (F := F) (p := p) hp hp2 hne b1 b2 hD⟩

end L20261018
#print axioms L20261018.cup_kummerClass_ne_zero_free
#print axioms L20261018.Bex_Phi_theta_free
#print axioms L20261018.phi_range_map_free
#print axioms L20261018.rank_range_eq_free
#print axioms L20261018.thm_ramified_2_explicit
#print axioms L20261018.thm_ramified_combined
