import L20261018.Hyp155

/-!
# R1004：**4.3(1) 与 4.4 完全去类**（论文层级：只留 `[Field F] [Fact p.Prime] [μ_p ⊂ F]`）

R1004 前的状态：4.2 已类无关（`Hyp153`），但 4.3(1)／4.4 的**载体层**仍带
`IsNonarchimedeanLocalField`（因为它们用了本战役在局部域上下文中声明的辅助引理）。

**本轮判别（`Check971`／`Check972`）**：
* `KummerBridge.kummerClass` 的 `rfl` 展开**类无关**；
* `Hyp128.h1ToVEquiv_apply_eq_muP` 所在 section 实测**类无关**（`variable {F} [Field F] …`）；
* 真正的类来源 = **`Hyp142.zmodMulPairing_eq_muPairing`**（局部域上下文里的 `rfl` 引理）
  ⟹ 在类无关层重建它就够了。

**⟹ 本文件**：类无关的 `Θ₁／Θ₂` ＋ 杯积相容 ＋ `U^⊥` 搬运 ＋ **4.3(1)** ＋ **4.4**
（`D` 作输入；`hK1` 为论文假设）。于是**第四章的全部四条在 `[Field F]` 级别 + §2.4 成立**。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-! ## 1. 类无关的配对相容与 `Θ₁／Θ₂` -/

/-- `Hyp142` 的类无关版（原文即 `rfl`）。 -/
theorem zmodMulPairing_eq_muPairing_free (x y : ZMod p) :
    GaloCup.zmodMulPairing p x y = (GaloBase.muPairing F p).bil x y := rfl

/-- `Hyp143` 的类无关版（`cupLin` 口径直证）。 -/
theorem cup_compat_muP_zmod_free (x y : H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :
    GaloBase.cup (K := F) (p := p)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete x)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete y)
      = (GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete
          (Theo352.cupLin (F := F) (p := p) x y) := by
  rw [Theo352.cupLin_apply]
  exact TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete
    (GaloBase.muPairing F p) (GaloCup.zmodMulPairing p)
    (zmodMulPairing_eq_muPairing_free (F := F) (p := p)) x y

/-- **`Θ₁`**（类无关）：`h1ToVEquiv⁻¹` 升级为 `≃ₗ`。 -/
noncomputable def theta1_free :
    GaloBase.V F p ≃ₗ[ZMod p] H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p) :=
  (KummerBridge.h1ToVEquiv F p).symm.toLinearEquiv (fun c x => ZMod.map_smul _ c x)

/-- **`Θ₂`**（类无关）。 -/
noncomputable def theta2_free :
    GaloBase.H2 F p ≃ₗ[ZMod p] H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p) :=
  ((GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete).symm.toLinearEquiv
    (fun c x => ZMod.map_smul _ c x)

@[simp] theorem theta1_free_apply (x : GaloBase.V F p) :
    theta1_free (F := F) p x = (KummerBridge.h1ToVEquiv F p).symm x := rfl

@[simp] theorem theta2_free_apply (y : GaloBase.H2 F p) :
    theta2_free (F := F) p y
      = ((GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete).symm y := rfl

/-- `Θ₁(kummerClass a) = kummerExplicit a`（类无关，`rfl` 级）。 -/
theorem theta1_free_kummerClass (hp : IsUnit (p : F)) (a : Fˣ) :
    theta1_free (F := F) p (KummerBridge.kummerClass F p hp a)
      = GaloCup.kummerExplicit (F := F) (p := p) hp a := by
  rw [theta1_free_apply, KummerBridge.kummerClass, GaloCup.kummerExplicit,
    AddEquiv.symm_apply_apply]

/-- **杯积相容**（类无关）：`Θ₂ (x∪y) = Θ₁x ∪' Θ₁y`。 -/
theorem cup_compat_theta_free (x y : GaloBase.V F p) :
    theta2_free (F := F) p (GaloBase.cup (K := F) (p := p) x y)
      = Theo352.cupLin (F := F) (p := p)
          (theta1_free (F := F) p x) (theta1_free (F := F) p y) := by
  have hx : (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
      (theta1_free (F := F) p x) = x := by
    rw [← h1ToVEquiv_apply_eq_muP, theta1_free_apply, AddEquiv.apply_symm_apply]
  have hy : (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
      (theta1_free (F := F) p y) = y := by
    rw [← h1ToVEquiv_apply_eq_muP, theta1_free_apply, AddEquiv.apply_symm_apply]
  have h := cup_compat_muP_zmod_free (F := F) (p := p) (theta1_free (F := F) p x)
    (theta1_free (F := F) p y)
  rw [hx, hy] at h
  rw [theta2_free_apply, h]
  exact AddEquiv.symm_apply_apply _ _

/-! ## 2. `U^⊥` 的载体搬运（类无关） -/

/-- **`U^⊥` 的载体搬运**（类无关）：`orth_exp = Θ₁(orth_galo)`。 -/
theorem orth_map_eq_free (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    ResidueCupData.orth (Theo352.cupLin (F := F) (p := p))
        (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
        (GaloCup.kummerExplicit (F := F) (p := p) hp a2)
      = Submodule.map (theta1_free (F := F) p).toLinearMap
          (ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
            (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2)) := by
  have key : ∀ (w : GaloBase.V F p) (a : Fˣ),
      theta2_free (F := F) p (GaloBase.cup (K := F) (p := p) w
          (KummerBridge.kummerClass F p hp a))
        = Theo352.cupLin (F := F) (p := p) (theta1_free (F := F) p w)
            (GaloCup.kummerExplicit (F := F) (p := p) hp a) := by
    intro w a
    rw [cup_compat_theta_free, theta1_free_kummerClass]
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨h1, h2⟩ := (mem_orth_iff (Theo352.cupLin (F := F) (p := p))
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) z).mp hz
    refine Submodule.mem_map.mpr ⟨(theta1_free (F := F) p).symm z, ?_, ?_⟩
    · refine (mem_orth_iff (GaloBase.cup (K := F) (p := p))
        (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) _).mpr ⟨?_, ?_⟩
      · refine (theta2_free (F := F) p).injective ?_
        rw [key, LinearEquiv.apply_symm_apply, h1, map_zero]
      · refine (theta2_free (F := F) p).injective ?_
        rw [key, LinearEquiv.apply_symm_apply, h2, map_zero]
    · exact LinearEquiv.apply_symm_apply _ z
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_orth_iff (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) w).mp hw
    exact (mem_orth_iff (Theo352.cupLin (F := F) (p := p))
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) (theta1_free (F := F) p w)).mpr
      ⟨by rw [← key, h1, map_zero], by rw [← key, h2, map_zero]⟩

/-! ## 3. **4.3(1)** 类无关版（`D` 作输入） -/

/-- **4.3(1)（论文层级，类无关）**：`U^⊥ = N = 0`，`D`（= §2.4）作输入。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_of_D_free {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
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
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ := by
  classical
  have hp2' : NeZero (2 : ZMod p) := Assemble36.neZero_two_zmod (p := p) hp2
  have hneG : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0 := by
    intro h0
    apply hne
    have h := cup_compat_theta_free (F := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2)
    rw [h0, map_zero, theta1_free_kummerClass, theta1_free_kummerClass] at h
    exact h.symm
  have hU0G : ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ :=
    orth_eq_bot_paper_route_hensel (F := F) (p := p) D hp2' hneG hval
  have hU0 : (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ := by
    rw [show (Theo352.Bex (F := F) (p := p) hp hne).Uperp
        = ResidueCupData.orth (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2) from rfl,
      orth_map_eq_free (F := F) (p := p) hp hne, hU0G, Submodule.map_bot]
  refine ⟨hU0, ?_⟩
  have hle := Assemble36.Nsub_le_Uperp (F := F) (p := p) hp hp2 Δ hroots hU ha1 ha2 hne
  rw [hU0] at hle
  exact eq_bot_iff.mpr hle

/-! ## 4. **4.4** 类无关版（`D` 作输入；`hK1` 为论文假设） -/

/-- 把任意 `D` 搬到显式载体（类无关）。 -/
noncomputable def henselResidueData_explicit_of_D_free {VK : Type} [AddCommGroup VK]
    [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p))) :
    HenselResidueData (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))
      (H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) VK
      (Theo352.cupLin (F := F) (p := p)) :=
  henselResidueDataTransport (theta1_free (F := F) p) (theta2_free (F := F) p)
    (LinearEquiv.refl (ZMod p) VK) (cup_compat_theta_free (F := F) (p := p)) D

/-- **`d_F = d_K + 1`**（类无关，`D` 作输入）。 -/
theorem finrank_eq_finrank_add_one_of_D_free {VK : Type} [AddCommGroup VK]
    [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p)))
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] [NeZero (2 : ZMod p)] :
    Module.finrank (ZMod p) (GaloBase.V F p) = Module.finrank (ZMod p) VK + 1 :=
  ResidueCupData.finrank_eq_finrank_add_one
    (D.toResidueCupData (fun x y => GaloBase.cup_skew (K := F) (p := p) x y))

-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
/-- **4.4（论文层级，类无关）**：`d_K=1`（论文假设）⟹ `rank(Φ)=2 ∧ d_F=2`。 -/
theorem corollary_4_4_of_D_free {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p)))
    (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      D.val (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p) VK = 1)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    [NeZero (2 : ZMod p)] :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2)).range = 2
      ∧ Module.finrank (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 :=
  ResidueCupData.corollary_4_4
    ((henselResidueData_explicit_of_D_free (F := F) (p := p) D).toResidueCupData
      (fun x y => Theo352.cupLin_skew (F := F) (p := p) x y))
    (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
    (GaloCup.kummerExplicit (F := F) (p := p) hp a2) hne hval hK1

end L20261018
#print axioms L20261018.thm_ramified_1_of_D_free
#print axioms L20261018.finrank_eq_finrank_add_one_of_D_free
#print axioms L20261018.corollary_4_4_of_D_free
