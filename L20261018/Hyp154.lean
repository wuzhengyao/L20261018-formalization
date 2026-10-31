import Hyp153
import Hyp101

/-!
# R1002：**4.3(1) 只依赖 §2.4** —— `U^⊥ = N = 0`（`D` 作输入，不依赖完备构造）

R1001 把 4.2 降到论文假设层级（`Hyp153.orth_eq_bot_paper_route_hensel`，`D` 作输入）。
本轮做 **4.3(1)**：`Hyp101.Nsub_le_Uperp`（实测类无关）＋ 4.2 的论文层级版，
沿载体等价 `Θ₁` 把 `U^⊥` 搬到显式载体，得到 `U^⊥ = N = 0`。

**依赖结构（本轮的重点）**：本定理的 `D` 是**输入**（= 论文 §2.4 两条命题），
**不用**本战役完备情形的构造（`Hyp139`）—— 故 4.3(1) 与 4.2 一样，只依赖 §2.4。

**诚实的层级说明**：`kummerClass`（把 `a ∈ Fˣ` 送到 `(a) ∈ H¹`）走的是 TauCeti 的
`kummerMap`，而本战役的桥 `KummerBridge.kummerClass` 目前只在局部域上下文可用 ⟹
本文件的**载体/Kummer 类层**仍需 `IsNonarchimedeanLocalField`（**库层限制，非数学需要**）。
数学上 Kummer 理论只需 `μ_p ⊂ F`；把该层类无关化是下一轮候选。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

/-! ## 1. `orth` 的成员刻画（类无关） -/

theorem mem_orth_iff {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {H2 : Type*} [AddCommGroup H2] [Module k H2]
    (cup : V →ₗ[k] V →ₗ[k] H2) (a1 a2 z : V) :
    z ∈ ResidueCupData.orth cup a1 a2 ↔ cup z a1 = 0 ∧ cup z a2 = 0 := by
  rw [ResidueCupData.orth, LinearMap.mem_ker, ResidueCupData.commonCupMap_apply,
    Prod.mk_eq_zero]

/-! ## 2. `U^⊥` 沿 `Θ₁` 的搬运（用 `Hyp145` 的 `Θ₁／Θ₂`） -/

section Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- **`U^⊥` 的载体搬运**：`orth_exp = Θ₁(orth_galo)`。 -/
theorem orth_map_eq (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    ResidueCupData.orth (Theo352.cupLin (F := F) (p := p))
        (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
        (GaloCup.kummerExplicit (F := F) (p := p) hp a2)
      = Submodule.map (theta1 (F := F) p).toLinearMap
          (ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
            (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2)) := by
  have key : ∀ (w : GaloBase.V F p) (a : Fˣ),
      theta2 (F := F) p (GaloBase.cup (K := F) (p := p) w
          (KummerBridge.kummerClass F p hp a))
        = Theo352.cupLin (F := F) (p := p) (theta1 (F := F) p w)
            (GaloCup.kummerExplicit (F := F) (p := p) hp a) := by
    intro w a
    rw [cup_compat_theta, theta1_kummerClass]
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨h1, h2⟩ := (mem_orth_iff (Theo352.cupLin (F := F) (p := p))
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) z).mp hz
    refine Submodule.mem_map.mpr ⟨(theta1 (F := F) p).symm z, ?_, ?_⟩
    · rw [mem_orth_iff]
      constructor
      · refine (theta2 (F := F) p).injective ?_
        rw [key, LinearEquiv.apply_symm_apply, h1, map_zero]
      · refine (theta2 (F := F) p).injective ?_
        rw [key, LinearEquiv.apply_symm_apply, h2, map_zero]
    · exact LinearEquiv.apply_symm_apply _ z
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_orth_iff (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) w).mp hw
    exact (mem_orth_iff (Theo352.cupLin (F := F) (p := p))
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2)
      (theta1 (F := F) p w)).mpr
      ⟨by rw [← key, h1, map_zero], by rw [← key, h2, map_zero]⟩

end Transport

/-! ## 3. **4.3(1)**：`U^⊥ = N = 0`，`D` 作输入（只依赖 §2.4） -/

section Part1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
/-- **`thm:ramified`(1)（4.3(1)）**：`U^⊥ = N = 0`，**`D`（= 论文 §2.4）是输入**，
不用本战役完备情形的构造 ⟹ 只依赖 §2.4。 -/
theorem thm_ramified_1_of_D {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
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
  -- `GaloBase` 层的非零杯积：由 `hne` 经 `Θ₂` 单射搬过去
  have hneG : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0 := by
    intro h0
    apply hne
    have h := cup_compat_theta (F := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2)
    rw [h0, map_zero, theta1_kummerClass, theta1_kummerClass] at h
    exact h.symm
  -- 4.2（论文层级，`D` 作输入）
  have hU0G : ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ :=
    orth_eq_bot_paper_route_hensel (F := F) (p := p) D hp2' hneG hval
  -- 搬到显式载体
  have hU0 : (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ := by
    rw [show (Theo352.Bex (F := F) (p := p) hp hne).Uperp
        = ResidueCupData.orth (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2) from rfl,
      orth_map_eq (F := F) (p := p) hp hne, hU0G, Submodule.map_bot]
  refine ⟨hU0, ?_⟩
  have hle := Assemble36.Nsub_le_Uperp (F := F) (p := p) hp hp2 Δ hroots hU ha1 ha2 hne
  rw [hU0] at hle
  exact eq_bot_iff.mpr hle

end Part1

end L20261018
#print axioms L20261018.mem_orth_iff
#print axioms L20261018.orth_map_eq
#print axioms L20261018.thm_ramified_1_of_D
