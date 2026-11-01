import L20261018.Ch2.Kummer.Step023_cup_compatible_mu_p

/-!
# R989：**桥的 `≃ₗ` 升级完成（选 (乙) 路）＋ T4 去 `D`**

## 判别结果（提示词 ④ 要求的第一动作）

`Check950`／`Check951`／`Check952` 三个探针实测：

| 判别项 | 结果 |
|---|---|
| `#synth Module (ZMod p) (H1 (AbsGal F) (ZMod p))` | ✓ `Theo352.instModuleZModH1` |
| `#synth Module (ZMod p) (GaloBase.V F p)` | ✓ `(continuousCohomology 1 (muP F p)).isModule` |
| `AddMonoidHom.toZModLinearMap` 存在 | ✓ `Mathlib/Algebra/Module/ZMod.lean:81` |
| `e : M ≃+ M₁` 的 `ZMod`-线性 | ✓ **一行** `fun c x => ZMod.map_smul _ c x`（`ZMod.map_smul`，`:68`） |
| `AddEquiv.toZModLinearEquiv` | ✗ 不存在（`AddEquiv.toLinearEquiv` 才是入口） |
| `NeZero p` 由 `Fact p.Prime` | ✓ 自动实例 |

**⟹ R987 的根因假设被证伪**：`H1` 的 `ZMod p`-`smul` **恰恰由 `ZMod.map_smul` 处理**
（`ZMod.map_smul` 只用到 `ZMod.intCast_zmod_cast` ＋ `map_intCast_smul`，**对任意**
`Module (ZMod n)` 实例都成立，故"`smul` 来源不同"不构成障碍）。
**⟹ 走 (乙)：直接把 `h1ToVEquiv`／`EH2OfDiscrete` 升级成 `≃ₗ`，`Hyp141` 不动。**

## 本文件产出

1. `theta1 : GaloBase.V F p ≃ₗ[ZMod p] H¹_abs(ZMod p)`（`h1ToVEquiv.symm` 的线性版）
2. `theta2 : GaloBase.H2 F p ≃ₗ[ZMod p] H²_abs(ZMod p)`（`EH2OfDiscrete.symm` 的线性版）
3. `cup_compat_muP_zmod`：`Hyp143` 的 `ZMod p` 口径重述（`rw [cupLin_apply]` ＋ `exact`）
4. **`cup_compat_theta`（`hcup`）**：`theta2 (cup x y) = cupLin (theta1 x) (theta1 y)`
5. **`henselResidueData_explicit`**：`HenselResidueData` 的**显式载体实例**（`def` 形态，体可见）
6. **`thm_ramified_1_uncond`：T4(1) 去 `D`**（条件只剩 `hpu`（论文 `char K ≠ p`）与 `p ≠ 2`）

`π`／`hπ` 不再作为假设出现：由 `TauCeti.exists_isUniformizer`（`LocalField/Uniformizer.lean:88`）
在证明内 `obtain`（论文"取 `v(π)=1`"是**取值**，不是假设）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-! ## 1. 两个载体等价的 `ZMod p`-线性升级 -/

/-- **`Θ₁`**：`h1ToVEquiv` 的逆（`GaloBase.V → 显式 H¹`），升级为 `≃ₗ`。

线性由 `ZMod.map_smul` 一行给出（R987 曾判此路不通，实为 `#synth` 未做）。 -/
noncomputable def theta1 :
    GaloBase.V F p ≃ₗ[ZMod p] H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p) :=
  (KummerBridge.h1ToVEquiv F p).symm.toLinearEquiv (fun c x => ZMod.map_smul _ c x)

/-- **`Θ₂`**：`EH2OfDiscrete` 的逆（`GaloBase.H2 → 显式 H²`），升级为 `≃ₗ`。 -/
noncomputable def theta2 :
    GaloBase.H2 F p ≃ₗ[ZMod p] H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p) :=
  ((GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete).symm.toLinearEquiv
    (fun c x => ZMod.map_smul _ c x)

@[simp] theorem theta1_apply (x : GaloBase.V F p) :
    theta1 (F := F) p x = (KummerBridge.h1ToVEquiv F p).symm x := rfl

@[simp] theorem theta2_apply (y : GaloBase.H2 F p) :
    theta2 (F := F) p y
      = ((GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete).symm y := rfl

/-! ## 2. 杯积相容（`Hyp141` 的 `hcup`） -/

/-- **`Hyp143` 的 `cupLin` 口径直证**（**不是**由 `Hyp143` 改写，而是同一泛型引理以
另一组实例参数重新实例化）。

**为什么不能从 `Hyp143` 改写**（L49 记法层，本阶段实踩）：`Hyp143` 的 `explicitCup11`
是 `muP.V` 口径（实例参数由 `TopRep.distribMulAction` 供给），`cupLin` 是 `ZMod p` 口径
（实例参数自动合成）；两者作为 `H2` **类型是同一个**（`rfl` 实测），但 `explicitCup11` 的
**证明参数**（`Continuous`／等变性的证明项）不同 ⟹ `rw` 与 `AddEquiv.symm_apply_apply`
在 `implicit` 透明度下匹配不上（报 `Did not find an occurrence of the pattern`）。
**修法 = 直接以 `ZMod p` 口径重证**（同一 `TopPairing.cup_one_one_…` 泛型引理）。 -/
theorem cup_compat_muP_zmod (x y : H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :
    GaloBase.cup (K := F) (p := p)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete x)
        ((GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete y)
      = (GaloBase.muP F p).explicitH2AddEquivContinuousCohomologyOfDiscrete
          (Theo352.cupLin (F := F) (p := p) x y) := by
  rw [Theo352.cupLin_apply]
  exact TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete
    (GaloBase.muPairing F p) (GaloCup.zmodMulPairing p)
    (zmodMulPairing_eq_muPairing (F := F) (p := p)) x y

/-- **杯积相容**：`Θ₂ (x ∪ y) = Θ₁x ∪' Θ₁y`（`∪ = GaloBase.cup`、`∪' = cupLin`）。

由 `Hyp143`（`muP` 口径）＋ `Hyp128`（`h1ToVEquiv` 与 `EH1OfDiscrete` 逐点一致）直接得。 -/
theorem cup_compat_theta (x y : GaloBase.V F p) :
    theta2 (F := F) p (GaloBase.cup (K := F) (p := p) x y)
      = Theo352.cupLin (F := F) (p := p)
          (theta1 (F := F) p x) (theta1 (F := F) p y) := by
  have hx : (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
      (theta1 (F := F) p x) = x := by
    rw [← h1ToVEquiv_apply_eq_muP, theta1_apply, AddEquiv.apply_symm_apply]
  have hy : (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
      (theta1 (F := F) p y) = y := by
    rw [← h1ToVEquiv_apply_eq_muP, theta1_apply, AddEquiv.apply_symm_apply]
  have h := cup_compat_muP_zmod (F := F) (p := p) (theta1 (F := F) p x) (theta1 (F := F) p y)
  rw [hx, hy] at h
  rw [theta2_apply, h]
  exact AddEquiv.symm_apply_apply _ _

/-! ## 3. 显式载体上的 `HenselResidueData`（`def` 形态，体可见） -/

/-- **`HenselResidueData` 的显式载体实例**。

`V = H¹_abs`、`H²= H²_abs`、`VK = ker \bar v`（与 `GaloBase` 侧同一 `VK`，`Θv = id`），
由 `Hyp139.henselResidueDataOfCup` 沿 `(Θ₁, Θ₂, id)` 搬运（`Hyp141`），唯一前提 `hcup` 已落。

**`D.val` 定义等于 `valLin ∘ h1ToVEquiv`**（`def` 体可见 ⟹ 下游 `hval` 可直接换口径）。 -/
noncomputable def henselResidueData_explicit (hp : IsUnit (p : F))
    (hp2 : NeZero (2 : ZMod p)) (hpu : IsUnit (p : 𝒪[F]))
    {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    HenselResidueData (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))
      (H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) ↥(LinearMap.ker (valLin F p hp))
      (Theo352.cupLin (F := F) (p := p)) :=
  -- 返回 Type 的 `def` **不能** `obtain` 拆 `∃`（`propRecLargeElim`）⟹ `Classical.choose`
  let π := Classical.choose (TauCeti.exists_isUniformizer F)
  henselResidueDataTransport (theta1 (F := F) p) (theta2 (F := F) p)
    (LinearEquiv.refl (ZMod p) ↥(LinearMap.ker (valLin F p hp)))
    (cup_compat_theta (F := F) (p := p))
    (henselResidueDataOfCup (F := F) (p := p) hp hp2
      (hπ := (TauCeti.isUniformizer_def (K := F) π).1
        (Classical.choose_spec (TauCeti.exists_isUniformizer F)))
      hpu hne)

/-- `D_expl.val = valLin ∘ h1ToVEquiv`（`def` 体可见性的显式记录，供下游换口径）。 -/
theorem henselResidueData_explicit_val (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (u : H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :
    (henselResidueData_explicit (F := F) (p := p) hp hp2 hpu hne).val u
      = valLin F p hp (KummerBridge.h1ToVEquiv F p u) := rfl

/-! ## 4. 桥第一段的显式形态（Kummer 类在 `Θ₁` 下的像） -/

/-- `Θ₁ (kummerClass a) = kummerExplicit a`（`Hyp140` 的 `Θ₁` 口径）。 -/
theorem theta1_kummerClass (hp : IsUnit (p : F)) (a : Fˣ) :
    theta1 (F := F) p (KummerBridge.kummerClass F p hp a)
      = GaloCup.kummerExplicit (F := F) (p := p) hp a := by
  rw [theta1_apply, AddEquiv.symm_apply_eq]
  exact (kummerClass_eq_h1ToVEquiv_kummerExplicit (F := F) (p := p) hp a).symm

/-- **`hne` 从显式载体制搬到 `GaloBase` 载体**（沿 `Θ₂` 单射）：
由 `hcup` ＋ `theta1_kummerClass`，显式层的非零杯积即 `GaloBase` 层的非零杯积。 -/
theorem cup_kummerClass_ne_zero (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F) (p := p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0 := by
  intro hzero
  apply hne
  have h := cup_compat_theta (F := F) (p := p)
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2)
  rw [hzero, map_zero, theta1_kummerClass, theta1_kummerClass] at h
  exact h.symm

/-! ## 5. **T4(1) 去 `D`** -/

section Part1

open TauCeti

/-- **`thm:ramified`(1)：`U^⊥ = N = 0`（无 `HenselResidueData`）**。

论文假设只剩：`p` 奇素（`[Fact p.Prime]` ＋ `hp2 : p ≠ 2`）、`F` 为 `char 0` 的
Hensel 离散赋值域（`IsNonarchimedeanLocalField`）、`μ_p ⊂ F`、
`(a₁)∪(a₂) ≠ 0`（`hne`）、`v|_U ≠ 0`（`hval`）、`char K ≠ p`（`hpu`）。
结论：`U^⊥ = N = 0`。

`π` 由 `TauCeti.exists_isUniformizer` 在证明内取；`D` 由 `henselResidueData_explicit` 构造。 -/
-- @source file=raw/L20261018.tex locator=label:thm:ramified quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$"
theorem thm_ramified_1_uncond (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (Δ : Subgroup Fˣ)
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
    (hpu : IsUnit (p : 𝒪[F]))
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLin F p hp (KummerBridge.h1ToVEquiv F p u) ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  have hne_galo := cup_kummerClass_ne_zero (F := F) (p := p) hp hne
  have hU0 : (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ :=
    ramified_vanishing_explicit (F := F) (p := p) hp hp2 _
      (henselResidueData_explicit (F := F) (p := p) hp
        (Assemble36.neZero_two_zmod (p := p) hp2) hpu hne_galo) a1 a2 hne hval
  refine ⟨hU0, ?_⟩
  have hle := Assemble36.Nsub_le_Uperp (F := F) (p := p) hp hp2 Δ hroots hU ha1 ha2 hne
  rw [hU0] at hle
  exact eq_bot_iff.mpr hle

end Part1

end L20261018
#print axioms L20261018.cup_compat_muP_zmod
#print axioms L20261018.cup_compat_theta
#print axioms L20261018.henselResidueData_explicit
#print axioms L20261018.theta1_kummerClass
#print axioms L20261018.cup_kummerClass_ne_zero
#print axioms L20261018.thm_ramified_1_uncond
