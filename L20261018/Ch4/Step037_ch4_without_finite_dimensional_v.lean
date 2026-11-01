import L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface
import L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness
import L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free

/-!
# S39 第 3 轮：**4.2／4.3(1) 去掉 `[FiniteDimensional (ZMod p) (GaloBase.V F p)]` 绑定**

## 为什么这个绑定是「错位」而不是「必要」

论文 4.2（`raw/L20261018.tex:1602`）**不假设** `d_F = dim_{F_p}H¹(F,μ_p) < ∞`；
论文自己的例 `ex:explicit-ramified`（`:2790`）恰恰用**无限维**情形
（`:2825–2827` 逐字：「后者为无限维」）。故该绑定是**真实的收紧**，必须去掉。

**根因（本轮定位）**：`FiniteDimensional` 在证明里**只被用了一次** ——
`LinearMap.finrank_range_add_finrank_ker` 的**定义域**是
`↥(ResidueCupData.plane a1 a2)`（**二维平面 `U`**），不是整个 `V`。
而 `finrank ↥(plane) = 2` 是 `finrank_plane_eq_two_free`（**本来就无该绑定**）给的。
⟹ 把实例**限到平面**即可：`Module.finite_of_finrank_pos`。

## 机检件

| 件 | 内容 |
|---|---|
| **`finrank_ker_restrict_plane_eq_one_nofin`** | 平面上的 `\ker` 一维（**无** `FiniteDimensional V`） |
| **`orth_eq_bot_paper_route_hensel_nofin`** | **4.2**（`D` 层，论文原证明路线，**无** `FiniteDimensional V`） |
| **`thm_ramified_1_of_D_free_nofin`** | **4.3(1)**（`D` 层，无该绑定） |
| **`orth_eq_bot_of_discrete_valuation_nofin`** | 4.2 论文假设层级（Hensel 不完备，模 (R1)+(R2)） |
| **`thm_ramified_1_of_discrete_valuation_nofin`** | 4.3(1) 同上 |
| **`orth_eq_bot_paper`** | ★★★★★ **4.2 在论文的假设层级**：Hensel ＋ `∂₂` 两条性质（＝`prop:prelim-residue`(1)），**无**有限剩余域、**无**有限维 |
| **`thm_ramified_1_paper`** | ★★★★★ **4.3(1) 同上** |
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

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

attribute [local instance] TopRep.distribMulAction

/-- 任意线性泛函：`val|_U ≠ 0` ⟹ `\ker(val|_U)` 一维（类无关版）。 -/
theorem finrank_ker_restrict_plane_eq_one_nofin (hp2 : NeZero (2 : ZMod p))
    {x y : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) x y ≠ 0)
    (val : GaloBase.V F p →ₗ[ZMod p] ZMod p)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) x y, val u ≠ 0)
    :
    Module.finrank (ZMod p) ↥(LinearMap.ker
      (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) = 1 := by
  -- `FiniteDimensional` 只需作用在**平面**（二维）上，不需要整个 `V`。
  haveI : FiniteDimensional (ZMod p) ↥(ResidueCupData.plane (k := ZMod p) x y) :=
    Module.finite_of_finrank_pos (by
      rw [finrank_plane_eq_two_free (F := F) (p := p) hp2 hne]; norm_num)
  have hφne : (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) ≠ 0 := by
    obtain ⟨u, hu, hvu⟩ := hval
    intro h
    apply hvu
    have hz : (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) ⟨u, hu⟩ = 0 := by
      rw [h, LinearMap.zero_apply]
    simpa using hz
  have hsurj : Function.Surjective
      (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) := by
    intro c
    have hx : ∃ z : ↥(ResidueCupData.plane (k := ZMod p) x y),
        (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφne (LinearMap.ext h)
    obtain ⟨z, hz⟩ := hx
    refine ⟨(c / ((val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) z)) • z, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ c hz
  have hrange1 : Module.finrank (ZMod p) ↥(LinearMap.range
      (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj,
      (Submodule.topEquiv (R := ZMod p) (M := ZMod p)).finrank_eq, Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) (V₂ := ZMod p)
  have hplane : Module.finrank (ZMod p) ↥(ResidueCupData.plane (k := ZMod p) x y) = 2 :=
    finrank_plane_eq_two_free (F := F) (p := p) hp2 hne
  rw [hrange1, hplane] at hrn
  omega

/-- **`lem:ramified-vanishing`（论文 4.2）在论文的假设层级**：按论文原证明路线
（`Hyp151` 的逐步转写），只用 §2.4（作 `D`）与线性代数，**不假设完备性/局部域**。 -/
theorem orth_eq_bot_paper_route_hensel_nofin {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p)))
    (hp2 : NeZero (2 : ZMod p))
    {a1 a2 : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2, D.val u ≠ 0)
    :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ := by
  classical
  have hval' := hval
  obtain ⟨u, hu, hvu⟩ := hval
  set κ : GaloBase.V F p := (D.val u)⁻¹ • u with hκdef
  have hκU : κ ∈ ResidueCupData.plane (k := ZMod p) a1 a2 := Submodule.smul_mem _ _ hu
  have hκval : D.val κ = 1 := by
    rw [hκdef, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hvu
  have hfin := finrank_ker_restrict_plane_eq_one_nofin (F := F) (p := p) (x := a1) (y := a2)
    (val := D.val) (hval := hval') hp2 hne
  have hpos : 0 < Module.finrank (ZMod p) ↥(LinearMap.ker
      (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)) := by omega
  haveI : Nontrivial ↥(LinearMap.ker
      (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨γc, hγc⟩ := exists_ne (0 : ↥(LinearMap.ker
    (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)))
  have hγU : ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p)
      ∈ ResidueCupData.plane (k := ZMod p) a1 a2 :=
    (γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)).2
  have hγker : D.val ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) = 0 :=
    LinearMap.mem_ker.mp γc.2
  have hγne : ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) ≠ 0 := by
    intro h0
    apply hγc
    exact Subtype.ext (Subtype.ext h0)
  obtain ⟨γ₀, hγ₀⟩ := LinearMap.mem_range.mp (by
    rw [← HenselResidueData.ker_val_eq_range_infl_free (F := F) (p := p) D]
    exact hγker)
  refine eq_bot_iff.mpr ?_
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨x₀, m, hx₀⟩ := D.split x
  have hxγ : GaloBase.cup (K := F) (p := p) x
      ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) = 0 :=
    cup_eq_zero_of_mem_orth_free (F := F) (p := p) hx hγU
  have htm : m = 0 := by
    rw [hx₀, ← hγ₀] at hxγ
    have h := congrArg D.res hxγ
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      D.tame_uu x₀ γ₀, zero_add, map_zero] at h
    have hneg : D.res (GaloBase.cup (K := F) (p := p) D.pi (D.infl γ₀)) = -γ₀ :=
      D.tame_pi_u D.pi D.val_pi γ₀
    rw [hneg, smul_neg] at h
    have hγ₀ne : γ₀ ≠ 0 := by
      intro h0
      apply hγne
      rw [← hγ₀, h0, map_zero]
    have : m • γ₀ = 0 := neg_eq_zero.mp h
    rcases smul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hγ₀ne
  have hx1 : x = D.infl x₀ := by rw [hx₀, htm, zero_smul, add_zero]
  have hxκ : GaloBase.cup (K := F) (p := p) x κ = 0 :=
    cup_eq_zero_of_mem_orth_free (F := F) (p := p) hx hκU
  rw [hx1] at hxκ
  have h := congrArg D.res hxκ
  simp only [map_zero] at h
  have hneg2 : D.res (GaloBase.cup (K := F) (p := p) (D.infl x₀) κ) = x₀ := by
    have hskew : GaloBase.cup (K := F) (p := p) (D.infl x₀) κ
        = - GaloBase.cup (K := F) (p := p) κ (D.infl x₀) :=
      GaloBase.cup_skew (K := F) (p := p) _ _
    rw [hskew, map_neg, D.tame_pi_u κ hκval x₀, neg_neg]
  rw [hneg2] at h
  rw [hx1, h, map_zero]

variable [HasEnoughRootsOfUnity F p]

/-- **4.3(1)（论文层级，类无关）**：`U^⊥ = N = 0`，`D`（= §2.4）作输入。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_of_D_free_nofin {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
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
    :
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
    orth_eq_bot_paper_route_hensel_nofin (F := F) (p := p) D hp2' hneG hval
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


/-! ## 论文假设层级（Hensel，不完备）：4.2／4.3(1) 无有限维绑定 -/

section PaperLevelNoFin

variable {F : Type} [Field F] [ValuativeRel F] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]

/-- ★★★★ **4.2 在论文假设层级（Hensel，不完备），无 `FiniteDimensional V`**：
唯一缺口是两条剩余事实 (R1)+(R2)。 -/
theorem orth_eq_bot_of_discrete_valuation_nofin (hp : IsUnit (p : F))
    (v : Fˣ →* Multiplicative ℤ) {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hp2 : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hp u ≠ 0)
    (hfacts : TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π)) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_paper_route_hensel_nofin (F := F) (p := p)
    (D := henselResidueDataOfDiscreteValuation (F := F) (p := p) hp v hπ hfacts)
    hp2 hne hval

/-- ★★★★ **4.3(1) 在论文假设层级（Hensel，不完备），无 `FiniteDimensional V`**。 -/
theorem thm_ramified_1_of_discrete_valuation_nofin (hp : IsUnit (p : F))
    (hp2 : p ≠ 2) (Δ : Subgroup Fˣ) [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    (v : Fˣ →* Multiplicative ℤ) {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hfacts : TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π))
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      valLinOf (F := F) (p := p) v hp u ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ :=
  thm_ramified_1_of_D_free_nofin (F := F) (p := p)
    (D := henselResidueDataOfDiscreteValuation (F := F) (p := p) hp v hπ hfacts)
    hp hp2 Δ hroots hU ha1 ha2 hne hval

end PaperLevelNoFin

/-! ## ★ 论文的**精确假设层级**：Hensel ＋ `prop:prelim-residue`(1) 的两条性质 -/

section PaperExact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **4.2（`lem:ramified-vanishing`）在论文的精确假设层级**。

假设 = 论文 §4 的开头段（Hensel 离散赋值域、`char K ≠ p`、`μ_p ⊂ F`、`v(π)=1`）＋
**`prop:prelim-residue`(1) 的两条性质**（`hd_infl`／`hd_cup_pi`，论文自己证明的命题）。
**无** `[Finite (ResidueField)]`、**无** `FiniteDimensional`。 -/
theorem orth_eq_bot_paper {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF)
    (hd_infl : ∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (hd_cup_pi : ∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y)
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation_nofin (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := v) (π := π)
      hpF d hd_infl hd_cup_pi)

/-- ★★★★★ **4.3(1) 在论文的精确假设层级**（同上，无有限剩余域、无有限维）。 -/
theorem thm_ramified_1_paper {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF)
    (hd_infl : ∀ y z : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (hd_cup_pi : ∀ y : VKG F p v hpF,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π)) = y)
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
    v hπ (tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := v) (π := π)
      hpF d hd_infl hd_cup_pi) ha1 ha2 hne hval

end PaperExact

end L20261018

#print axioms L20261018.finrank_ker_restrict_plane_eq_one_nofin
#print axioms L20261018.orth_eq_bot_paper_route_hensel_nofin
#print axioms L20261018.thm_ramified_1_of_D_free_nofin
#print axioms L20261018.orth_eq_bot_of_discrete_valuation_nofin
#print axioms L20261018.thm_ramified_1_of_discrete_valuation_nofin
#print axioms L20261018.orth_eq_bot_paper
#print axioms L20261018.thm_ramified_1_paper
