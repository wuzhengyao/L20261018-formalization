import L20261018.Ch2.Kummer.Step018_bridge_kc_def
import L20261018.Ch2.Kummer.Step011_cup_fp_eq_galo_cup_equiv
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic

/-!
# 载体桥「第 1.5 段」：`bridgeKc` 上单位-单位杯积为零

`Hyp125` 给出 `cupFp`（`Field.absoluteGaloisGroup` 载体）上两个**单位** Kummer 类的杯积为零。
本文件把它沿 `bridgeKc` 的三段链搬到 `GaloBase.cup`（`TauCeti.AbsoluteGaloisGroup` 载体）：

    cupFp (小群)   --cupFp_map（群变元自然性）-->  cupFp (大群)
                   --Hyp46 cupFp_coeffMap_eq_cup-->  GaloBase.cup

⟹ **`GaloBase.cup (bridgeKc u) (bridgeKc w) = 0`**（`cup_bridgeKc_unit_unit_eq_zero`）。

再加上「`bridgeKc` 与 `KummerBridge.kummerClass` 只差一个非零尺度」这一条
（`hUU_of_scale`：**本阶段唯一剩余的等式缺口**），即得 `hUU`。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **`bridgeKc` 上的单位-单位杯积为零**。

三段：(1) `Hyp125`（`cupFp` 小群载体）；(2) `TauCeti.cupFp_map`（`cohomFpMap` 保持杯积，
群变元自然性）；(3) `Hyp46.GaloCupTransport.cupFp_coeffMap_eq_cup`（`cupFp` 在载体同构下即
`GaloBase.cup`）。

假设与 `Hyp124`／`Hyp125` 完全一致：`tr`（`H²` 的迹识别）与 `hp`（剩余特征不分 `p`）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_2((u)\cup(w))=0."
theorem cup_bridgeKc_unit_unit_eq_zero {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (tr : ↑(continuousCohomology 2 (ClassFieldTheory.muNRep p F)).toModuleCat ≃+ ZMod p)
    (hres : ¬ ringChar 𝓀[F] ∣ p) {a b : Fˣ}
    (ha : a ∈ unitFiltration F 0) (hb : b ∈ unitFiltration F 0) :
    GaloBase.cup (K := F) (p := p) (bridgeKc (F := F) p hζ a)
      (bridgeKc (F := F) p hζ b) = 0 := by
  -- `Hyp125`：小群载体上的零点
  have hsmall : TauCeti.cupFp p (Field.absoluteGaloisGroup F)
      ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
        (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a))
      ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
        (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit b)) = 0 :=
    cupFp_unit_unit_eq_zero (K := F) (n := p) (ζ := ζ) hζ tr hres ha hb
  -- 沿 `cohomFpMap ρ.symm` 搬到 BIG 群载体：`cupFp_map` 是 `@[simp]`
  have hbig : TauCeti.cupFp p (TauCeti.AbsoluteGaloisGroup F)
      ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
        ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
          (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a)))
      ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
        ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
          (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit b))) = 0 := by
    rw [← TauCeti.cupFp_map (p := p) (G := Field.absoluteGaloisGroup F)
      (H := TauCeti.AbsoluteGaloisGroup F)
      (φ := (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm), hsmall, map_zero]
  -- `Hyp46`：`cupFp` 在载体同构下即 `GaloBase.cup`
  rw [show bridgeKc (F := F) p hζ a
        = ContinuousCohomology.coeffMap (GaloTrivialFp.iso F p).hom 1
            ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
              ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
                (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a))) from rfl,
      show bridgeKc (F := F) p hζ b
        = ContinuousCohomology.coeffMap (GaloTrivialFp.iso F p).hom 1
            ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
              ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
                (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit b))) from rfl,
      ← GaloCupTransport.cupFp_coeffMap_eq_cup (K := F) (p := p), hbig, map_zero]

/-- **`hUU` 由「`bridgeKc` 与 `KummerBridge.kummerClass` 只差一个非零尺度」推出。**

这是本阶段**唯一剩余的等式缺口**：`∃ c : ZMod p, c ≠ 0 ∧ ∀ a, bridgeKc a = c • kummerClass a`。
一旦该缺口补上，`hUU` 即为定理（配合 `cup_bridgeKc_unit_unit_eq_zero`）。 -/
theorem hUU_of_scale {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : F))
    {c : ZMod p} (hc : c ≠ 0)
    (hscale : ∀ a : Fˣ,
      bridgeKc (F := F) p hζ a = c • KummerBridge.kummerClass F p hp a)
    (hcup : ∀ a b : Fˣ, a ∈ unitFiltration F 0 → b ∈ unitFiltration F 0 →
      GaloBase.cup (K := F) (p := p) (bridgeKc (F := F) p hζ a)
        (bridgeKc (F := F) p hζ b) = 0) :
    ∀ u w : Fˣ, normalizedValuation F u = 1 → normalizedValuation F w = 1 →
      GaloBase.cup (K := F) (p := p)
        (KummerBridge.kummerClass F p hp u) (KummerBridge.kummerClass F p hp w) = 0 := by
  intro u w hu hw
  have hu' : u ∈ unitFiltration F 0 :=
    (mem_unitFiltration_zero u).2 ((normalizedValuation_eq_one_iff u).1 hu)
  have hw' : w ∈ unitFiltration F 0 :=
    (mem_unitFiltration_zero w).2 ((normalizedValuation_eq_one_iff w).1 hw)
  -- 尺度关系把 `bridgeKc` 侧变成 `cup (c • kc u) (c • kc w)`
  have hz : GaloBase.cup (K := F) (p := p) (c • KummerBridge.kummerClass F p hp u)
      (c • KummerBridge.kummerClass F p hp w) = 0 := by
    rw [← hscale u, ← hscale w]
    exact hcup u w hu' hw'
  -- 双线性：`cup (c • x) (c • y) = (c * c) • cup x y`
  have hsmul : ∀ x y : GaloBase.V F p,
      GaloBase.cup (K := F) (p := p) (c • x) (c • y)
        = (c * c) • GaloBase.cup (K := F) (p := p) x y := by
    intro x y
    have e1 : GaloBase.cup (K := F) (p := p) (c • x)
        = c • GaloBase.cup (K := F) (p := p) x := by simp
    have e2 : GaloBase.cup (K := F) (p := p) x (c • y)
        = c • GaloBase.cup (K := F) (p := p) x y := by simp
    calc GaloBase.cup (K := F) (p := p) (c • x) (c • y)
        = (c • GaloBase.cup (K := F) (p := p) x) (c • y) := by rw [e1]
      _ = c • GaloBase.cup (K := F) (p := p) x (c • y) := rfl
      _ = c • (c • GaloBase.cup (K := F) (p := p) x y) := by rw [e2]
      _ = (c * c) • GaloBase.cup (K := F) (p := p) x y := by rw [smul_smul]
  rw [hsmul] at hz
  set z := GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp u)
    (KummerBridge.kummerClass F p hp w)
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  calc z = ((c * c)⁻¹ * (c * c)) • z := by rw [inv_mul_cancel₀ hc2, one_smul]
    _ = (c * c)⁻¹ • ((c * c) • z) := by rw [← smul_smul]
    _ = (c * c)⁻¹ • 0 := by rw [hz]
    _ = 0 := smul_zero _

end L20261018
#print axioms L20261018.cup_bridgeKc_unit_unit_eq_zero
#print axioms L20261018.hUU_of_scale
