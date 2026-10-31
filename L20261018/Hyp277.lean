import Hyp157

/-!
# R1153（**第 1 项：单载体合述 —— 4.3(1)(2) ＋ 4.4 在同一载体上一次陈述**）

## 本轮做什么

`CH4-COVERAGE-AUDIT.md` §3 的偏差 ④：4.3(1)／4.4 在显式载体、4.3(2) 在 `GaloBase.V`，
「`(1)`／`(2)` 不是同一载体上的陈述」。

**核查结果（本轮）**：`Theo352.Bex` 的载体**就是** `H1 (AbsoluteGaloisGroup F) (ZMod p)`（`Hyp92.Bex`，`cup := cupLin`），
`corollary_4_4_of_D_free` 的 `commonCupMap (Theo352.cupLin …)` **也在同一载体** ⟹
**两处本来同载体**，缺的只是**一条把四条结论合起来的陈述**。

本轮给出该合述定理 `ch4_single_carrier_combined`：
`U^⊥ = ⊥`（4.2/4.3(1)）∧ `N = ⊥`（4.3(1)）∧ `3 ≤ rank Φ`（4.3(2)）∧
`rank Φ = 2` 与 `d_F = 2`（4.4，`d_K = 1` 时），**全部在 `V = H¹(F, μ_p)` 上一次陈述**。

## 本轮

| 声明 | 内容 |
|---|---|
| **`ch4_single_carrier_combined`** | ★★★★ **第 4 章四条结果的单载体合述**（论文 `V = H¹(F,μ_p)`） |
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- ★★★★ **第 4 章的四条结果在同一载体 `V = H¹(F, μ_p)` 上一次陈述**。

* 4.2／4.3(1) 前半：`U^⊥ = ⊥`；
* 4.3(1) 后半：`N = ⊥`；
* 4.3(2)：`3 ≤ rank(Φ)`；
* 4.4（`d_K = 1` 时）：`rank(Φ) = 2` 且 `d_F = 2`。

（`U^⊥`／`N`／`Φ` 都由 `Theo352.Bex`（`cup := cupLin`）给出，载体同为 `H1 (AbsoluteGaloisGroup F) (ZMod p)`；
4.4 的 `Φ` 写成 `ResidueCupData.commonCupMap (Theo352.cupLin …)`，与 `Bex.cup` 同一支杯积。） -/
theorem ch4_single_carrier_combined {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
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
    (hval' : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      D.val (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2)
    (hK1 : Module.finrank (ZMod p) VK = 1)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)]
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    [NeZero (2 : ZMod p)] :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ ∧
      (3 : Cardinal) ≤ Module.rank (ZMod p)
        ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range ∧
      Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2)).range = 2 ∧
      Module.finrank (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 := by
  obtain ⟨h1, h2, h3⟩ := thm_ramified_combined (F := F) (p := p) D hp hp2 Δ hroots hU
    ha1 ha2 hne hval b1 b2 hD
  obtain ⟨h4, h5⟩ := corollary_4_4_of_D_free (F := F) (p := p) D hp hne hval' hK1
  exact ⟨h1, h2, h3, h4, h5⟩

end L20261018

#print axioms L20261018.ch4_single_carrier_combined
