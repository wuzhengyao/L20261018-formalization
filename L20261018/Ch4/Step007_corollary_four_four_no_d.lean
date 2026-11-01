import L20261018.Ch4.Step006_thm_ramified_no_d
import L20261018.Ch4.Step005_corollary_four_four_dimension

/-!
# R990：**T5（`corollary_4_4`）去 `D`** ＋ `d_F = d_K + 1` 的无条件化

`Hyp112` 的 `corollary_4_4` 活在 `ResidueCupData` 抽象层（入口 `D : ResidueCupData`）。
本文件把 `Hyp145.henselResidueData_explicit` 经 `HenselResidueData.toResidueCupData`
（`Hyp110`，`hskew` 由 `Theo352.cupLin_skew` 供给）转一层，得到**论文真实对象上的 T5**。

## 论文 `raw/L20261018.tex:1646`（未编号推论 4.4）的三步

| 论文声明 | 本文件 |
|---|---|
| `rank(Φ) = d_F`（秩--零化度 ＋ `U^⊥ = ker Φ = 0`） | `ResidueCupData.finrank_range_commonCupMap`（`Hyp112`） |
| `d_F = d_K + 1` | **`finrank_eq_finrank_add_one_uncond`**（本文件） |
| `d_K = 1 ⟹ rank(Φ) = 2` | **`corollary_4_4_uncond`**（本文件） |

## 载体与假设口径

* 载体：`V = H¹_abs(ZMod p)`、`∪ = Theo352.cupLin`、`VK = ↥(ker \bar v)`（`\bar v = valLin`）；
* `D` 已消失（由 `Hyp145.henselResidueData_explicit` 构造）；
* 剩余假设**全是论文自带的**：`hpu`（`char K ≠ p`）、`hp2`（`p ≠ 2`，交错性用）、
  `hne`（`(a₁)∪(a₂) ≠ 0`）、`hval`（`v|_U ≠ 0`）、**`hK1`（`d_K = 1`）**。
* **`hK1` 是论文假设**（论文原话「若 `d_K=1`，则 `rank(Φ)=2`」），
  在 `VK := ↥(ker \bar v)` 下它等价于 `finrank ↥(ker valLin) = 1`（`finrank = finrank V - 1`）。
  本文件**不**声称能证 `hK1`（需要 `finrank V = 2`，即 `H¹(F,μ_p) ≅ Fˣ/Fˣ^p` 的 `p²` 阶——
  五库皆无，登记 `∅-formalization-gap`）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-! ## 1. 显式载体上的 `ResidueCupData`（由 `HenselResidueData` 转层） -/

/-- **论文真实对象上的 `ResidueCupData`**（`D` 已构造）：由 `Hyp145` 的
`HenselResidueData` 经 `toResidueCupData` 转一层，`skew` 由 `cupLin_skew` 供给。 -/
noncomputable def residueCupData_explicit (hp : IsUnit (p : F))
    (hp2 : NeZero (2 : ZMod p)) (hpu : IsUnit (p : 𝒪[F]))
    {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    ResidueCupData (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))
      (H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) ↥(LinearMap.ker (valLin F p hp)) :=
  (henselResidueData_explicit (F := F) (p := p) hp hp2 hpu hne).toResidueCupData
    (fun x y => Theo352.cupLin_skew (F := F) (p := p) x y)

/-- `residueCupData_explicit` 的 `val` 就是 `valLin ∘ h1ToVEquiv`（`def` 体可见）。 -/
theorem residueCupData_explicit_val (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (u : H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :
    (residueCupData_explicit (F := F) (p := p) hp hp2 hpu hne).val u
      = valLin F p hp (KummerBridge.h1ToVEquiv F p u) := rfl

/-- `residueCupData_explicit` 的 `cup` 就是 `cupLin`（`def` 体可见）。 -/
theorem residueCupData_explicit_cup (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    (residueCupData_explicit (F := F) (p := p) hp hp2 hpu hne).cup
      = Theo352.cupLin (F := F) (p := p) := rfl

/-! ## 2. `d_F = d_K + 1`（论文 4.4 的第二步，`D` 已消失） -/

/-- **`d_F = d_K + 1`**（论文 `:1647`「命题~\ref{prop:prelim-kummer-valuation} 给出 `d_F=d_K+1`」）。

由 `Hyp112.ResidueCupData.finrank_eq_finrank_add_one` 用在 `residueCupData_explicit` 上。 -/
theorem finrank_eq_finrank_add_one_uncond (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))] :
    Module.finrank (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))
      = Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) + 1 := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  exact ResidueCupData.finrank_eq_finrank_add_one
    (residueCupData_explicit (F := F) (p := p) hp
      (Assemble36.neZero_two_zmod (p := p) hp2) hpu
      (cup_kummerClass_ne_zero (F := F) (p := p) hp hne))

/-! ## 3. **T5 去 `D`**：`d_K = 1 ⟹ rank(Φ) = 2` -/

/-- **4.4（未编号推论）在论文真实对象上，`D` 已消失**：
若 `d_K = 1`，则 `rank(Φ) = 2` 且 `d_F = 2`（`Φ = Φ_Bex = commonCupMap cupLin (a₁) (a₂)`）。

`hK1` 即论文的 `d_K = 1`（`VK = ↥(ker \bar v)` 时 `finrank VK = d_K`）。 -/
-- @source file=raw/L20261018.tex locator=line:1646 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_uncond (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLin F p hp (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) = 1)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))] :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2)).range = 2
      ∧ Module.finrank (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  exact ResidueCupData.corollary_4_4 (residueCupData_explicit (F := F) (p := p) hp
      (Assemble36.neZero_two_zmod (p := p) hp2) hpu
      (cup_kummerClass_ne_zero (F := F) (p := p) hp hne))
    (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
    (GaloCup.kummerExplicit (F := F) (p := p) hp a2) hne hval hK1

/-- `corollary_4_4_uncond` 与 `(Theo352.Bex …).Phi` 的口径一致：
`Bex.Phi = commonCupMap cupLin (a₁) (a₂)`（`def` 层同一公式，`rfl`）。 -/
theorem Bex_Phi_eq_commonCupMap (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hp hne).Phi
      = ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2) := rfl

end L20261018
#print axioms L20261018.residueCupData_explicit
#print axioms L20261018.finrank_eq_finrank_add_one_uncond
#print axioms L20261018.corollary_4_4_uncond
#print axioms L20261018.Bex_Phi_eq_commonCupMap
