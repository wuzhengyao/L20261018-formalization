import L20261018.Hyp138

/-!
# R981：**论文 `lem:ramified-vanishing` 成为无驯符号假设的定理**

`Hyp138` 只给了 `Nonempty`（Prop）—— 那样取出的 `D` 是**不透明**的（`D.val` 不再定义等于 `valLin`），
因而不能直接喂给 `HenselResidueData.ramified_vanishing`（它的 `hval` 用 `D.val`）。

本文件把同一构造写成**返回结构的 `def`**（`def` 体可见 ⟹ `D.val` 定义等于 `valLin`），
再喂给 `Hyp110.ramified_vanishing`，得到**不再接受 `D` 与三条驯符号假设**的 T3。

## ⚠ 载体身份（L12／L16）

`res` 仍是 `Φ := cup (·) π` 的**某个左逆**（由 `Classical.choice` 取出），**不是**论文 `∂₂`。
但**本定理的结论不涉及 `res`**：`HenselResidueData` 对 `res` 的全部约束都落在
`im Φ`（`tame_u_pi`）与 `0`（`tame_uu`）上，故结论**与 `res` 的选取无关**。
-/

set_option maxHeartbeats 4000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **`HenselResidueData` 的具体实例**（`def` 体可见，故 `D.val` 定义等于 `valLin`）。

11 个字段全部由定理供给；`res` 取 `Φ := kerCupPi` 的某个左逆（`Φ` 单射，`Hyp138`／`Hyp137`）。 -/
noncomputable def henselResidueDataOfCup (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {π : Fˣ} (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p)
      ↥(LinearMap.ker (valLin F p hp)) (GaloBase.cup (K := F) (p := p)) := by
  classical
  -- `∃` 是 Prop，而目标是 Type（结构）⟹ 必须用 `Classical.choose`（`noncomputable def` 内可用）
  let γ : ↥(LinearMap.ker (valLin F p hp)) :=
    Classical.choose (exists_cup_pi_ne_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu
      (a1 := a1) (a2 := a2) hne)
  have hγ := Classical.choose_spec (exists_cup_pi_ne_zero (F := F) (p := p) hp hp2
    (hπ := hπ) hpu (a1 := a1) (a2 := a2) hne)
  have hγ' : kerCupPi (F := F) (p := p) hp π γ ≠ 0 := by
    rw [kerCupPi_apply]
    exact hγ
  have hinj := kerCupPi_injective (F := F) (p := p) hp hp2 (hπ := hπ) hpu hγ'
  let g : GaloBase.H2 F p →ₗ[ZMod p] ↥(LinearMap.ker (valLin F p hp)) :=
    Classical.choose (LinearMap.exists_leftInverse_of_injective
      (kerCupPi (F := F) (p := p) hp π) (LinearMap.ker_eq_bot.mpr hinj))
  have hg := Classical.choose_spec (LinearMap.exists_leftInverse_of_injective
    (kerCupPi (F := F) (p := p) hp π) (LinearMap.ker_eq_bot.mpr hinj))
  have hleft : ∀ y : ↥(LinearMap.ker (valLin F p hp)),
      g (kerCupPi (F := F) (p := p) hp π y) = y := by
    intro y
    have h := congrFun (congrArg DFunLike.coe hg) y
    simpa [LinearMap.comp_apply] using h
  refine HenselResidueData.mk g (valLin F p hp)
    (LinearMap.ker (valLin F p hp)).subtype Subtype.val_injective (fun y => y.2)
    (KummerBridge.kummerClass F p hp π) (valLin_pi (F := F) (p := p) hp hπ)
    (fun x => decomp_mem_ker (valLin F p hp) (KummerBridge.kummerClass F p hp π)
      (valLin_pi (F := F) (p := p) hp hπ) x) ?_ ?_ ?_
  · -- `tame_uu`
    intro y z
    show g (GaloBase.cup (K := F) (p := p) ((y : GaloBase.V F p)) ((z : GaloBase.V F p))) = 0
    rw [ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y z, map_zero]
  · -- `tame_u_pi`
    intro y
    show g (kerCupPi (F := F) (p := p) hp π y) = y
    exact hleft y
  · -- `tame_pi_u`
    intro κ hκ z
    exact tame_pi_u_of (GaloBase.cup (K := F) (p := p))
      (fun x y => GaloBase.cup_skew (K := F) (p := p) x y) (valLin F p hp)
      (KummerBridge.kummerClass F p hp π) (valLin_pi (F := F) (p := p) hp hπ) g
      (fun y z => by
        show g (GaloBase.cup (K := F) (p := p) ((y : GaloBase.V F p)) ((z : GaloBase.V F p))) = 0
        rw [ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y z, map_zero])
      (fun y => by
        show g (kerCupPi (F := F) (p := p) hp π y) = y
        exact hleft y)
      κ hκ z


/-- **T3（论文 `lem:ramified-vanishing`）无条件版**（除 `char K ≠ p` 与 `p ≠ 2`）：
不再接受 `HenselResidueData`／`tame_uu`／`tame_u_pi`／`tame_pi_u`。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem ramified_vanishing_unconditional (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      (valLin F p hp) u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  have hval' : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      (henselResidueDataOfCup (F := F) (p := p) hp
        (Assemble36.neZero_two_zmod (p := p) hp2) (hπ := hπ) hpu hne).val u ≠ 0 := hval
  exact HenselResidueData.ramified_vanishing
    (henselResidueDataOfCup (F := F) (p := p) hp (Assemble36.neZero_two_zmod (p := p) hp2)
      (hπ := hπ) hpu hne)
    (fun x y => GaloBase.cup_skew (K := F) (p := p) x y)
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) hne hval'

end L20261018
#print axioms L20261018.ramified_vanishing_unconditional
