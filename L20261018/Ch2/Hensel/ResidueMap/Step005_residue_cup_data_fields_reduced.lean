import L20261018.Ch2.Hensel.ResidueMap.Step004_valuation_decomposition_unique
import L20261018.Ch4.Step002_residue_cup_data_shape
import L20261018.Ch3.NormImage.Step018_three_six_nezero_two

/-!
# R948：**把 `ResidueCupData` 的 11 个假设字段压到 4 个**

## 观察

论文 `prop:prelim-kummer-valuation`(2) 的分裂正合列

$$0\to H^1(K,\mu_p)\xrightarrow{\mathrm{inf}}H^1(F,\mu_p)\xrightarrow{\bar v}\Fp\to0$$

里，**`\ker\bar v` 就是 `\mathrm{inf}` 的像**（正合）。于是 `infl` **不必独立假设**：
取 `VK := ↥(ker \bar v)`、`infl := Subtype` 即可，且

* `inj_infl` = 子类型单射（免费）；
* `val_infl` = 成员条件 `y.2`（免费）；
* `split` = `Hyp116.exists_decomp`（`x₀ := x - \bar v(x)·π`，免费）；
* `val`、`val_pi` = `Hyp115`（`\bar v` 与 `\bar v((π)) = 1`，已机检）。

⟹ `ResidueCupData` 的 11 个字段里，**6 个变成定理**，只剩 4 个真假设：
`res`（剩余映射）＋ `tame_uu`／`tame_u_pi`／`tame_pi_u`（驯符号三条特化）。

**这不是偷换**：论文的 `\ker\bar v` **恰是** `H¹(K,μ_p)` 的像（`prop:prelim-kummer-valuation`(1)
的单位约化同构 ＋ `(2)` 的正合性），故把 `VK` 取成 `ker \bar v` 与取成 `H¹(K,μ_p)` **同构意义下等价**；
本文件采用的是「不显式搬 `H¹(K,μ_p)` 载体」的那一侧（L12 载体身份）。

## 与 T3 的关系

`ResidueCupData` 的字段名与类型**完全不变**，故 `Hyp109.vanishing`（T3 抽象版）
**无需改一字**即可作用在本文件造出的实例上 ⟹ 具名假设的那部分**实际被消掉**。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

section Abstract

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- **分解落在 `\ker\bar v` 里**（显式陈述；供 `structure` 字段以 `exact` 喂入，
避免在 `where` 里硬证 —— R933 教训）。 -/
theorem decomp_mem_ker (val : V →ₗ[k] k) (π : V) (hπ : val π = 1) (x : V) :
    ∃ (x₀ : ↥(LinearMap.ker val)) (m : k), x = (x₀ : V) + m • π := by
  refine ⟨⟨x - val x • π, ?_⟩, val x, ?_⟩
  · simp [map_sub, hπ]
  · rw [sub_add_cancel]

/-- **由 `\bar v` ＋ `π` ＋ 剩余映射 ＋ 三条驯符号，造出 `ResidueCupData`**
（`VK := ker \bar v`，`infl := Subtype`）。 -/
noncomputable def residueCupDataOfKer (cup : V →ₗ[k] V →ₗ[k] H2)
    (hskew : ∀ x y, cup x y = - cup y x) (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    (res : H2 →ₗ[k] ↥(LinearMap.ker val))
    (tame_uu : ∀ y z : ↥(LinearMap.ker val), res (cup (y : V) (z : V)) = 0)
    (tame_u_pi : ∀ y : ↥(LinearMap.ker val), res (cup (y : V) π) = y)
    (tame_pi_u : ∀ (κ : V), val κ = 1 → ∀ z : ↥(LinearMap.ker val), res (cup κ (z : V)) = -z) :
    ResidueCupData k V H2 ↥(LinearMap.ker val) where
  cup := cup
  skew := hskew
  res := res
  val := val
  infl := (LinearMap.ker val).subtype
  inj_infl := Subtype.val_injective
  val_infl := fun y => y.2
  pi := π
  val_pi := hπ
  split := fun x => decomp_mem_ker val π hπ x
  tame_uu := tame_uu
  tame_u_pi := tame_u_pi
  tame_pi_u := tame_pi_u

/-- **T3（`lem:ramified-vanishing`）在「压到 4 条假设」的形态下成立**：
`\bar v`、`π`、`\bar v(π)=1` 都是**给定数据**（由 `Hyp115`／`Hyp116` 免费供给），
只有 `res` 与三条驯符号是假设。 -/
theorem vanishing_of_ker (cup : V →ₗ[k] V →ₗ[k] H2)
    (hskew : ∀ x y, cup x y = - cup y x) (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    (res : H2 →ₗ[k] ↥(LinearMap.ker val))
    (tame_uu : ∀ y z : ↥(LinearMap.ker val), res (cup (y : V) (z : V)) = 0)
    (tame_u_pi : ∀ y : ↥(LinearMap.ker val), res (cup (y : V) π) = y)
    (tame_pi_u : ∀ (κ : V), val κ = 1 → ∀ z : ↥(LinearMap.ker val), res (cup κ (z : V)) = -z)
    [NeZero (2 : k)] (a1 a2 : V) (hne : cup a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := k) a1 a2, val u ≠ 0) :
    ResidueCupData.orth cup a1 a2 = ⊥ :=
  (residueCupDataOfKer cup hskew val π hπ res tame_uu tame_u_pi tame_pi_u).vanishing
    a1 a2 hne hval

end Abstract

/-! ## 论文层：`\bar v` 与 `(π)` 由 `Hyp115`／`Hyp116` 供给 -/

section Paper

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **论文层：只要 4 条假设**（`res` ＋ 三条驯符号），T3 就在论文载体
`GaloBase.V F p`／`GaloBase.cup` 上成立 —— `\bar v` 与 `(π)` 全部是定理。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem ramified_vanishing_reduced (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (res : GaloBase.H2 F p →ₗ[ZMod p]
      ↥(LinearMap.ker (valLin F p hp)))
    (tame_uu : ∀ y z : ↥(LinearMap.ker (valLin F p hp)),
      res (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (tame_u_pi : ∀ y : ↥(LinearMap.ker (valLin F p hp)),
      res (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hp π)) = y)
    (tame_pi_u : ∀ (κ : GaloBase.V F p), (valLin F p hp) κ = 1 →
      ∀ z : ↥(LinearMap.ker (valLin F p hp)),
        res (GaloBase.cup (K := F) (p := p) κ (z : GaloBase.V F p)) = -z)
    (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      (valLin F p hp) u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  exact vanishing_of_ker (GaloBase.cup (K := F) (p := p))
    (fun x y => GaloBase.cup_skew (K := F) (p := p) x y)
    (valLin F p hp) (KummerBridge.kummerClass F p hp π)
    (valLin_pi (F := F) (p := p) hp hπ) res tame_uu tame_u_pi tame_pi_u
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) hne hval

end Paper

end L20261018

#print axioms L20261018.residueCupDataOfKer
#print axioms L20261018.vanishing_of_ker
#print axioms L20261018.ramified_vanishing_reduced
