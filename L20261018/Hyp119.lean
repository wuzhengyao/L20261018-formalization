import Hyp117
import Hyp103
set_option maxHeartbeats 2000000
namespace L20261018

section Abstract
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- **`tame_pi_u` 是多余的**：由 `tame_uu` ＋ `tame_u_pi` ＋ 斜对称 ＋ 线性推出。

理由（纯线性代数）：`val κ = 1 = val π` ⟹ `d := κ - π ∈ ker val`，故
`cup κ (↑z) = cup π (↑z) + cup d (↑z)`；第一项由 `tame_u_pi` ＋ 斜对称给 `-z`，
第二项由 `tame_uu`（两个 `ker val` 元素）给 `0`。 -/
theorem tame_pi_u_of (cup : V →ₗ[k] V →ₗ[k] H2) (hskew : ∀ x y, cup x y = - cup y x)
    (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    (res : H2 →ₗ[k] ↥(LinearMap.ker val))
    (tame_uu : ∀ y z : ↥(LinearMap.ker val), res (cup (y : V) (z : V)) = 0)
    (tame_u_pi : ∀ y : ↥(LinearMap.ker val), res (cup (y : V) π) = y)
    (κ : V) (hκ : val κ = 1) (z : ↥(LinearMap.ker val)) :
    res (cup κ (z : V)) = -z := by
  have hmem : κ - π ∈ LinearMap.ker val := by
    rw [LinearMap.mem_ker, map_sub, hκ, hπ, sub_self]
  have hκπ : κ = π + ((⟨κ - π, hmem⟩ : ↥(LinearMap.ker val)) : V) := by
    simp
  have h1 : res (cup π (z : V)) = -z := by
    rw [hskew π (z : V), map_neg, tame_u_pi z]
  have h2 : res (cup ((⟨κ - π, hmem⟩ : ↥(LinearMap.ker val)) : V) (z : V)) = 0 :=
    tame_uu ⟨κ - π, hmem⟩ z
  rw [hκπ, map_add, LinearMap.add_apply, map_add, h1, h2, add_zero]

/-- **T3 只要 3 条假设**（`res` ＋ `tame_uu` ＋ `tame_u_pi`）。 -/
theorem vanishing_of_ker3 (cup : V →ₗ[k] V →ₗ[k] H2) (hskew : ∀ x y, cup x y = - cup y x)
    (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    (res : H2 →ₗ[k] ↥(LinearMap.ker val))
    (tame_uu : ∀ y z : ↥(LinearMap.ker val), res (cup (y : V) (z : V)) = 0)
    (tame_u_pi : ∀ y : ↥(LinearMap.ker val), res (cup (y : V) π) = y)
    [NeZero (2 : k)] (a1 a2 : V) (hne : cup a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := k) a1 a2, val u ≠ 0) :
    ResidueCupData.orth cup a1 a2 = ⊥ :=
  vanishing_of_ker cup hskew val π hπ res tame_uu tame_u_pi
    (fun κ hκ z => tame_pi_u_of cup hskew val π hπ res tame_uu tame_u_pi κ hκ z)
    a1 a2 hne hval

end Abstract


/-! ## 论文层：`GaloBase.cup` 上只要 3 条假设 -/

section Paper

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **论文 `lem:ramified-vanishing`（`GaloBase.cup` 上，只要 3 条假设）**：
`\bar v`、`(π)`、`\bar v(π)=1` 全部由 `Hyp115`／`Hyp116` 供给；`tame_pi_u` 由 `tame_pi_u_of` 证掉。
⟹ 只剩 `res`、`tame_uu`、`tame_u_pi`。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem ramified_vanishing_reduced3 (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (res : GaloBase.H2 F p →ₗ[ZMod p] ↥(LinearMap.ker (valLin F p hp)))
    (tame_uu : ∀ y z : ↥(LinearMap.ker (valLin F p hp)),
      res (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0)
    (tame_u_pi : ∀ y : ↥(LinearMap.ker (valLin F p hp)),
      res (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hp π)) = y)
    (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      (valLin F p hp) u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  exact vanishing_of_ker3 (GaloBase.cup (K := F) (p := p))
    (fun x y => GaloBase.cup_skew (K := F) (p := p) x y)
    (valLin F p hp) (KummerBridge.kummerClass F p hp π)
    (valLin_pi (F := F) (p := p) hp hπ) res tame_uu tame_u_pi
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) hne hval

end Paper

end L20261018
#print axioms L20261018.tame_pi_u_of
#print axioms L20261018.vanishing_of_ker3
#print axioms L20261018.ramified_vanishing_reduced3
