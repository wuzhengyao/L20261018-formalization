import L20261018.Ch2.Hensel.ResidueMap.Step018_huu_discharged
import L20261018.Ch4.Step003_ramified_vanishing_paper_objects
import L20261018.Ch2.Hensel.ResidueMap.Step006_tame_pi_u_of

/-!
# R978：**`HenselResidueData` 的 11 个字段里 9 个由定理供给** —— `tame_uu` 字段摘除

`Hyp110` 的具名假设 `HenselResidueData` 有 **11 个字段**。本文件构造真实实例：

| 字段 | 来源 |
|---|---|
| `res` | **假设**（T2，未解） |
| `val` | `Hyp115.valLin`（定理） |
| `infl` / `inj_infl` / `val_infl` | `VK := ↥(ker valLin)` 的子类型（定理） |
| `pi` | `Hyp19.kummerClass π`；`val_pi` = `Hyp115.valLin_pi`（定理） |
| `split` | `Hyp117.decomp_mem_ker`（定理） |
| **`tame_uu`** | **`Hyp135.ker_cup_eq_zero`（定理！本轮摘除）** |
| `tame_u_pi` | **假设**（T3 研究级边界，未解） |
| `tame_pi_u` | `Hyp119.tame_pi_u_of` 由前后两条推出（定理） |

⟹ **`∅-open` 从 11 个字段降到 2 个**（`res` 与 `tame_u_pi`），其余 9 个全部机检。
论文假设 `char K ≠ p`（`raw/L20261018.tex:982`）以 `hpu : IsUnit (p : 𝒪[F])` 的形式显式带入。
-/

set_option maxHeartbeats 4000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **`HenselResidueData` 的真实实例**：只保留 `res` 与 `tame_u_pi` 两条假设，
其余 9 个字段全部由已机检的定理供给（**`tame_uu` 由 `Hyp135.ker_cup_eq_zero`**）。 -/
noncomputable def henselResidueDataOfKer (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {π : Fˣ} (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F]))
    (res : GaloBase.H2 F p →ₗ[ZMod p] ↥(LinearMap.ker (valLin F p hp)))
    (tame_u_pi : ∀ y : ↥(LinearMap.ker (valLin F p hp)),
      res (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hp π)) = y) :
    HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p)
      ↥(LinearMap.ker (valLin F p hp)) (GaloBase.cup (K := F) (p := p)) where
  res := res
  val := valLin F p hp
  infl := (LinearMap.ker (valLin F p hp)).subtype
  inj_infl := Subtype.val_injective
  val_infl := fun y => y.2
  pi := KummerBridge.kummerClass F p hp π
  val_pi := valLin_pi (F := F) (p := p) hp hπ
  split := fun x => decomp_mem_ker (valLin F p hp) (KummerBridge.kummerClass F p hp π)
    (valLin_pi (F := F) (p := p) hp hπ) x
  tame_uu := fun y z => by
    show res (GaloBase.cup (K := F) (p := p) ((y : GaloBase.V F p)) ((z : GaloBase.V F p))) = 0
    rw [ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y z, map_zero]
  tame_u_pi := tame_u_pi
  tame_pi_u := fun κ hκ z =>
    tame_pi_u_of (GaloBase.cup (K := F) (p := p))
      (fun x y => GaloBase.cup_skew (K := F) (p := p) x y) (valLin F p hp)
      (KummerBridge.kummerClass F p hp π) (valLin_pi (F := F) (p := p) hp hπ) res
      (fun y z => by
        rw [ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y z, map_zero])
      tame_u_pi κ hκ z

/-- **T3／`lem:ramified-vanishing` 在「只剩 `res` 与 `tame_u_pi`」的形态下成立**：
用上面那个真实 `HenselResidueData` 实例 ＋ `Hyp110.ramified_vanishing`。 -/
theorem ramified_vanishing_ker_tame (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F]))
    (res : GaloBase.H2 F p →ₗ[ZMod p] ↥(LinearMap.ker (valLin F p hp)))
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
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ :=
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  HenselResidueData.ramified_vanishing
    (henselResidueDataOfKer (F := F) (p := p) hp
      (Assemble36.neZero_two_zmod (p := p) hp2) (hπ := hπ) hpu res tame_u_pi)
    (fun x y => GaloBase.cup_skew (K := F) (p := p) x y)
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) hne hval

end L20261018
#print axioms L20261018.henselResidueDataOfKer
#print axioms L20261018.ramified_vanishing_ker_tame
