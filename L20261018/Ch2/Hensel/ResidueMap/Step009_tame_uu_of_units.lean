import L20261018.Ch2.Hensel.ResidueMap.Step008_exists_unit_rep
set_option maxHeartbeats 2000000
open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField
namespace L20261018

section Paper
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`tame_uu` 由「单位-单位杯积为零」推出**：用 `Hyp122.exists_unit_rep` 把 `\ker\bar v` 的
两个元素各换成**单位**的 Kummer 类，再用单位-单位的假设。

这是把 `tame_uu` **换成可搬运形态**的关键一步：右侧 `hUU` 只谈 `Fˣ` 与 `GaloBase.cup`，
正是 `localSymbol` 单位-单位定理经载体桥后能供给的形状。 -/
theorem tame_uu_of_units (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (VK : Type) [AddCommGroup VK] [Module (ZMod p) VK]
    (res : GaloBase.H2 F p →ₗ[ZMod p] VK)
    (hUU : ∀ u w : Fˣ, TauCeti.normalizedValuation F u = 1 →
      TauCeti.normalizedValuation F w = 1 →
        GaloBase.cup (K := F) (p := p)
          (KummerBridge.kummerClass F p hp u) (KummerBridge.kummerClass F p hp w) = 0) :
    ∀ y z : ↥(LinearMap.ker (valLin F p hp)),
      res (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 := by
  intro y z
  obtain ⟨u, hu, h1⟩ := exists_unit_rep (F := F) (p := p) hp (hπ := hπ)
    (y := (y : GaloBase.V F p)) (LinearMap.mem_ker.mp y.2)
  obtain ⟨w, hw, h2⟩ := exists_unit_rep (F := F) (p := p) hp (hπ := hπ)
    (y := (z : GaloBase.V F p)) (LinearMap.mem_ker.mp z.2)
  rw [show (y : GaloBase.V F p) = KummerBridge.kummerClass F p hp u from h1.symm,
    show (z : GaloBase.V F p) = KummerBridge.kummerClass F p hp w from h2.symm,
    hUU u w hu hw, map_zero]

/-- **T3 的「可搬运」形态**：假设只剩 `res` ＋ **单位-单位杯积为零** ＋ `tame_u_pi`。
（`tame_uu` 已被 `tame_uu_of_units` 从 `hUU` 推出。） -/
theorem ramified_vanishing_units (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (res : GaloBase.H2 F p →ₗ[ZMod p] ↥(LinearMap.ker (valLin F p hp)))
    (hUU : ∀ u w : Fˣ, TauCeti.normalizedValuation F u = 1 →
      TauCeti.normalizedValuation F w = 1 →
        GaloBase.cup (K := F) (p := p)
          (KummerBridge.kummerClass F p hp u) (KummerBridge.kummerClass F p hp w) = 0)
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
  ramified_vanishing_reduced3 (F := F) (p := p) hp hp2 (hπ := hπ) (res := res)
    (tame_uu_of_units (F := F) (p := p) hp (hπ := hπ) (VK := ↥(LinearMap.ker (valLin F p hp)))
      res hUU)
    (tame_u_pi := tame_u_pi) (a1 := a1) (a2 := a2) hne hval

end Paper
end L20261018
#print axioms L20261018.tame_uu_of_units
#print axioms L20261018.ramified_vanishing_units
