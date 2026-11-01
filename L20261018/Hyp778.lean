import Hyp777

/-!
# S74 R4：**(甲1) 的输入降为「`H¹(Γ⧸I,ℤ/p)` 非零」**——`inflToVKG` 单射

`Hyp777.finrank_VKG_eq_one_of_ne_zero` 把 (甲1) 的输入降为 `∃ y ∈ VKG, y ≠ 0`。
本轮再降一层：`inflToVKG : H¹(Γ⧸I,ℤ/p) →ₗ VKG` **单射**（它是 `infl1EquivVKG` 的"半"），
故 `VKG` 非平凡 ⟺ `H¹(Γ⧸I,ℤ/p)` 非平凡。

## 为什么这有用

**`H¹(Γ⧸I,ℤ/p)` 的非平凡性是本战役里最便宜的非平凡性**：
* `Γ⧸I ≃* Ẑ`（`Hyp380.galoisQuotientInertiaEquivZHat`）；
* TauCeti 有 `TauCeti.zHat.h1EquivZMod : H1 zHat (ZMod n) ≃ₗ[ZMod n] ZMod n`
  （`ZHat/CohomologicalDimension.lean:105`）⟹ `Nat.card (H1 zHat (ZMod n)) = n`。

（剩下的只是 `≃*` → `≃ₜ*` 的搬运，见 §3 的诚实边界。）

## 交付

| 声明 | 内容 |
|---|---|
| **`inflToVAddHom_injective`** | `h1ToVEquiv ∘ explicitMap1(商映射, id)` 单射 |
| **`inflToVKG_injective`** | ★★★★ **`H¹(Γ⧸I,ℤ/p) ↪ VKG`** |
| **`exists_ne_zero_VKG_of_quot`** | ★★★★ `(∃ c ∈ H¹(Γ⧸I,ℤ/p), c ≠ 0) ⟹ ∃ y ∈ VKG, y ≠ 0` |
| **`finrank_VKG_eq_one_of_quot`** | ★★★★★ **(甲1) 的新形态**：只需 `H¹(Γ⧸I,ℤ/p)` 非平凡 |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ## 1 `inflToVAddHom` 单射 -/

/-- ★★★★ **`h1ToVEquiv ∘ explicitMap1(商映射, id)` 单射**（两因子各自单）。

`KummerBridge.h1ToVEquiv` 是加性等价；`explicitMap1_quot_id_injective`（`Hyp758`）给另一因子。 -/
theorem inflToVAddHom_injective :
    Function.Injective (inflToVAddHom (F := F) (p := p)) := by
  have h1 : Function.Injective
      (KummerBridge.h1ToVEquiv (F := F) (p := p)).toAddMonoidHom :=
    (KummerBridge.h1ToVEquiv (F := F) (p := p)).injective
  have h2 : Function.Injective
      (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) (AbsoluteGaloisGroup F)
        (ZMod p) (inertiaLoc F).quotientMkContinuousMonoidHom
        (AddMonoidHom.id (ZMod p)) continuous_id (fun _ _ => rfl)) :=
    explicitMap1_quot_id_injective (F := F) (p := p)
  intro a b hab
  exact h2 (h1 (by simpa [inflToVAddHom] using hab))

/-! ## 2 `inflToVKG` 单射 -/

/-- ★★★★ **`H¹(Γ⧸I,ℤ/p) ↪ VKG`**（`inflToVKG` 单射）。

`inflToVKG` 是 `inflToVAddHom` 的 `codRestrict`，故取值后回到 `inflToVAddHom`。 -/
theorem inflToVKG_injective (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p) :
    Function.Injective (inflToVKG (F := F) (p := p) hp hpq) := by
  intro a b hab
  have h : inflToVAddHom (F := F) (p := p) a = inflToVAddHom (F := F) (p := p) b := by
    have h' := congrArg Subtype.val hab
    simpa [inflToVKG] using h'
  exact inflToVAddHom_injective (F := F) (p := p) h

/-! ## 3 (甲1) 的新形态 -/

/-- ★★★★ **`VKG` 非平凡 ⟸ `H¹(Γ⧸I,ℤ/p)` 非平凡**（`inflToVKG` 单射的直接后果）。 -/
theorem exists_ne_zero_VKG_of_quot (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p)
    (h0 : ∃ c : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p), c ≠ 0) :
    ∃ y : VKG F p (TauCeti.normalizedValuation F) hp, y ≠ 0 := by
  obtain ⟨c, hc⟩ := h0
  refine ⟨inflToVKG (F := F) (p := p) hp hpq c, ?_⟩
  intro h
  exact hc (inflToVKG_injective (F := F) (p := p) hp hpq (by
    rw [h, map_zero]))

/-- ★★★★★ **(甲1)：只需 `H¹(Γ⧸I,ℤ/p)` 非平凡** ⟹ `finrank VKG = 1`。

与 `Hyp777.finrank_VKG_eq_one_of_ne_zero` 复合；输入是**本战役里最便宜的一条非平凡性**。 -/
theorem finrank_VKG_eq_one_of_quot (hp : IsUnit (p : F)) (hpu : IsUnit (p : ↥𝒪[F]))
    (hpq : ¬ ringChar 𝓀[F] ∣ p)
    (h0 : ∃ c : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p), c ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) (VKG F p (TauCeti.normalizedValuation F) hp) = 1 :=
  finrank_VKG_eq_one_of_ne_zero (F := F) (p := p) hp hpu
    (exists_ne_zero_VKG_of_quot (F := F) (p := p) hp hpq h0)

end L20261018

#print axioms L20261018.inflToVAddHom_injective
#print axioms L20261018.inflToVKG_injective
#print axioms L20261018.exists_ne_zero_VKG_of_quot
#print axioms L20261018.finrank_VKG_eq_one_of_quot
