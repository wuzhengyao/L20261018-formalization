import L20261018.Ch2.Hensel.ResidueMap.Step020_cup_pi_nonzero_injective

/-!
# R980：**`res` 与 `tame_u_pi` 一起解除** —— `HenselResidueData` 在真实载体上非空

（R979 的三条修法已落实：① `Φ` 提成**顶层 `def`** `cupPi`／`kerCupPi`；
② 用 `Submodule.sub_mem`；③ `exists_leftInverse_of_injective` 收 **`f.ker = ⊥`**。）

`tame_u_pi : ∀ y ∈ \ker, res (cup y π) = y` 就是「`res` 是 `Φ := cup (·) π` 的**左逆**」。
本文件：`Φ` 在 `\ker\bar v` 上**单射**（`Hyp137` 给 `Φ ≠ 0`，`Hyp134` 给 `\ker` ≤ 1 维），
故左逆存在 ⟹ **`res` 与 `tame_u_pi` 同时解除**。

## ⚠ 载体身份（L12／L16，硬纪律）

所得 `res` 是 `Φ` 的一个左逆；**不是本文件"算出"的论文 `∂₂`**。
本文件给的是 **`HenselResidueData` 的非空见证（真实载体）** = L1＋L10① 的非空实例义务。
**加强（下一轮）**：若 `finrank H² ≤ 1`，则 `Φ` 是同构、左逆**唯一**，
此时 `res = Φ⁻¹` **就是**论文 `∂₂` 在 `im Φ` 上的限制 —— 含糊性消失。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **`Φ := cup (·) (π)` 作为 `V` 上的线性映射。** -/
noncomputable def cupPi (hp : IsUnit (p : F)) (π : Fˣ) :
    GaloBase.V F p →ₗ[ZMod p] GaloBase.H2 F p where
  toFun x := GaloBase.cup (K := F) (p := p) x (KummerBridge.kummerClass F p hp π)
  map_add' := by intro a b; simp [map_add]
  map_smul' := by intro c a; simp [map_smul]

@[simp]
theorem cupPi_apply (hp : IsUnit (p : F)) (π : Fˣ) (x : GaloBase.V F p) :
    cupPi (F := F) (p := p) hp π x
      = GaloBase.cup (K := F) (p := p) x (KummerBridge.kummerClass F p hp π) := rfl

/-- **`Φ` 限制到 `\ker\bar v`**（左逆的原料）。 -/
noncomputable def kerCupPi (hp : IsUnit (p : F)) (π : Fˣ) :
    ↥(LinearMap.ker (valLin F p hp)) →ₗ[ZMod p] GaloBase.H2 F p :=
  (cupPi (F := F) (p := p) hp π).comp (LinearMap.ker (valLin F p hp)).subtype

@[simp]
theorem kerCupPi_apply (hp : IsUnit (p : F)) (π : Fˣ)
    (y : ↥(LinearMap.ker (valLin F p hp))) :
    kerCupPi (F := F) (p := p) hp π y
      = GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
          (KummerBridge.kummerClass F p hp π) := rfl

/-- **`Φ` 在 `\ker\bar v` 上单射**：`Φ ≠ 0`（`Hyp137`）＋ `\ker` 至多 1 维（`Hyp134`）。 -/
theorem kerCupPi_injective (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) {γ : ↥(LinearMap.ker (valLin F p hp))}
    (hγ : kerCupPi (F := F) (p := p) hp π γ ≠ 0) :
    Function.Injective (kerCupPi (F := F) (p := p) hp π) := by
  have hpoint : ∀ w : ↥(LinearMap.ker (valLin F p hp)),
      kerCupPi (F := F) (p := p) hp π w = 0 → w = 0 := by
    intro w hw
    rcases ker_dependent (F := F) (p := p) hp hπ hpu (w : GaloBase.V F p)
      (γ : GaloBase.V F p) w.2 γ.2 with hdep | hdep
    · -- `w = c • γ`
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdep
      have hc' : c • γ = w := Subtype.ext hc
      have hyc : c • (kerCupPi (F := F) (p := p) hp π γ) = 0 := by
        rw [← map_smul, hc', hw]
      have hc0 : c = 0 := (smul_eq_zero.mp hyc).resolve_right hγ
      rw [← hc', hc0, zero_smul]
    · -- `γ = c • w`
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdep
      have hc' : c • w = γ := Subtype.ext hc
      exact absurd (by rw [← hc', map_smul, hw, smul_zero] : kerCupPi (F := F) (p := p) hp π γ = 0) hγ
  intro y z hyz
  have hyz' : y - z = 0 := hpoint (y - z) (by rw [map_sub, hyz, sub_self])
  exact sub_eq_zero.mp hyz'

/-- **`HenselResidueData` 在 `GaloBase` 载体上非空**（L1＋L10① 的非空实例义务）。

`VK := ↥(\ker\bar v)`；`res` 取 `kerCupPi` 的任一左逆；其余 9 个字段全部由定理供给。
**无任何驯符号假设。** ⚠ `res` 与论文 `∂₂` 的同一性未证（见文件头）。 -/
theorem henselResidueData_nonempty (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    Nonempty (HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p)
      ↥(LinearMap.ker (valLin F p hp)) (GaloBase.cup (K := F) (p := p))) := by
  classical
  obtain ⟨γ, hγ⟩ :=
    exists_cup_pi_ne_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu (a1 := a1) (a2 := a2) hne
  have hγ' : kerCupPi (F := F) (p := p) hp π γ ≠ 0 := by
    rw [kerCupPi_apply]
    exact hγ
  have hinj := kerCupPi_injective (F := F) (p := p) hp hp2 (hπ := hπ) hpu hγ'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (kerCupPi (F := F) (p := p) hp π) (LinearMap.ker_eq_bot.mpr hinj)
  have hleft : ∀ y : ↥(LinearMap.ker (valLin F p hp)),
      g (kerCupPi (F := F) (p := p) hp π y) = y := by
    intro y
    have h := congrFun (congrArg DFunLike.coe hg) y
    simpa [LinearMap.comp_apply] using h
  refine ⟨{ res := g
            val := valLin F p hp
            infl := (LinearMap.ker (valLin F p hp)).subtype
            inj_infl := Subtype.val_injective
            val_infl := fun y => y.2
            pi := KummerBridge.kummerClass F p hp π
            val_pi := valLin_pi (F := F) (p := p) hp hπ
            split := fun x => decomp_mem_ker (valLin F p hp)
              (KummerBridge.kummerClass F p hp π) (valLin_pi (F := F) (p := p) hp hπ) x
            tame_uu := fun y z => by
              show g (GaloBase.cup (K := F) (p := p) ((y : GaloBase.V F p))
                ((z : GaloBase.V F p))) = 0
              rw [ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y z, map_zero]
            tame_u_pi := fun y => by
              show g (kerCupPi (F := F) (p := p) hp π y) = y
              exact hleft y
            tame_pi_u := fun κ hκ z =>
              tame_pi_u_of (GaloBase.cup (K := F) (p := p))
                (fun x y => GaloBase.cup_skew (K := F) (p := p) x y) (valLin F p hp)
                (KummerBridge.kummerClass F p hp π) (valLin_pi (F := F) (p := p) hp hπ) g
                (fun y z => by
                  show g (GaloBase.cup (K := F) (p := p) ((y : GaloBase.V F p))
                    ((z : GaloBase.V F p))) = 0
                  rw [ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y z, map_zero])
                (fun y => by
                  show g (kerCupPi (F := F) (p := p) hp π y) = y
                  exact hleft y)
                κ hκ z }⟩

end L20261018
#print axioms L20261018.kerCupPi_injective
#print axioms L20261018.henselResidueData_nonempty
