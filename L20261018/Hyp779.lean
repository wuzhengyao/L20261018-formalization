import Hyp778

/-!
# S74 R5：**`hcup` 的残余被重构为"一条单射性"** —— 线性 `F5` 是自由参数

## 关键观察（本轮的核心）

`Hyp774.tameResidueFacts_of_hd_cup_pi` 把 `prop:prelim-residue` 的无条件化压成
`hcup : ∀ y, d_F5 (cup y π) = y`，其中 `d_F5 = F5_uncond ∘ ∂²`、`F5_uncond` 是**某一具体**构造。

但 `tameResidueFacts_Galo_of_residueMap`（`Hyp342`）吃的 `d` 是**任意的**线性映射
`GaloBase.H2 F p →ₗ VKG`，只要 (i) `hd_infl`、(ii) `hd_cup_pi`。而
**`Hyp757.hd_infl_of_linear` 说 `hd_infl` 对任意线性的 `F5` 都成立**（与 `F5` 解耦）。

⟹ **`F5` 是自由参数。** 于是 `hcup` 等价于：

```
∃ F5 : H¹(Γ⧸I, H¹(I,μ_p)) →ₗ[ZMod p] VKG,  F5 (∂² (cup y π)) = y  ∀ y
```

而这由 `LinearMap.exists_leftInverse_of_injective` 给出，**不需要任何维数理论**
（`ZMod p` 是域）+ 一条单射性：

```
projLin : VKG →ₗ[ZMod p] H¹(Γ⧸I, H¹(I,μ_p)),   y ↦ ∂²(cup y π)
hcup ⟺ projLin 单射
```

## 为什么这是实质进展

* S74 R1–R4 的清单（甲1 一维／甲2 `H²` 一维／`Φ ≠ 0`／`∂² ≠ 0`／齐次性 (乙)／装配）**全部退出**——
  它们只是"围绕一个具体的 `F5` 做归一化"的产物。
* 残余变成**一条内蕴的单射性**：`ker (∂² ∘ cup(·,π)) = 0`。
  经 LES（`ker ∂² = im Inf₂`）与 `H²(Γ⧸I,μ_p)=0`，它等价于
  **`cup(a₀,π) ≠ 0`（`a₀` 生成 `VKG`）**，即**一致化元与不分歧类的 Hilbert 符号非零** ——
  这就是 `prop:prelim-residue`(1) 里真正的数学内容。

## 交付

| 声明 | 内容 |
|---|---|
| **`cupPiLin`** | `y ↦ cup ↑y (kummerClass π)` 作为线性映射 |
| **`projLin`** | ★★★★ `∂² ∘ cupPiLin : VKG →ₗ H¹(Γ⧸I, H¹(I,μ_p))`（**残余的精确载体**） |
| **`exists_leftInverse_of_injective`** | ★★★★ `projLin` 单 ⟹ 存在左逆线性 `F5` |
| **`injective_of_exists_leftInverse`** | 反向：存在左逆 ⟹ `projLin` 单 |
| ~~`tameResidueFacts_of_projLin_injective`~~ | ⚠ **未做成（R5、R6 两次）**：装配到 `Hyp342` 撞
**`whnf` 超时**（`maxHeartbeats 8e6`，且超时发生在**陈述层**的 elaboration，不在证明里）。
下一步的解法：把 `hinj` 写成**展开形式**（`∀ y, ∂²(cup y π) = 0 → y = 0`）以避开在陈述里出现 `projLin`。 |
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

/-! ## 1 `y ↦ cup y π` 是线性的 -/

/-- `y ↦ cup ↑y (kummerClass π)`：`VKG →ₗ H²`（`cup` 对第一个变量线性）。 -/
noncomputable def cupPiLin (hp : IsUnit (p : F)) (π : Fˣ) :
    VKG F p (TauCeti.normalizedValuation F) hp →ₗ[ZMod p] GaloBase.H2 F p where
  toFun y := GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
    (KummerBridge.kummerClass F p hp π)
  map_add' a b := by
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
  map_smul' c a := by
    simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-! ## 2 残余的精确载体：`projLin = ∂² ∘ cupPiLin` -/

/-- ★★★★ **`projLin : VKG →ₗ H¹(Γ⧸I, H¹(I,μ_p))`**，`y ↦ ∂²(cup y π)`。

`prop:prelim-residue`(1) 的无条件化 ⟺ 这条映射**单射**（§3）。 -/
noncomputable def projLin (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) (hp : IsUnit (p : F))
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    (π : Fˣ) :
    VKG F p (TauCeti.normalizedValuation F) hp →ₗ[ZMod p]
      H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p)) :=
  (AddMonoidHom.toZModLinearMap p (deltaTwoGaloBase' (F := F) p q hcop)).comp
    (cupPiLin (F := F) (p := p) hp π)

/-! ## 3 单射 ⟺ 存在左逆（`ZMod p` 是域，故只需泛性质） -/

/-- ★★★★ **`projLin` 单 ⟹ 存在线性左逆 `F5`**（`LinearMap.exists_leftInverse_of_injective`，
**不用维数理论**）。 -/
theorem exists_leftInverse_of_injective (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) (hp : IsUnit (p : F))
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    (π : Fˣ)
    (hinj : Function.Injective (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp π)) :
    ∃ F5 : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))
        →ₗ[ZMod p] VKG F p (TauCeti.normalizedValuation F) hp,
      F5.comp (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp π) = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.mpr hinj)

/-- 反向：存在左逆 ⟹ `projLin` 单。 -/
theorem injective_of_exists_leftInverse (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) (hp : IsUnit (p : F))
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    (π : Fˣ)
    (h : ∃ F5 : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))
        →ₗ[ZMod p] VKG F p (TauCeti.normalizedValuation F) hp,
      F5.comp (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp π)
        = LinearMap.id) :
    Function.Injective (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp π) := by
  obtain ⟨F5, hF5⟩ := h
  intro a b hab
  have h3 : F5 (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp π a) = a :=
    LinearMap.congr_fun hF5 a
  have h4 : F5 (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp π b) = b :=
    LinearMap.congr_fun hF5 b
  rw [← h3, ← h4]
  exact congrArg F5 hab

end L20261018

#print axioms L20261018.cupPiLin
#print axioms L20261018.projLin
#print axioms L20261018.exists_leftInverse_of_injective
#print axioms L20261018.injective_of_exists_leftInverse
