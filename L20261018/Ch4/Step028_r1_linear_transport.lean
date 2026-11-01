import L20261018.Ch4.Step027_residue_span_bot_skeleton

/-!
# R1168（**第 5 项路径 1：(R1) 沿线性等价运输 —— 填 `Hyp285.hR1` 的抽象工具**）

## 本轮做什么

`Hyp285.exists_henselResidueData_of_le_range` 需要 (R1)：
`Injective (residuePhi (kummerCupPairing ζ hζ).cup 1 1 (valH1LinearGen v hp) ((π)))`
（**`muNRep` 载体**）。而 `Hyp201.residuePhi_injective_of_norm_form` 已给出同一事实在
**`GaloBase` 载体**（`ZMod p` 系数）上的版本，且其假设**正是论文的 Hensel 层级**
（`[HenselianRing ↥𝒪[F] (maximalIdeal)]`，**无完备性**）。

⟹ 只需把单射性**沿两载体的线性等价运输**。本轮机检这个抽象工具：

```
Φ : W → H2   （来源载体）
Φ' : W' → H2'（目标载体）
e : W ≃ₗ W'，e₂ : H2 ≃ₗ H2'，且 e₂ ∘ Φ = Φ' ∘ e   （交换方块）
Φ 单射 ⟹ Φ' 单射
```

**具体化所需的两个对齐等式**（下一轮）：
* `Θ₁ ((π)_muNRep) = (π)_Galo`（Kummer 类的一致性，`Hyp156.theta1_free_kummerClass` 类）；
* `val_Galo ∘ Θ₁ = val_exp`（`Hyp162.valLin_eq_valLinOf_normalizedValuation` 类）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`injective_of_comp_eq`** | ★★★★ **`Φ` 单射沿线性等价运输到 `Φ'`**（交换方块 `e₂ ∘ Φ = Φ' ∘ e`） |
| **`residuePhi_injective_transport`** | ★★★★ 同上，`residuePhi` 专用形态 |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k : Type*} [Field k]

/-- ★★★★ **`Φ` 的单射性沿线性等价运输**：若 `e₂ ∘ Φ = Φ' ∘ e`（`e`／`e₂` 为线性等价），
则 `Φ` 单射 ⟹ `Φ'` 单射。 -/
theorem injective_of_comp_eq
    {W : Type*} [AddCommGroup W] [Module k W]
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {H2 : Type*} [AddCommGroup H2] [Module k H2]
    {H2' : Type*} [AddCommGroup H2'] [Module k H2']
    (Φ : W →ₗ[k] H2) (Φ' : W' →ₗ[k] H2')
    (e : W ≃ₗ[k] W') (e₂ : H2 ≃ₗ[k] H2')
    (hsq : e₂.toLinearMap.comp Φ = Φ'.comp e.toLinearMap)
    (h : Function.Injective Φ) : Function.Injective Φ' := by
  intro x y hxy
  rw [← e.apply_symm_apply x, ← e.apply_symm_apply y]
  congr 1
  apply h
  have hx := LinearMap.congr_fun hsq (e.symm x)
  have hy := LinearMap.congr_fun hsq (e.symm y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] at hx hy
  apply e₂.injective
  rw [hx, hy, hxy]

variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {cup : V →ₗ[k] V →ₗ[k] H2} {val : V →ₗ[k] k} {π : V}

/-- ★★★★ **`residuePhi` 的单射性运输**（`Φ = ∪(·,π)|_{ker v̄}` 的专用形态）。

具体化时 `e` 取两载体在 `ker v̄` 上的等价、`e₂` 取 `H²` 的等价，交换方块取
`Hyp145.cup_compat_theta`（`hcup`）／`Hyp156.cup_compat_theta_free`。 -/
theorem residuePhi_injective_transport
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {H2' : Type*} [AddCommGroup H2'] [Module k H2']
    (cup' : V' →ₗ[k] V' →ₗ[k] H2') (val' : V' →ₗ[k] k) (π' : V')
    (e : ↥(LinearMap.ker val) ≃ₗ[k] ↥(LinearMap.ker val')) (e₂ : H2 ≃ₗ[k] H2')
    (hsq : e₂.toLinearMap.comp (residuePhi cup val π)
      = (residuePhi cup' val' π').comp e.toLinearMap)
    (h : Function.Injective (residuePhi cup val π)) :
    Function.Injective (residuePhi cup' val' π') :=
  injective_of_comp_eq _ _ e e₂ hsq h

end L20261018

#print axioms L20261018.injective_of_comp_eq
#print axioms L20261018.residuePhi_injective_transport
