import L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame

/-!
# S43 R25（**B1 闭合**）：`Finite (H¹(I, μ_p))` —— 目标里的 B1 原话

## 目标原文

`PROMPT-S43` §2.6：**B1（支线）：`Finite (H¹(I, μ_p))`**。本件把它机检，**无条件**（除 `p ≠ char κ`）。

## 机制（本轮的**决定性简化**）

前一版计划要证 `Hom_cont(I_t, μ_p) ≅ ℤ/p`（GMS (7.3) 第二等号），需「相容原始根族 ＋
离散对数」。**但 `Finite` 只要单射**：

```
ζ 拓扑生成 M := ℤ̂^{(p')}(1)          （Hyp512）
⟹ 求值  ev : Hom_cont(M, μ_p) → μ_p,  f ↦ f ζ   是**单射**
     （f、g 在 ζ 上相等 ⟹ 在 `closedZpowers ζ = ⊤` 上相等：
        `{x | f x = g x}` 闭（T2 的等化子）且含 `zpowers ζ`，故含其闭包 ⊤）
⟹ Hom_cont(M, μ_p) ↪ μ_p ≅ ℤ/p        （有限 ⟹ 有限）
⟹ 沿 M ≅ I_t（`Hyp516`）与 I_t ≅ I（`Hyp519`，GMS (7.3) 第一等号）搬到 `I`
```

**副产品**：`Nat.card (Hom_cont(I, μ_p)) ≤ p` —— 即「1 维」的**上界**（精确等号仍需第二等号）。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`hom_cont_eval_injective`** | 求值 `f ↦ f ζ` 单射（等化子闭 ＋ `closedZpowers ζ = ⊤`） |
| **`finite_hom_cont_tameModel_zmod`** | `Finite (Hom_cont(M, μ_p))` |
| **`natCard_hom_cont_tameModel_zmod_le`** | `Nat.card ≤ p`（维数上界） |
| **`equivTameModelInertia`** | 沿 `M ≃ₜ* I_t` 搬运同态集 |
| **`finite_zmodDual_tameInertia`** | `Finite (Hom_cont(I_t, μ_p))` |
| **`finite_zmodDual_inertiaLoc`** | ★★★★★ **B1：`Finite (H¹(inertiaLoc, μ_p))`** |
| **`natCard_zmodDual_inertiaLoc_le`** | `Nat.card ≤ p`（战役载体上的维数上界） |

## 诚实边界

* 得到的是 **`Finite` ＋ `Nat.card ≤ p`**，**不是** `≅ ℤ/p`。精确等号（GMS (7.3) 第二等号）
  仍需「`{ker(Λ → μ_m)}` 是邻域基」或「相容原始根族 ＋ 离散对数」——见 `S43-STATUS.md` §1.8。
* **系数是平凡作用下的 `μ_p`**，不是 Kummer twist `μ_p(1)`。论文的 `H¹(I, μ_p)` 带 Galois 作用，
  那一条（`H¹(I, μ_p(1)) ≅ ℤ/p`，由 `res_I(π)` 生成）**仍未做**。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime]

/-- ★★★★ **求值 `f ↦ f ζ` 是单射**：`ζ` 拓扑生成 `M` 时，`f` 由 `f ζ` 决定。

证明：`{x | f x = g x}` 是闭集（T2 空间的等化子），含 `Subgroup.zpowers ζ`，
故含其拓扑闭包 `= closedZpowers ζ = ⊤`。 -/
theorem hom_cont_eval_injective (ζ : TameModel F) (hζ : closedZpowers ζ = ⊤) :
    Function.Injective
      (fun f : TameModel F →ₜ* Multiplicative (ZMod p) => f ζ) := by
  intro f g h
  refine ContinuousMonoidHom.ext fun x => ?_
  -- `(zpowers ζ).topologicalClosure = ⊤`
  have htop : (Subgroup.zpowers ζ).topologicalClosure = ⊤ := by
    rw [← closedZpowers_def]; exact hζ
  set T : Subgroup (TameModel F) :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := fun hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := fun hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_inv, map_inv, hx] } with hTdef
  have hclosedT : IsClosed (T : Set (TameModel F)) := by
    rw [hTdef]
    exact isClosed_eq f.continuous_toFun g.continuous_toFun
  have hsub : Subgroup.zpowers ζ ≤ T := by
    rintro _ ⟨n, rfl⟩
    show f (ζ ^ n) = g (ζ ^ n)
    rw [map_zpow, map_zpow]
    rw [show f ζ = g ζ from h]
  have hcl : (Subgroup.zpowers ζ).topologicalClosure ≤ T :=
    Subgroup.topologicalClosure_minimal _ hsub hclosedT
  exact hcl (htop ▸ Subgroup.mem_top x)

/-- ★★★★★ **`Hom_cont(M, μ_p)` 有限**（单射进 `μ_p ≅ ℤ/p`）。 -/
theorem finite_hom_cont_tameModel_zmod (ζ : TameModel F) (hζ : closedZpowers ζ = ⊤) :
    Finite (TameModel F →ₜ* Multiplicative (ZMod p)) :=
  Finite.of_injective _ (hom_cont_eval_injective p ζ hζ)

/-- ★★★★ **维数上界**：`Nat.card (Hom_cont(M, μ_p)) ≤ p`。 -/
theorem natCard_hom_cont_tameModel_zmod_le (ζ : TameModel F) (hζ : closedZpowers ζ = ⊤) :
    Nat.card (TameModel F →ₜ* Multiplicative (ZMod p)) ≤ p := by
  have hle := Nat.card_le_card_of_injective _
    (hom_cont_eval_injective (F := F) p ζ hζ)
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
  rwa [hcard] at hle

/-- 沿 `M ≃ₜ* I_t`（`Hyp516` 的 `tameModelEquivTameInertia`）搬运同态集。 -/
noncomputable def equivTameModelInertia :
    (TameModel F →ₜ* Multiplicative (ZMod p)) ≃
      (↥(tameInertia F) →ₜ* Multiplicative (ZMod p)) where
  toFun f := f.comp
    ⟨(tameModelEquivTameInertia (K := F)).symm.toMulEquiv.toMonoidHom,
      (tameModelEquivTameInertia (K := F)).symm.continuous_toFun⟩
  invFun g := g.comp
    ⟨(tameModelEquivTameInertia (K := F)).toMulEquiv.toMonoidHom,
      (tameModelEquivTameInertia (K := F)).continuous_toFun⟩
  left_inv f := ContinuousMonoidHom.ext fun x => by simp
  right_inv g := ContinuousMonoidHom.ext fun x => by simp

/-- ★★★★★ **`Finite (Hom_cont(I_t, μ_p))`**。 -/
theorem finite_zmodDual_tameInertia :
    Finite (↥(tameInertia F) →ₜ* Multiplicative (ZMod p)) := by
  -- 取模型的拓扑生成元（`Hyp512`）
  obtain ⟨ζ, hζc⟩ := exists_generator_primeToPTateModule F
  have hζ : closedZpowers ζ = ⊤ := by
    rw [closedZpowers_def, Subgroup.zpowers_eq_closure]
    exact hζc
  exact (equivTameModelInertia (F := F) p).finite_iff.mp
    (finite_hom_cont_tameModel_zmod (F := F) p ζ hζ)

/-- ★★★★★ **B1：`Finite (H¹(inertiaLoc, μ_p))`** —— 战役载体，**无条件**（除 `p ≠ char κ`）。

（`PROMPT-S43` §2.6 的 B1 原话。） -/
theorem finite_zmodDual_inertiaLoc (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hpq : p ≠ q) :
    Finite (↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p)) :=
  (InertiaTame.finite_zmodDual_inertiaLoc_iff (F := F) p q hpq).mpr
    (finite_zmodDual_tameInertia (F := F) p)

/-- ★★★★ **维数上界（战役载体）**：`Nat.card (H¹(inertiaLoc, μ_p)) ≤ p`。 -/
theorem natCard_zmodDual_inertiaLoc_le (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hpq : p ≠ q) :
    Nat.card (↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p)) ≤ p := by
  obtain ⟨ζ, hζc⟩ := exists_generator_primeToPTateModule F
  have hζ : closedZpowers ζ = ⊤ := by
    rw [closedZpowers_def, Subgroup.zpowers_eq_closure]
    exact hζc
  -- 经由 `I ≃ I_t ≃ M` 的同态集等价
  have hbij : Nat.card (↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p))
      = Nat.card (TameModel F →ₜ* Multiplicative (ZMod p)) :=
    (Nat.card_congr (InertiaTame.equivInertiaLocInertia (F := F) p)).trans
      ((Nat.card_congr (InertiaTame.equivTameInertia (F := F) p q hpq).symm).trans
        (Nat.card_congr (equivTameModelInertia (F := F) p).symm))
  rw [hbij]
  exact natCard_hom_cont_tameModel_zmod_le (F := F) p ζ hζ

end L20261018

#print axioms L20261018.hom_cont_eval_injective
#print axioms L20261018.finite_hom_cont_tameModel_zmod
#print axioms L20261018.natCard_hom_cont_tameModel_zmod_le
#print axioms L20261018.finite_zmodDual_tameInertia
#print axioms L20261018.finite_zmodDual_inertiaLoc
#print axioms L20261018.natCard_zmodDual_inertiaLoc_le
