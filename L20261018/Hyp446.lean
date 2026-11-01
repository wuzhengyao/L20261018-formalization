import L20261018.Hyp445

/-!
# S39 第 20 轮（B 第 16 步）：**完整良定义性**（`Hyp446`）

## 原文（NSW `prop-1.6.6` 末段，`raw/NSW2020.tex:2266–2272`）

> Therefore `∂y` and `∂y'` … **differ by the coboundary `∂z ∈ B²(G/H,A^H)`**,
> i.e. define the same cohomology class in `H²(G/H,A^H)`.

## 本件

对同一 `x` 的两支提升 `y, y'`（`z = y − y'`，`z|_H = 0`，`∂z` 双不变），机检

```
tg[y](q₁,q₂) − tg[y'](q₁,q₂) = ∂_{G/H}(tgDescend z)(q₁,q₂)
```

即 **`tg[y] − tg[y'] ∈ B²(G/H, A^H)`** —— `tg` 在上同调层良定义。

| 件 | 内容 |
|---|---|
| **`tgLift_z_quot_eq`** | ★★★ `z` 右 `H`-不变 ⟹ 同陪集的两个代表给同一 `z` 值 |
| **`coe_quot_smul`** | `↑(q • a) = (s q) • ↑a`（`G/H`-作用 = 代表的 `G`-作用） |
| **`tgCocycle_sub_eq`** | ★★★★★ 完整良定义性 |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgWellDef

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]

/-- ★★★ **同陪集代表给同一 `z` 值**（在 `z` 右 `H`-不变的前提下）。 -/
theorem tgLift_z_quot_eq (z : G → A)
    (hzH : ∀ τ : H, z (τ : G) = 0)
    (hright : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A z (σ₁, σ₂ * (τ : G)) = d1 G A z (σ₁, σ₂))
    {σ σ' : G} (h : (QuotientGroup.mk σ : G ⧸ H) = QuotientGroup.mk σ') :
    z σ' = z σ := by
  have hinv := tgLift_z_right_invariant H z hzH hright
  have hm : σ⁻¹ * σ' ∈ H := (QuotientGroup.eq).mp h
  have hdec : σ' = σ * ((⟨σ⁻¹ * σ', hm⟩ : H) : G) := by
    show σ' = σ * (σ⁻¹ * σ')
    group
  rw [hdec]
  exact hinv σ _

/-- `↑(q • ⟨a,_⟩) = (S.s q) • a`（`G/H`-作用就是代表的 `G`-作用）。 -/
theorem coe_quot_smul' (S : TgSection H) (q : G ⧸ H) (a : A)
    (ha : ∀ τ : H, (τ : G) • a = a) :
    ((q • (⟨a, ha⟩ : ↥(FixedPoints.addSubgroup H A)) : ↥(FixedPoints.addSubgroup H A)) : A)
      = (S.s q) • a := by
  conv_lhs => rw [show q = QuotientGroup.mk (S.s q) from (S.sec q).symm]
  rfl

/-- `↑(q • a) = (S.s q) • ↑a`（`G/H`-作用就是代表的 `G`-作用）。 -/
theorem coe_quot_smul (S : TgSection H) (q : G ⧸ H) (a : ↥(FixedPoints.addSubgroup H A)) :
    ((q • a : ↥(FixedPoints.addSubgroup H A)) : A) = (S.s q) • (a : A) := by
  conv_lhs => rw [show q = QuotientGroup.mk (S.s q) from (S.sec q).symm]
  rfl

variable (S : TgSection H)

/-- ★★★★★ **完整良定义性**：同一 `x` 的两支提升给出的 `tg` 差一个上边缘。

`tg[y](q₁,q₂) − tg[y'](q₁,q₂) = ∂_{G/H}(tgDescend z)(q₁,q₂)`，其中 `z = y − y'`。 -/
theorem tgCocycle_sub_eq (y y' : G → A)
    (hii₁ : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
    (hiii₁ : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)
    (hii₂ : ∀ (σ : G) (τ : H), y' (σ * (τ : G)) = y' σ + σ • y' (τ : G))
    (hiii₂ : ∀ (σ : G) (τ : H), y' ((τ : G) * σ) = y' (τ : G) + (τ : G) • y' σ)
    (hzH : ∀ τ : H, (y - y') (τ : G) = 0)
    (hleft : ∀ (σ₁ σ₂ : G) (τ : H),
      d1 G A (y - y') ((τ : G) * σ₁, σ₂) = d1 G A (y - y') (σ₁, σ₂))
    (hright : ∀ (σ₁ σ₂ : G) (τ : H),
      d1 G A (y - y') (σ₁, σ₂ * (τ : G)) = d1 G A (y - y') (σ₁, σ₂))
    (q₁ q₂ : G ⧸ H) :
    tgCocycle H S y hii₁ hiii₁ q₁ q₂ - tgCocycle H S y' hii₂ hiii₂ q₁ q₂
      = d1 (G ⧸ H) ↥(FixedPoints.addSubgroup H A)
          (fun q => tgDescend H S (y - y') hzH hleft hright q) (q₁, q₂) := by
  apply Subtype.ext
  rw [d1_apply]
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, tgCocycle, tgDescend]
  rw [coe_quot_smul' H S q₁ ((y - y') (S.s q₂))
    (fun τ => tgLift_z_mem_fixed H (y - y') hzH hleft hright (S.s q₂) τ)]
  rw [← d1_sub_apply, d1_apply]
  -- 目标：`s₁•z(s₂) − z(s₁s₂) + z(s₁) = s₁•z(s₂) − z(S.s(q₁q₂)) + z(s₁)`
  have hz : (y - y') (S.s (q₁ * q₂)) = (y - y') (S.s q₁ * S.s q₂) := by
    apply tgLift_z_quot_eq H (y - y') hzH hright
    rw [S.sec (q₁ * q₂), QuotientGroup.mk_mul H, S.sec q₁, S.sec q₂]
  rw [hz]

end TgWellDef

end L20261018

#print axioms L20261018.tgLift_z_quot_eq
#print axioms L20261018.coe_quot_smul
#print axioms L20261018.coe_quot_smul'
#print axioms L20261018.tgCocycle_sub_eq
