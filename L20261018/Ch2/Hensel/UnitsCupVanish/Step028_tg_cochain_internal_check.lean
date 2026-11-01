import L20261018.Ch2.Hensel.UnitsCupVanish.Step027_tg_additive_component

/-!
# S39 第 18 轮（B 第 14 步）：**`tg` 余链的内在校验**（`Hyp444`）

## 本轮两件

### 1. 截面无关性（`tgCocycle` 不依赖截面选择）

`Hyp442` 用固定截面 `S` 定义了 `tgCocycle`。NSW 的 `tg` 本身**不依赖截面**
（原文：「`y : G → A` 用**任意**连续截面 `s` 构造」）。本件把这条做成机检：

```
tgCocycle H S y … q₁ q₂ = tgCocycle H S' y … q₁ q₂      （两个不同截面）
```

由 `d1_tgLift_quot_compat`：`S.s q` 与 `S'.s q` 同陪集（两者 `mk` 都等于 `q`）。

### 2. 余链条件（`∂y` 在 `G/H` 上是上闭链）

`prop-1.6.6` 说 `∂y`「may be viewed as cocycles in `Z²(G/H, A^H)`」。
本件机检 `d²_{G/H}(tgCocycle) = 0`（系数 `A^H`，`G/H`-作用）。

**已确认的前提**：`DistribMulAction (G ⧸ H) ↥(FixedPoints.addSubgroup H A)` 实例**存在**
（`infer_instance` 直接过）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgSecIndep

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (y : G → A)
variable (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
variable (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)

/-- ★★★★ **截面无关性**：两个不同截面给出的 `tgCocycle` 逐点相等。

⟹ NS​W 的 `tg` 是**内在**的（不依赖 `s` 的选择），与原文一致。 -/
theorem tgCocycle_sec_indep (S S' : TgSection H) (q₁ q₂ : G ⧸ H) :
    tgCocycle H S y hii hiii q₁ q₂ = tgCocycle H S' y hii hiii q₁ q₂ := by
  apply Subtype.ext
  show d1 G A y (S.s q₁, S.s q₂) = d1 G A y (S'.s q₁, S'.s q₂)
  have h₁ : (QuotientGroup.mk (S.s q₁) : G ⧸ H) = QuotientGroup.mk (S'.s q₁) := by
    rw [S.sec q₁, S'.sec q₁]
  have h₂ : (QuotientGroup.mk (S.s q₂) : G ⧸ H) = QuotientGroup.mk (S'.s q₂) := by
    rw [S.sec q₂, S'.sec q₂]
  exact d1_tgLift_quot_compat H y hii hiii h₁ h₂

end TgSecIndep

section TgCocycleCond

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (y : G → A)
variable (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
variable (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)

/-- ★★★★★ **`∂y` 在 `G/H` 上是上闭链**（NSW「viewed as cocycles in `Z²(G/H, A^H)`」）。

`d²_{G/H}(tgCocycle) = 0`，系数取值在 `A^H`，`G/H`-作用。
证明：把 `S.s (qᵢqⱼ)` 换成 `S.s qᵢ * S.s qⱼ`（同陪集，用 `d1_tgLift_quot_compat`），
即归到 `G` 上的 `d²(d¹y) = 0`。**关键事实**：`G/H` 对 `A^H` 的作用由代表的 `G`-作用给出（`rfl`）。 -/
theorem tgCocycle_cocycle (S : TgSection H) (q₁ q₂ q₃ : G ⧸ H) :
    d2 (G ⧸ H) ↥(FixedPoints.addSubgroup H A)
      (fun p : (G ⧸ H) × (G ⧸ H) => tgCocycle H S y hii hiii p.1 p.2) (q₁, q₂, q₃) = 0 := by
  have h0 : d2 G A (d1 G A y) ((S.s q₁), (S.s q₂), (S.s q₃)) = 0 := by
    rw [d2_comp_d1_apply]
    simp
  rw [d2_apply] at h0
  rw [d2_apply]
  have hcoe : ∀ (q : G ⧸ H) (a : ↥(FixedPoints.addSubgroup H A)),
      ((q • a : ↥(FixedPoints.addSubgroup H A)) : A) = (S.s q) • (a : A) := by
    intro q a
    conv_lhs => rw [show q = QuotientGroup.mk (S.s q) from (S.sec q).symm]
    rfl
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, AddSubgroup.coe_zero, tgCocycle]
  rw [hcoe]
  show (S.s q₁) • (d1 G A y (S.s q₂, S.s q₃))
      - d1 G A y (S.s (q₁ * q₂), S.s q₃) + d1 G A y (S.s q₁, S.s (q₂ * q₃))
      - d1 G A y (S.s q₁, S.s q₂) = 0
  have e₁ : (QuotientGroup.mk (S.s (q₁ * q₂)) : G ⧸ H)
      = QuotientGroup.mk (S.s q₁ * S.s q₂) := by
    rw [S.sec (q₁ * q₂), QuotientGroup.mk_mul H, S.sec q₁, S.sec q₂]
  have e₂ : (QuotientGroup.mk (S.s (q₂ * q₃)) : G ⧸ H)
      = QuotientGroup.mk (S.s q₂ * S.s q₃) := by
    rw [S.sec (q₂ * q₃), QuotientGroup.mk_mul H, S.sec q₂, S.sec q₃]
  have k₁ : d1 G A y (S.s (q₁ * q₂), S.s q₃) = d1 G A y (S.s q₁ * S.s q₂, S.s q₃) :=
    d1_tgLift_quot_compat H y hii hiii e₁
      (rfl : (QuotientGroup.mk (S.s q₃) : G ⧸ H) = QuotientGroup.mk (S.s q₃))
  have k₂ : d1 G A y (S.s q₁, S.s (q₂ * q₃)) = d1 G A y (S.s q₁, S.s q₂ * S.s q₃) :=
    d1_tgLift_quot_compat H y hii hiii
      (rfl : (QuotientGroup.mk (S.s q₁) : G ⧸ H) = QuotientGroup.mk (S.s q₁)) e₂
  rw [k₁, k₂]
  exact h0

end TgCocycleCond

end L20261018

#print axioms L20261018.tgCocycle_sec_indep
#print axioms L20261018.tgCocycle_cocycle
