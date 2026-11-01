import L20261018.Hyp444

/-!
# S39 第 19 轮（B 第 15 步）：**第一段正合的机检核心**（`Hyp445`）

## 原文（NSW `prop-1.6.7` 证明，`raw/NSW2020.tex:2302`，逐字）

> **Exactness at `H¹(H,A)^{G/H}`**: If `y ∈ 𝒵¹(G,A)` and `x = res y` represents a class `[x]`
> in `H¹(H,A)^{G/H}`, then `tg[x] = [∂y] = 0`, i.e. `im(res) ⊆ ker(tg)`.

即：**从 `G` 来的类在 `tg` 下为零**。

## 本件

| 件 | 内容 |
|---|---|
| **`tgCocycle_eq_zero_of_cocycle`** | ★★★★★ 若 `y` 本身是 `G` 上的 1-上闭链（`d¹y = 0`），则 `tgCocycle y = 0` |
| **`tgLift_hright_sub`** | `∂y`、`∂y'` 对第二槽右 `H`-不变 ⟹ `∂(y−y')` 亦然（`z = y − y'` 下降的前置） |
| **`tgLift_hleft_sub`** | 同上，第一槽 |
| **`tgDescend`** | ★★★★ `z` 下降为 `G/H → A^H`（`z|_H = 0` ＋ `∂z` 双不变 ⟹ 用 `tgLift_z_mem_fixed`） |

⟹ `tg[x] = 0`（`x` 来自 `G`），且 `z = y − y'` 的下降件已就位 ——
下一轮即得 `tg[y] − tg[y'] = ∂(下降 z)`（`∈ B²`），即完整良定义性。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgExact

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]

/-- ★★★★★ **`im(res) ⊆ ker(tg)` 的定量核心**：若 `y : G → A` 是 `G` 上的 1-上闭链，
则 `tgCocycle y = 0`（NSW `:2302`「`tg[x] = [∂y] = 0`」）。 -/
theorem tgCocycle_eq_zero_of_cocycle (S : TgSection H) (y : G → A)
    (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
    (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)
    (hzero : d1 G A y = 0) (q₁ q₂ : G ⧸ H) :
    tgCocycle H S y hii hiii q₁ q₂ = 0 := by
  apply Subtype.ext
  show d1 G A y (S.s q₁, S.s q₂) = ((0 : ↥(FixedPoints.addSubgroup H A)) : A)
  rw [hzero]
  rfl

/-- `d¹` 的线性性：`d¹(y − y') = d¹y − d¹y'`（逐点）。 -/
theorem d1_sub_apply (y y' : G → A) (σ₁ σ₂ : G) :
    d1 G A (y - y') (σ₁, σ₂) = d1 G A y (σ₁, σ₂) - d1 G A y' (σ₁, σ₂) := by
  rw [d1_apply, d1_apply, d1_apply]
  simp only [Pi.sub_apply, smul_sub]
  abel

/-- ★★★ `∂y`、`∂y'` 对第二槽右 `H`-不变 ⟹ `∂(y−y')` 亦然。 -/
theorem tgLift_hright_sub {y y' : G → A}
    (h₁ : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A y (σ₁, σ₂ * (τ : G)) = d1 G A y (σ₁, σ₂))
    (h₂ : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A y' (σ₁, σ₂ * (τ : G)) = d1 G A y' (σ₁, σ₂))
    (σ₁ σ₂ : G) (τ : H) :
    d1 G A (y - y') (σ₁, σ₂ * (τ : G)) = d1 G A (y - y') (σ₁, σ₂) := by
  rw [d1_sub_apply, d1_sub_apply, h₁, h₂]

/-- ★★★ `∂y`、`∂y'` 对第一槽左 `H`-不变 ⟹ `∂(y−y')` 亦然。 -/
theorem tgLift_hleft_sub {y y' : G → A}
    (h₁ : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A y ((τ : G) * σ₁, σ₂) = d1 G A y (σ₁, σ₂))
    (h₂ : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A y' ((τ : G) * σ₁, σ₂) = d1 G A y' (σ₁, σ₂))
    (σ₁ σ₂ : G) (τ : H) :
    d1 G A (y - y') ((τ : G) * σ₁, σ₂) = d1 G A (y - y') (σ₁, σ₂) := by
  rw [d1_sub_apply, d1_sub_apply, h₁, h₂]

/-- ★★★★ **`z` 沿 `G → G/H` 下降为 `A^H`-值函数**（`z|_H = 0` ＋ `∂z` 双不变）。 -/
noncomputable def tgDescend (S : TgSection H) (z : G → A)
    (hzH : ∀ τ : H, z (τ : G) = 0)
    (hleft : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A z ((τ : G) * σ₁, σ₂) = d1 G A z (σ₁, σ₂))
    (hright : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A z (σ₁, σ₂ * (τ : G)) = d1 G A z (σ₁, σ₂))
    (q : G ⧸ H) : ↥(FixedPoints.addSubgroup H A) :=
  ⟨z (S.s q), fun τ => tgLift_z_mem_fixed H z hzH hleft hright (S.s q) τ⟩

end TgExact

end L20261018

#print axioms L20261018.d1_sub_apply
#print axioms L20261018.tgCocycle_eq_zero_of_cocycle
#print axioms L20261018.tgLift_hright_sub
#print axioms L20261018.tgLift_hleft_sub
#print axioms L20261018.tgDescend
