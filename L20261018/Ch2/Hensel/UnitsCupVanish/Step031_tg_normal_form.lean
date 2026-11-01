import L20261018.Ch2.Hensel.UnitsCupVanish.Step030_tg_well_defined_complete

/-!
# S39 第 21 轮（B 第 17 步）：**`tg` 的正规映射形式**（`Hyp447`）

## 目标（第 5d 项）

把 `tg` 装成可用对象。**不触碰** TauCeti `H2`（`Z²/B²` 商）的装配细节，
而是给出 `tg` 在 `G/H`-**余链层**的正规形式：

```
tgYs  x        := Classical.choose (exists_tgLift x)          -- 正规提升 y（`G → A`）
tgMap  x q₁ q₂ := tgCocycle tgYs … q₁ q₂                      -- `G/H × G/H → A^H`
```

**接口约定**：`exists_tgLift` 的输入是 `x : G → A`，但其条件 `hx` 只约束 `x` 在 `H` 上的值，
故从 `H¹(H,A)` 来的类只需任取一个到 `G` 的延拓即可（延拓方式不影响结果）。

这是**第 8 项直接需要的形状**（在具体类 `(u)`、`(π)` 上求值 `tg`）。

| 件 | 内容 |
|---|---|
| **`tgYs`** | 正规提升 `y`（`Classical.choose`，来自 `exists_tgLift`） |
| **`tgYs_one`／`tgYs_restrict`／`tgYs_hii`／`tgYs_hiii`** | 四个性质（由 `choose_spec`） |
| **`tgMap`** | ★★★★★ `tg` 在 `G/H`-余链层的正规形式 |
| **`tgMap_cocycle`** | ★★★★★ 它是 `Z²(G/H, A^H)` 的上闭链 |
| **`tgMap_sec_indep`** | ★★★★ 与截面选择无关 |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgMap

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (S : TgSection H)
variable (x : G → A)
variable (hx : ∀ τ₁ τ₂ : H, x ((τ₁ : G) * τ₂) = x (τ₁ : G) + (τ₁ : G) • x (τ₂ : G))
variable (hinv : ConjInvariant H S x)

/-- **正规提升 `y : G → A`**（由 `exists_tgLift` 用 `Classical.choose` 取定）。 -/
noncomputable def tgYs : G → A :=
  Classical.choose (exists_tgLift H S x hx hinv)

/-- `tgYs 1 = 0`（NSW 的 `y(1) = 0` 归一化）。 -/
theorem tgYs_one : tgYs H S x hx hinv 1 = 0 :=
  (Classical.choose_spec (exists_tgLift H S x hx hinv)).1

/-- `tgYs|_H = x`（NSW **(i)**）。 -/
theorem tgYs_restrict (τ : H) : tgYs H S x hx hinv (τ : G) = x (τ : G) :=
  (Classical.choose_spec (exists_tgLift H S x hx hinv)).2.1 τ

/-- 余链条件 **(ii)**。 -/
theorem tgYs_hii (σ : G) (τ : H) :
    tgYs H S x hx hinv (σ * (τ : G)) = tgYs H S x hx hinv σ + σ • tgYs H S x hx hinv (τ : G) :=
  (Classical.choose_spec (exists_tgLift H S x hx hinv)).2.2.1 σ τ

/-- 余链条件 **(iii)**。 -/
theorem tgYs_hiii (σ : G) (τ : H) :
    tgYs H S x hx hinv ((τ : G) * σ) = tgYs H S x hx hinv (τ : G) + (τ : G) • tgYs H S x hx hinv σ :=
  (Classical.choose_spec (exists_tgLift H S x hx hinv)).2.2.2 σ τ

/-- ★★★★★ **`tg` 在 `G/H`-余链层的正规形式**（NSW 的 `tg[x] = [∂y]`，去掉商）。 -/
noncomputable def tgMap (q₁ q₂ : G ⧸ H) : ↥(FixedPoints.addSubgroup H A) :=
  tgCocycle H S (tgYs H S x hx hinv)
    (tgYs_hii H S x hx hinv) (tgYs_hiii H S x hx hinv) q₁ q₂

/-- ★★★★★ **`tgMap` 是 `Z²(G/H, A^H)` 的上闭链**。 -/
theorem tgMap_cocycle (q₁ q₂ q₃ : G ⧸ H) :
    d2 (G ⧸ H) ↥(FixedPoints.addSubgroup H A)
      (fun p : (G ⧸ H) × (G ⧸ H) => tgMap H S x hx hinv p.1 p.2) (q₁, q₂, q₃) = 0 :=
  tgCocycle_cocycle (H := H) (y := tgYs H S x hx hinv)
    (hii := tgYs_hii H S x hx hinv) (hiii := tgYs_hiii H S x hx hinv) S q₁ q₂ q₃

/-- ★★★★ **`tgMap` 与截面选择无关**。 -/
theorem tgMap_sec_indep (S' : TgSection H) (q₁ q₂ : G ⧸ H) :
    tgMap H S x hx hinv q₁ q₂
      = tgCocycle H S' (tgYs H S x hx hinv)
          (tgYs_hii H S x hx hinv) (tgYs_hiii H S x hx hinv) q₁ q₂ :=
  tgCocycle_sec_indep H (tgYs H S x hx hinv)
    (tgYs_hii H S x hx hinv) (tgYs_hiii H S x hx hinv) S S' q₁ q₂

end TgMap

end L20261018

#print axioms L20261018.tgYs_one
#print axioms L20261018.tgYs_restrict
#print axioms L20261018.tgYs_hii
#print axioms L20261018.tgYs_hiii
#print axioms L20261018.tgMap_cocycle
#print axioms L20261018.tgMap_sec_indep
