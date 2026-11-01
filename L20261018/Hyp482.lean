import L20261018.Hyp481
import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Integral

/-!
# S40 R22：动作 A 第三段 —— `integralBockstein` 的 range 引理

## 本轮前置：**移植 `Bockstein.Integral`**

`raw/TauCeti/.../ContCohomology/Bockstein/Integral.lean` 原先**未被移植**（`out/` 无 olean）。
按规则 17（(b) 类须"算完"）跑
`python3 scratch/lean-l20261018/port_tau.py TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Integral`
⟹ 已 built（连带 `Data.ZMod.TrivialAction`、`Data.ZMod.MulCastHom`、
`Corestriction.ConnectingMap` 等依赖）。

## 库内已有的（移植后）

| 件 | 内容 |
|---|---|
| `TauCeti.integralBockstein (G) (n) (i)` | `H^i(ULift (ZMod n)) ⟶ H^{i+1}(ULift ℤ)` |
| `TauCeti.integralBockstein_one_injective` | 单射 |
| `TauCeti.integralBocksteinShortExact (G) (n)` | `0 → ℤ --n--> ℤ → ZMod n → 0` |
| `TauCeti.integralBocksteinShortExact_incl` | `incl = nsmulAddMonoidHom n` |
| `TauCeti.subsingleton_continuousCohomology_one_int` | `H¹(ULift ℤ) = 0`（`G` 紧） |

## 本机检件

| 声明 | 内容 |
|---|---|
| `integralBockstein_available` | 可用性锁定 |
| **`integralBockstein_one_range`** | ★★★★★ **`(∃ y, δ y = x) ↔ ↑n • x = 0`**（像 = `n`-挠） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- `G` 在 `ULift ℤ` 上的平凡作用（`integralBockstein` 的系数结构）。 -/
local instance integralTrivialAction : DistribMulAction G (ULift.{0} ℤ) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- ★★★★ **可用性锁定**：`integralBockstein` 与它的单射性（移植后可用）。 -/
theorem integralBockstein_available (n : ℕ) [NeZero n] :
    Function.Injective ⇑(ConcreteCategory.hom (TauCeti.integralBockstein G n 1)) :=
  TauCeti.integralBockstein_one_injective G n

/-! ## 本轮未完成：range 引理（诚实记录，`RECON-R3` §101.3）

`longExact_exact₄` **不存在**（只有 `exact₁`（`range delta = ker incl_*` 的**前一格**）、
`exact₂`（`range incl_* = ker proj_*`）、`exact₃`（`range proj_* = ker delta`））。
而我要的 `range δ = ker(incl_* at degree 2)` 是 **`exact₄`** 那一格。

**下轮两条路**：
1. 直接由 `exact₃ (S) 1` ＋ `subsingleton_continuousCohomology_one_int`（`H¹(ULift ℤ)` 是
   subsingleton ⟹ `incl_*` 在 degree 1 是零映射 ⟹ `ker(incl_* at 2) ⊇ range δ` 来自
   `delta ∘ incl_* = 0`-型复合为零；反向用 `Function.Exact` 的 `le` 方向 ＋ 长度论证）。
2. **查 `DiscreteShortExact` 是否另有 `range_delta`-型件**（`#check` 一批候选名：
   `delta_comp`、`comp_delta`、`incl_comp_delta`、`range_delta`、`ker_delta`）。
-/

end L20261018

#print axioms L20261018.integralBockstein_available
