import Hyp177

/-!
# R1031（路径 A · **·b·iii ① 的解锁**）：mathlib 已有范数–基变换桥，`A_𝒪` 的 `Free`/`Finite` 白拿

上一轮我计划「自建范数与基变换的交换」，**先做了内容式检索（L46/L47），发现库里已有**：

| 库内件 | 位置 | 内容 |
|---|---|---|
| **`Algebra.norm_localization`** | `RingTheory/Localization/NormTrace.lean:62` | `N_{Rₘ}(a ⊗ 1) = N_R(a) ⊗ 1`（`[Module.Free R S] [Module.Finite R S]`） |
| `Algebra.map_leftMulMatrix_localization` | 同上 `:51` | 矩阵版（`mapMatrix` 与局部化交换） |
| `Algebra.norm_eq_iff` | 同上 `:74` | `N_R a = b ↔ N_{Rₘ}(a⊗1) = b⊗1`（`M ≤ nonZeroDivisors`） |
| **`Polynomial.Monic.free_adjoinRoot`** | `RingTheory/AdjoinRoot.lean:752` | 单项式多项式 ⟹ `AdjoinRoot` 是 `Free` |
| **`Polynomial.Monic.finite_adjoinRoot`** | 同上 `:755` | 同上，`Finite` |

⟹ **·b·iii ① 从「自建」降级为「接线」**：剩下的只是把 `(A_𝒪)_M` 识别成 `L`。
本文件先落地 `A_𝒪` 的 `Free`/`Finite` 实例（`norm_localization` 的前提）。

| 声明 | 内容 |
|---|---|
| **`free_adjoinRoot_uniformizer`** | `Module.Free ↥𝒪_F (AdjoinRoot (X^p − C b))` |
| **`finite_adjoinRoot_uniformizer`** | `Module.Finite ↥𝒪_F (AdjoinRoot (X^p − C b))` |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section AdjoinRootFree

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **`A_𝒪 = 𝒪_F[X]/(X^p − π)` 是自由 `𝒪_F`-模**（单项式，库内 `Monic.free_adjoinRoot`）。 -/
theorem free_adjoinRoot_uniformizer (b : ↥𝒪[F]) :
    Module.Free ↥𝒪[F] (AdjoinRoot (X ^ p - C b)) :=
  Polynomial.Monic.free_adjoinRoot (monic_X_pow_sub_C b (Fact.out : p.Prime).pos.ne')

/-- **`A_𝒪` 是有限 `𝒪_F`-模**（同上，`Monic.finite_adjoinRoot`）。 -/
theorem finite_adjoinRoot_uniformizer (b : ↥𝒪[F]) :
    Module.Finite ↥𝒪[F] (AdjoinRoot (X ^ p - C b)) :=
  Polynomial.Monic.finite_adjoinRoot (monic_X_pow_sub_C b (Fact.out : p.Prime).pos.ne')

end AdjoinRootFree

end L20261018

#print axioms L20261018.free_adjoinRoot_uniformizer
#print axioms L20261018.finite_adjoinRoot_uniformizer
