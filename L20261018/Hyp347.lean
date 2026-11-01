import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# R1258（S35 C 项第 1 步）：`K((t))` 的 `ValuativeRel` 实例（一般 `K`）

PROMPT-S35 的 C 项：把第 4 章的 `L1` 见证搬到函数域例子。第一步是把**估值关系**装上。

mathlib 已有 `X`-进赋值 `LaurentSeries.valued : Valued K⸨X⸩ ℤᵐ⁰`
（`RingTheory/LaurentSeries.lean:504`，section 变量要求 `[Field K]`）；
`ValuativeRel.ofValuation` 把它转成本战役使用的 `ValuativeRel` 类。
本文件给出**对任意域 `K`** 的实例（比只做 `𝔽₇` 更强，且不依赖 `ZMod 7` 的域实例命名）。
-/

noncomputable section

open LaurentSeries

namespace L20261018
namespace FqXt

/-- ★★★★ **`K((t))` 上的 `ValuativeRel`**（由 `X`-进赋值给出；`K` 为任意域）。 -/
instance instValuativeRel {K : Type*} [Field K] : ValuativeRel (LaurentSeries K) :=
  ValuativeRel.ofValuation (Valued.v)

/-- 自检：`1 ≤ᵥ 0` 不成立（`ValuativeRel` 的 `not_vle_one_zero`）。 -/
example {K : Type*} [Field K] : ¬ ((1 : LaurentSeries K) ≤ᵥ 0) :=
  ValuativeRel.not_vle_one_zero

end FqXt
end L20261018

#print axioms L20261018.FqXt.instValuativeRel
