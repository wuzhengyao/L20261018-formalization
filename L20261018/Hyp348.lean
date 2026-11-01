import L20261018.Hyp347
import Mathlib.Algebra.Field.ZMod

/-!
# R1259（S35 C 项第 2 步）：`𝔽₇` 的域实例与具体 `ValuativeRel`

`Hyp347` 给出任意域上的 `ValuativeRel (LaurentSeries K)`。本文件补上具体例子 `𝔽₇((t))` 的两块：

* `𝔽₇` 的域结构（`Mathlib.Algebra.Field.ZMod` 的 `Field (ZMod p)`，需 `Fact p.Prime`；
  `Hyp347` 的探查曾因缺此 import 而误报"无域实例"）；
* `ValuativeRel (LaurentSeries (ZMod 7))` 的实例化。

`μ₃` 的本原根（`2 ∈ 𝔽₇`）留到下一步（`IsPrimitiveRoot` 的 import 路径待定）。
-/

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `𝔽₇` 是域。 -/
example : Field (ZMod 7) := inferInstance

/-- 具体例子上的 `ValuativeRel`（`Hyp347` 的一般实例的实例化）。 -/
noncomputable instance : ValuativeRel (LaurentSeries (ZMod 7)) := instValuativeRel

/-- 自检：`1 ≤ᵥ 0` 不成立。 -/
example : ¬ ((1 : LaurentSeries (ZMod 7)) ≤ᵥ 0) := ValuativeRel.not_vle_one_zero

end FqXt
end L20261018
