import Hyp310
import Hyp204
import Hyp206
import Hyp80

/-!
# R1202（`hbridge` 标量化 · **第 1 块：标量的来源**）

`hbridge`（`c = 1`）在 `Hyp19` 现定义下不可证，因为
`KummerBridge.kummerCoeffLinearEquiv = LinearEquiv.ofFinrankEq _ _ _` 是 `Classical.choose`
**任意取**的一个线性同构。本块把"任意性"精确定位为一个**非零标量**：

两种系数识别 `KummerBridge.kummerCoeffLinearEquiv`（任意）与
`SymbolCupBridge.kummerCoeffLinearEquiv`（规范，由本原根确定）都是
`KummerCoeff F p →ₗ[ZMod p] ZMod p` 的同构，而 `KummerCoeff` **一维**（`finrank_kummerCoeff`）
⟹ 二者只差一个非零标量 `c`。

这就是 `PLAN-HBRIDGE.md` §7.3 所说的"标量来源"。

## 本轮
| 声明 | 内容 |
|---|---|
| **`exists_smul_kummerCoeffLinearEquiv`** | ★★★★★ `∃ c ≠ 0, ∀ x, E x = c • E₀ x` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section CoeffScalar

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [NeZero p]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- ★★★★★ **两种系数识别只差一个非零标量**（`KummerCoeff` 一维）。

`KummerBridge.kummerCoeffLinearEquiv`（`Classical.choose`，任意）与
`SymbolCupBridge.kummerCoeffLinearEquiv`（规范）都是 `KummerCoeff F p ≃ₗ ZMod p`，
而 `KummerCoeff` 的 `ZMod p`-维数为 `1` ⟹ 只差一个 `c ≠ 0`。 -/
theorem exists_smul_kummerCoeffLinearEquiv (hp : IsUnit (p : F)) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ x : KummerCoeff F p,
      KummerBridge.kummerCoeffLinearEquiv F p hp x
        = c • SymbolCupBridge.kummerCoeffLinearEquiv (p := p) (ζ := ζ) hζ x :=
  exists_smul_eq_of_linearEquiv (K := ZMod p) (M := KummerCoeff F p) (N := ZMod p)
    (finrank_kummerCoeff hp) (Module.finrank_self (ZMod p)) _ _

end CoeffScalar

end L20261018

#print axioms L20261018.exists_smul_kummerCoeffLinearEquiv
