import Hyp172

/-!
# R1026（路径 A · **A1′·2·b·iii（二）**）：范数是幺半同态 ⟹ 乘性／幂性／幂零为零

**上一轮的 API 读数错了**：`Algebra.norm` 的定义就是**幺半同态**
（`noncomputable def norm : S →* R := LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom`），
故 `norm_pow`／`norm_mul` 就是 `map_pow`／`map_mul`（本文件即更正）。

它们正是 ·b·iii ② 需要的：
* **幂零 ⟹ 范数为 `0`**：`x^n = 0 ⟹ N(x)^n = N(x^n) = 0`，域上故 `N(x) = 0`；
* **乘性**：`N(a₀·(1+w)) = N(a₀)·N(1+w)`，`N(a₀) = a₀^p`（`Hyp172`）。

在**剩余模型** `A_𝓀 := AdjoinRoot_{𝓀}(X^p)` 上，`s^p = 0`（`AdjoinRoot.mk_self`）⟹ `N(s) = 0`。

| 声明 | 内容 |
|---|---|
| **`norm_pow`** | `N(x^n) = (N x)^n` |
| **`norm_mul`** | `N(x·y) = N x · N y` |
| **`norm_eq_zero_of_nilpotent`** | `x^n = 0`（`n > 0`）⟹ `N x = 0`（需 `[Nontrivial S]`） |
| **`root_pow_eq_zero_adjoinRoot`** | 剩余模型里 `s^p = 0`（幂零） |

> **未落地的一步（登记）**：由上一行推 `N(s) = 0` 还需 `Nontrivial (AdjoinRoot (X^p))` 实例（`Algebra.norm_zero` 需要它）。
> 本 pin 未直接合成，留到下一轮补（或改用 `map_mul` 避开 `norm_zero`）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel Polynomial

namespace L20261018

section NormHom

variable {k : Type} [Field k]
variable (S : Type) [CommRing S] [Algebra k S] [Nontrivial S] [Module.Free k S] [Module.Finite k S]

/-- **范数是乘性的**（`Algebra.norm` 本就是 `S →* k`）。 -/
theorem norm_mul (x y : S) :
    Algebra.norm k (x * y) = Algebra.norm k x * Algebra.norm k y :=
  map_mul (Algebra.norm k) x y

/-- **范数是幂性的**。 -/
theorem norm_pow (x : S) (n : ℕ) :
    Algebra.norm k (x ^ n) = (Algebra.norm k x) ^ n :=
  map_pow (Algebra.norm k) x n

/-- **幂零元的范数为 `0`**：`x^n = 0`（`n > 0`）⟹ `N x = 0`。 -/
theorem norm_eq_zero_of_nilpotent {x : S} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 0) :
    Algebra.norm k x = 0 := by
  have hpow : (Algebra.norm k x) ^ n = 0 := by
    rw [← norm_pow S x n, hx, Algebra.norm_zero]
  exact pow_eq_zero_iff hn.ne' |>.mp hpow

end NormHom

section ResidueModel

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime]

/-- 剩余模型 `A_𝓀 = 𝓀[X]/(X^p)` 里，`s := X` 是**幂零**的：`s^p = 0`。 -/
theorem root_pow_eq_zero_adjoinRoot :
    (AdjoinRoot.root (X ^ p : k[X])) ^ p = 0 := by
  rw [← AdjoinRoot.mk_X (f := (X ^ p : k[X])), ← map_pow]
  have : (X : k[X]) ^ p = (X ^ p : k[X]) := rfl
  rw [this, AdjoinRoot.mk_self]

end ResidueModel

end L20261018

#print axioms L20261018.norm_mul
#print axioms L20261018.norm_pow
#print axioms L20261018.norm_eq_zero_of_nilpotent
#print axioms L20261018.root_pow_eq_zero_adjoinRoot
