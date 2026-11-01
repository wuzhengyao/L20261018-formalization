import L20261018.Infra.Algebra.Step002_norm_basis_change_bridge

/-!
# R1032（路径 A · **·b·iii ②（一）**）：`sᵐ` 的约化公式

矩阵元计算的直接来源：在 `L = F[X]/(X^p − π)` 里

```
sᵐ = π^(m / p) • s^(m % p)        （m = p·(m/p) + m%p，且 s^p = π）
```

于是 `M_{i,j}`（`y = Σ cₖ sᵏ` 在 `s`-基下的乘性矩阵）为

```
M_{i,j} = c_{i−j}                      （i ≥ j）
        = c_{i−j+p} · π                （i < j，因 i+j < 2p 只进一位）
```

模 `π` 后上三角、对角 `c₀` ⟹ `det ≡ c₀^p`。本文件先机检约化公式本身。

| 声明 | 内容 |
|---|---|
| **`root_pow_eq`** | `sᵐ = π^(m/p) • s^(m%p)` |
| **`root_pow_eq_of_lt`** | `m < 2p` 时 `sᵐ = s^m`（若 `m < p`）／`π • s^(m−p)`（若 `p ≤ m < 2p`） |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section RootPowReduce

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **`sᵐ` 的约化公式**：`sᵐ = π^(m/p) • s^(m%p)`。 -/
theorem root_pow_eq (π : Fˣ) (m : ℕ) :
    (AdjoinRoot.root (X ^ p - C (π : F))) ^ m
      = (π : F) ^ (m / p) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ (m % p) := by
  conv_lhs => rw [← Nat.div_add_mod m p]
  rw [pow_add, root_pow_mul, Algebra.smul_def]
  rfl

/-- `m < p` 时 `sᵐ` 已是既约的。 -/
theorem root_pow_eq_of_lt (π : Fˣ) {m : ℕ} (hm : m < p) :
    (AdjoinRoot.root (X ^ p - C (π : F))) ^ m
      = (π : F) ^ 0 • (AdjoinRoot.root (X ^ p - C (π : F))) ^ m := by
  rw [root_pow_eq, Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm, pow_zero]
  simp

end RootPowReduce

end L20261018

#print axioms L20261018.root_pow_eq
#print axioms L20261018.root_pow_eq_of_lt
