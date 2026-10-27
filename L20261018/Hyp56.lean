import L20261018.Hyp55
/-!
# `(1b)` 第二阶段（一）：carry 余环的**算术核心**

在 Kummer 扩张 `L = K(a^{1/p})`（`Hyp55`）上，carry 余环按
`c(σ^i, σ^j) = b^{⌊(i+j)/p⌋}`（`i, j` 取 `ZMod p` 的典范代表）定义，其中 `b ∈ Kˣ`。
TauCeti `TwoCocycle` 的余环恒等式在 `Lˣ` 里读作

    c(τ, ρ) · c(τρ, ρ') = τ(c(ρ, ρ')) · c(τ, ρρ')        (Lˣ 中)

`b ∈ Kˣ` 被 `τ` 固定，故两边都是 `b` 的幂，指数分别为

    ⌊(i+j)/p⌋ + ⌊((i+j) mod p + k)/p⌋       与
    ⌊(j+k)/p⌋ + ⌊(i + (j+k) mod p)/p⌋

本文件证明二者都等于 `⌊(i+j+k)/p⌋`（**进位的结合律**）——这是 carry 余环良定的全部算术内容。
-/

set_option linter.unusedSectionVars false

namespace SymbolCarry

/-- **进位的结合律（左形）**：`⌊(i+j)/p⌋ + ⌊((i+j) mod p + k)/p⌋ = ⌊(i+j+k)/p⌋`。 -/
theorem carry_left (hp : 0 < p) (i j k : ℕ) :
    (i + j) / p + ((i + j) % p + k) / p = (i + j + k) / p := by
  conv_rhs =>
    rw [show i + j + k = (i + j) + k from rfl, ← Nat.div_add_mod (i + j) p,
      show p * ((i + j) / p) + (i + j) % p + k
        = p * ((i + j) / p) + ((i + j) % p + k) from by ring]
  rw [Nat.mul_add_div hp]

/-- **进位的结合律（右形）**：`⌊(j+k)/p⌋ + ⌊(i + (j+k) mod p)/p⌋ = ⌊(i+j+k)/p⌋`。 -/
theorem carry_right (hp : 0 < p) (i j k : ℕ) :
    (j + k) / p + (i + (j + k) % p) / p = (i + j + k) / p := by
  have h := carry_left hp j k i
  rw [add_comm ((j + k) % p) i] at h
  rw [show j + k + i = i + j + k from by ring] at h
  exact h

/-- **carry 余环的余环恒等式**（指数层面）：两个指数相等。 -/
theorem carry_assoc (hp : 0 < p) (i j k : ℕ) :
    (i + j) / p + ((i + j) % p + k) / p
      = (j + k) / p + (i + (j + k) % p) / p := by
  rw [carry_left hp i j k, carry_right hp i j k]

end SymbolCarry
