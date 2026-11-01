import L20261018.Hyp174

/-!
# R1028（路径 A · **A1′·2·b·iv（一）**）：一致化元在 `𝒪_F` 中 ＋ 清分母的单调性

整性判据的归一化步是：对每个系数 `aᵢ` 用 `Hyp170` 取一个清分母指数 `nᵢ`，再取 `n := max nᵢ`
（或任意 `≥` 全部 `nᵢ` 的数）。「取 max」需要一条**单调性**：清过的分母不会被更小的幂破坏，
而这要用 **`π ∈ 𝒪_F`**（乘 `π` 保持整数性）。

| 声明 | 内容 |
|---|---|
| **`uniformizer_mem_integer`** | `∃ b : ↥𝒪_F, (b : F) = π`（`v(π) = 1 ≥ 0`） |
| **`uniformizer_pow_mul_mem_integer_mono`** | `(π^n·a ∈ 𝒪_F) ∧ n ≤ m ⟹ (π^m·a ∈ 𝒪_F)` |

> 下一轮：与 `Hyp170`＋坐标分解合成 `∃ n, s^n x` 的系数全在 `𝒪_F`。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section UniformizerInteger

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **一致化元在 `𝒪_F` 中**（`v(π) = 1 ≥ 0`）。 -/
theorem uniformizer_mem_integer (hv : ValIntegralityCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    ∃ b : ↥𝒪[F], (b : F) = (π : F) := by
  obtain ⟨b, hb⟩ := hv.exists_unit_of_nonneg π (by rw [hπ]; simp)
  refine ⟨(b : ↥𝒪[F]), ?_⟩
  have h := congrArg (fun u : Fˣ => (u : F)) hb
  simpa using h

/-- **清分母的单调性**：`π^n·a ∈ 𝒪_F` 且 `n ≤ m` ⟹ `π^m·a ∈ 𝒪_F`。 -/
theorem uniformizer_pow_mul_mem_integer_mono (hv : ValIntegralityCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {a : F} {n m : ℕ} (hnm : n ≤ m)
    (ha : (π : F) ^ n * a ∈ 𝒪[F]) : (π : F) ^ m * a ∈ 𝒪[F] := by
  obtain ⟨b, hb⟩ := uniformizer_mem_integer (F := F) hv hπ
  have hbF : ((b : ↥𝒪[F]) : F) = (π : F) := hb
  have hpow : (π : F) ^ m = ((b : ↥𝒪[F]) : F) ^ (m - n) * (π : F) ^ n := by
    conv_lhs => rw [← hbF]
    conv_rhs => rw [← hbF]
    rw [← pow_add, Nat.sub_add_cancel hnm]
  rw [hpow, mul_assoc]
  refine Subring.mul_mem _ ?_ ha
  exact Subring.pow_mem _ b.2 _

end UniformizerInteger

end L20261018

#print axioms L20261018.uniformizer_mem_integer
#print axioms L20261018.uniformizer_pow_mul_mem_integer_mono
