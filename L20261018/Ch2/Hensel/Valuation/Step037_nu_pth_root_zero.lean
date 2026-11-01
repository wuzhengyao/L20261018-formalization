import L20261018.Witness.Step038_val_compat_nonempty
import L20261018.Ch2.Hensel.ResidueMap.Step063_mu_p_residue_instance

/-!
# S51 R11：**`ν(u^{1/p}) = 0` 的引擎** ＋ 延拓假设的**三条锁**（第三步「`Γ_F`-稳定性」入锁）

## 0 本轮的数学发现（关键简化）

`(CI)` 的 `⊆` 方向需要「`α^p = u`（`u` 是单位）⟹ `α` 的赋值是 0」。
上一轮（`hyp-fbar-valuation` §5 步 2）把它当成需要 Krull 延拓的重活。**其实一旦有了值群上的赋值
`w`，它是免费的**：

```
w(α)^p = w(α^p) = w(u) = 1   ⟹   w(α) = 1        （有序群无挠）
```

**不需要**整性、不需要 `𝒪[F][α]` 的结构、不需要 Hensel。
⟹ 步 2 里**只剩「`Γ_F`-稳定性」（`σ` 保 `𝒪_W`）是实质内容**，而它正是 Hensel 给、必须**入锁**的第三项。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`eq_one_of_pow_eq_one`** | ★★★ 有序群无挠：`a^p = 1`、`p ≠ 0` ⟹ `a = 1`（值群 `Multiplicative ℚ`） |
| **`unitVal_root_eq_one`** | ★★★★★★ **`α^p = u`、`w u = 1` ⟹ `w α = 1`**（＝`ν(u^{1/p}) = 0` 的群论骨架） |
| **`FbarValuationHyp₂`** | ★★★★★ 延拓假设的**三条锁**：赋值环相容 ＋ 极大理想相容 ＋ **`Γ_F`-稳定性** |

## 2 两件件的分工（写入下一轮接缝）

`FbarValuationHyp₂` 给的是 **`Valuation` 层**的 `W`；`unitVal_root_eq_one` 说的是**单位群层**的 `w`。
把 `W` 变成 `w`（`WithZero (Multiplicative ℚ)` 的单位群 ≃ `Multiplicative ℚ`，即
`WithZero.unitsWithZeroEquiv`）是**下一轮的一行桥**（`Hyp620`）。
之所以分开：`Valuation` 层的 `W α ^ p = 1 ⟹ W α = 1` 要走 `WithZero` 的非零段，
API 摩擦大且与本轮的数学结论无关。

## 3 诚实边界

* `FbarValuationHyp₂` 仍是**假设**（Krull 延拓 ＋ Hensel 唯一性都不在库）。
* 本轮**不增覆盖率**；它是 `(CI) ⊆` 的第二个前置件（第一个是 `Hyp618` 的在住性）。
* **下一步（已明确）**：`Hyp620` 做 `W ↦ w` 的桥 ＋ 从稳定条件取 `I := {σ | σ 在 κ̄ 上平凡}`，
  再用 `Hyp613` 的 `μ_p ↪ κ̄^×` 证 `Hyp614` 的 `hCI` —— 那时 `φ` 由假设变**导出**。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

/-! ## 1 无挠引擎 -/

/-- ★★★ **有序群无挠**（值群 `Multiplicative ℚ`）：`a^p = 1`、`p ≠ 0` ⟹ `a = 1`。 -/
theorem eq_one_of_pow_eq_one {p : ℕ} (hp : p ≠ 0) {a : Multiplicative ℚ} (h : a ^ p = 1) :
    a = 1 := by
  have hkey : ∀ n : ℕ, Multiplicative.toAdd (a ^ n) = Multiplicative.toAdd a * (n : ℚ) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        show Multiplicative.toAdd (a ^ m) + Multiplicative.toAdd a
          = Multiplicative.toAdd a * ((m + 1 : ℕ) : ℚ)
        rw [ih]
        push_cast
        ring
  have h2 := congrArg Multiplicative.toAdd h
  rw [hkey p] at h2
  have hpQ : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp
  have hzero : Multiplicative.toAdd a = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 hpQ
  simpa using congrArg Multiplicative.ofAdd hzero

/-- ★★★★★★ **`ν(u^{1/p}) = 0` 的群论骨架**：`α^p = u`、`w u = 1` ⟹ `w α = 1`。 -/
theorem unitVal_root_eq_one {L : Type} [Field L] {p : ℕ} (hp : p ≠ 0)
    (w : Lˣ →* Multiplicative ℚ) {u α : Lˣ} (hα : α ^ p = u) (hu : w u = 1) : w α = 1 := by
  have hpow : w α ^ p = 1 := by rw [← map_pow, hα, hu]
  exact eq_one_of_pow_eq_one hp hpow

/-! ## 2 延拓假设的三条锁 -/

section ThreeLock

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★★ **延拓假设（三条锁）**：`v` 延拓到 `F̄ = SeparableClosure F`。

1. 赋值环与 `𝒪[F]` 相容：`W (x) ≤ 1 ↔ x ∈ 𝒪[F]`；
2. 极大理想相容：`W (x) < 1 ↔ x ∈ 𝔪[F]`；
3. **`Γ_F`-稳定性**（Hensel 给）：`Γ_F` 保 `𝒪_W`。

⚠ 这是**假设的形态**，不是定理（Krull 延拓 ＋ Hensel 唯一性都不在库）。 -/
def FbarValuationHyp₂ : Prop :=
  ∃ W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)),
    (∀ x : F, W (algebraMap F (SeparableClosure F) x) ≤ 1 ↔ x ∈ 𝒪[F]) ∧
    (∀ x : F, W (algebraMap F (SeparableClosure F) x) < 1 ↔
      ∃ h : x ∈ 𝒪[F], (⟨x, h⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F]) ∧
    (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (x : SeparableClosure F),
      W x ≤ 1 → W (σ x) ≤ 1)

end ThreeLock

end L20261018

#print axioms L20261018.eq_one_of_pow_eq_one
#print axioms L20261018.unitVal_root_eq_one
