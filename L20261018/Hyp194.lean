import Hyp193

/-!
# R1047（**S29 · ④.1 第二步**）：`n ≥ 1` 的表示必有 `c 0 ∈ 𝔪`

设 `sⁿ·x = Σ_{i<p} cᵢ sⁱ`（`cᵢ ∈ 𝒪_F`）且 `n ≥ 1`、`N(x) ∈ 𝒪_F`。则

```
c 0 ∈ 𝔪
```

**论证**：
1. `N(sⁿ·x) = πⁿ·N(x)`（`Hyp193.norm_pow_root_mul`）；
2. 作为 `𝒪_F` 元素 `⟨N(sⁿx), _⟩ = bⁿ·⟨N(x), _⟩` ⟹ `red` 后 `= (red b)ⁿ · …`；
3. `n ≥ 1` ⟹ `(red b)ⁿ = 0`（`Hyp190.residue_uniformizer_image_eq_zero`）⟹ `red ⟨N(sⁿx), _⟩ = 0`；
4. `Hyp190.norm_residue_eq_pow` 给同一边 `= (red (c 0))^p` ⟹ `(red (c 0))^p = 0` ⟹ `c 0 ∈ 𝔪`。

> 注意：**不需要**「`N(x)` 是单位」这个假设 —— 只要 `n ≥ 1` 就成立（这正是极小性论证要的）。
> 下一轮：用 `Hyp191` 提出 `s`，把指数降到 `n−1` ⟹ 与 `n` 极小性矛盾 ⟹ `n = 0`。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section CoeffZeroMem

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **`n ≥ 1` 的归一化表示的常数项落在 `𝔪`**。 -/
theorem coeff_zero_mem_maximalIdeal (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) {b : ↥𝒪[F]}
    (hb : (b : F) = (π : F))
    {x : AdjoinRoot (X ^ p - C (π : F))} {n : ℕ} (hn : 1 ≤ n) {c : ℕ → ↥𝒪[F]}
    (hrep : (AdjoinRoot.root (X ^ p - C (π : F))) ^ n * x
      = sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F)))
    (hx : (Algebra.norm F x : F) ∈ 𝒪[F]) :
    (c 0 : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
  obtain ⟨B, hB⟩ := basis_root_pow (F := F) p π
  -- 1. `N(Σ cᵢ sⁱ) = πⁿ · N(x)`
  have hNy : Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F)))
      = (π : F) ^ n * Algebra.norm F x := by
    rw [← hrep, norm_pow_root_mul (F := F) p π hp2]
  -- 2. `N(Σ cᵢ sⁱ) ∈ 𝒪_F`
  have hNmem : (Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))) : F)
      ∈ 𝒪[F] := norm_mem_integer (F := F) p π hb hB c
  -- 3. `red` 之后为 0
  have hzero : IsLocalRing.residue ↥𝒪[F]
      ⟨Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))), hNmem⟩ = 0 := by
    have hEq : (⟨Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))), hNmem⟩
        : ↥𝒪[F]) = b ^ n * ⟨Algebra.norm F x, hx⟩ := by
      apply Subtype.ext
      show (Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))) : F)
        = ((b ^ n : ↥𝒪[F]) : F) * (Algebra.norm F x : F)
      rw [hNy]
      push_cast
      rw [hb]
    rw [hEq, map_mul, map_pow,
      residue_uniformizer_image_eq_zero (F := F) hv hπ hb]
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
    simp
  -- 4. `Hyp190`：`red ⟨N(Σ cᵢ sⁱ), _⟩ = (red (c 0))^p`
  have hcong := norm_residue_eq_pow (F := F) p hv hπ hb (B := B) hB (c := c) hNmem
  have hp0 : (IsLocalRing.residue ↥𝒪[F] (c 0)) ^ p = 0 := by
    rw [← hcong, hzero]
  exact (IsLocalRing.residue_eq_zero_iff _).mp
    ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp hp0)

end CoeffZeroMem

end L20261018

#print axioms L20261018.coeff_zero_mem_maximalIdeal
