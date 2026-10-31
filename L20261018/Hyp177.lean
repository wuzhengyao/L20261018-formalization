import Hyp176

/-!
# R1030（路径 A · **A1′·2·b·iv（三）**）：归一化 —— `∃ n, sⁿx` 的坐标全在 `𝒪_F`

把前几轮的零件装配起来：

* `Hyp176.exists_coeff_adjoinRoot`：`x = Σ_{i<p} aᵢ • sⁱ`；
* `Hyp170.exists_uniformizer_pow_mul_mem_integer`：每个 `aᵢ` 有清分母指数 `mᵢ`；
* `Hyp175.uniformizer_pow_mul_mem_integer_mono`：清过的指数不因取大而失效（取 `n = Σ mᵢ`）；
* `Hyp174.root_pow_mul`：`s^{p·n} = of (πⁿ)`。

| 声明 | 内容 |
|---|---|
| **`exists_pow_root_mul_coeff_mem`** | `∃ n c, sⁿ * x = Σ_{i<p} ((cᵢ : 𝒪_F) : F) • sⁱ` |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section Normalization

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **归一化**：存在 `n`，使 `sⁿ * x` 的坐标（在 `s`-基下）全在 `𝒪_F` 中。 -/
theorem exists_pow_root_mul_coeff_mem (hv : ValIntegralityCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (x : AdjoinRoot (X ^ p - C (π : F))) :
    ∃ (n : ℕ) (c : ℕ → ↥𝒪[F]),
      (AdjoinRoot.root (X ^ p - C (π : F))) ^ n * x
        = ∑ i ∈ Finset.range p,
            ((c i : ↥𝒪[F]) : F) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i := by
  obtain ⟨a, ha⟩ := exists_coeff_adjoinRoot (F := F) p π x
  -- 每个坐标的清分母指数
  choose m hm using fun i : ℕ =>
    exists_uniformizer_pow_mul_mem_integer (F := F) hv π hπ (a i)
  -- 取总和（`≥` 每个 `mᵢ`）
  set n : ℕ := ∑ i ∈ Finset.range p, m i with hn
  have hle : ∀ i ∈ Finset.range p, m i ≤ n := by
    intro i hi
    exact Finset.single_le_sum (f := m) (fun j _ => Nat.zero_le _) hi
  -- 系数族
  have hcoeff : ∀ i ∈ Finset.range p, (π : F) ^ n * a i ∈ 𝒪[F] := by
    intro i hi
    exact uniformizer_pow_mul_mem_integer_mono (F := F) hv hπ (hle i hi) (hm i)
  -- 系数族（`i < p` 时取 `π^n aᵢ`，否则取 `0`）
  set cfun : ℕ → ↥𝒪[F] :=
    fun i => if h : i < p then ⟨(π : F) ^ n * a i, hcoeff i (Finset.mem_range.mpr h)⟩ else 0
    with hcfun
  have hc : ∀ i ∈ Finset.range p, ((cfun i : ↥𝒪[F]) : F) = (π : F) ^ n * a i := by
    intro i hi
    have hip : i < p := Finset.mem_range.mp hi
    simp only [hcfun, dif_pos hip, Subtype.coe_mk]
  refine ⟨p * n, cfun, ?_⟩
  have hroot : (AdjoinRoot.root (X ^ p - C (π : F))) ^ (p * n)
      = algebraMap F (AdjoinRoot (X ^ p - C (π : F))) ((π : F) ^ n) := by
    rw [root_pow_mul (F := F) p π n]
    rfl
  rw [hroot, ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hc i hi, Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

end Normalization

end L20261018

#print axioms L20261018.exists_pow_root_mul_coeff_mem
