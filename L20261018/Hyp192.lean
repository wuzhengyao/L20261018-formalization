import Hyp191

/-!
# R1045（**S29 · ④.0**）：归一化的 `ValCompat` 版（输出 `sumCoeff` 形式）

旧 `Hyp177.exists_pow_root_mul_coeff_mem` 用的是 R1039 判为空的结构 `ValIntegralityCompat`。
本文件在 `Hyp187.ValCompat` 下重述，并且**输出改为 `sumCoeff`（`Fin p` 指标）形式**，
以便与 `Hyp190.norm_residue_eq_pow` 直接复合。

| 声明 | 内容 |
|---|---|
| **`sum_range_eq_sumCoeff`** | `∑ i ∈ range p, aᵢ • sⁱ = sumCoeff π a`（指标类型转换） |
| **`exists_pow_root_mul_coeff_mem_sumCoeff`** | `∃ n c, sⁿ · x = sumCoeff π (fun i => ((cᵢ : ↥𝒪_F) : F))` |
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section NormalizationFixed

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **指标转换**：`∑ i ∈ range p` 形式与 `sumCoeff`（`Fin p`）形式相等。 -/
theorem sum_range_eq_sumCoeff (π : Fˣ) (a : ℕ → F) :
    (∑ i ∈ Finset.range p, a i • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i)
      = sumCoeff (F := F) p π a := by
  rw [sumCoeff,
    Finset.sum_fin_eq_sum_range (c := fun i : Fin p =>
      a (i : ℕ) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))]
  exact Finset.sum_congr rfl fun i hi => by
    rw [dif_pos (Finset.mem_range.mp hi)]

/-- **归一化（`ValCompat` 版，`sumCoeff` 输出）**：存在 `n`，使 `sⁿ·x` 的 `s`-坐标全在 `𝒪_F`。 -/
theorem exists_pow_root_mul_coeff_mem_sumCoeff (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (x : AdjoinRoot (X ^ p - C (π : F))) :
    ∃ (n : ℕ) (c : ℕ → ↥𝒪[F]),
      (AdjoinRoot.root (X ^ p - C (π : F))) ^ n * x
        = sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F)) := by
  obtain ⟨a, ha⟩ := exists_coeff_adjoinRoot (F := F) p π x
  have ha' : x = sumCoeff (F := F) p π a := by rw [ha, sum_range_eq_sumCoeff]
  -- 逐坐标取清分母指数
  choose m hm using fun i : ℕ => valCompat_exists_pow_mul_mem_integer (F := F) hv π hπ (a i)
  set n : ℕ := ∑ i ∈ Finset.range p, m i with hn
  have hle : ∀ i ∈ Finset.range p, m i ≤ n := fun i hi =>
    Finset.single_le_sum (f := m) (fun j _ => Nat.zero_le _) hi
  have hcoeff : ∀ i ∈ Finset.range p, (π : F) ^ n * a i ∈ 𝒪[F] := fun i hi =>
    valCompat_pow_mul_mem_integer_mono (F := F) hv hπ (hle i hi) (hm i)
  set c : ℕ → ↥𝒪[F] := fun i =>
    if h : i < p then ⟨(π : F) ^ n * a i, hcoeff i (Finset.mem_range.mpr h)⟩ else 0 with hc
  refine ⟨p * n, c, ?_⟩
  -- `s^(p*n) = algebraMap (π^n)`
  have hroot : (AdjoinRoot.root (X ^ p - C (π : F))) ^ (p * n)
      = algebraMap F (AdjoinRoot (X ^ p - C (π : F))) ((π : F) ^ n) := by
    rw [root_pow_mul (F := F) p π n]
    rfl
  -- `π^n • x = sumCoeff π (fun i => π^n * a i)`
  have hsmul : (π : F) ^ n • x = sumCoeff (F := F) p π (fun i => (π : F) ^ n * a i) := by
    rw [ha', sumCoeff, sumCoeff, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
  -- `algebraMap c * x = c • x`（`Algebra.smul_def`）
  rw [hroot, ← Algebra.smul_def, hsmul]
  -- 两个 `sumCoeff` 的系数在 `i < p` 上相同
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) < p := k.isLt
  simp only [hc, dif_pos hk]

end NormalizationFixed

end L20261018

#print axioms L20261018.sum_range_eq_sumCoeff
#print axioms L20261018.exists_pow_root_mul_coeff_mem_sumCoeff
