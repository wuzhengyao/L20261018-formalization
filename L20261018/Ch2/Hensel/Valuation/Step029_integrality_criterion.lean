import L20261018.Ch2.Hensel.Valuation.Step028_reindex_eliminate_s
import L20261018.Witness.Step006_val_compat_complete_field
import TauCeti.NumberTheory.LocalField.Uniformizer

/-!
# R1050（**S29 · ④.1 收口**）：整性判据 —— `N(x) ∈ 𝒪_F ⟹ x ∈ 𝒪_F[s]`

本文件机检论文 §2.4 的**第 3 步本体**（S28 配方的最后一块）：

```
N_{L/F}(x) ∈ 𝒪_F   ⟹   ∃ c : ℕ → ↥𝒪_F,  x = Σ_{i<p} cᵢ sⁱ
                    且  red (N x) = (red (c 0))^p
```

（模型：`L := AdjoinRoot_F (Xᵖ − Cπ)`、`s := root`、`𝒪_F := Valuation.integer (ValuativeRel.valuation F)`、
`red := IsLocalRing.residue ↥𝒪_F`。）

## 论证（极小性 ＋ 消去 `s`，零件全部已有）

1. 由 `Hyp192`：`∃ n c, sⁿ·x = sumCoeff π c`。取**最小**的 `n`（`Nat.find`）。
2. 若 `n ≥ 1`：`Hyp194`（`coeff_zero_mem_maximalIdeal`）给 **`c 0 ∈ 𝔪`**；
   `Hyp191`（`𝔪 = (π)`）给 `c 0 = b·c₀'`。
3. `Hyp196.sumCoeff_eq_root_mul`：`Σ cᵢ sⁱ = s · Σ c'ⱼ sʲ`（`c'_{p−1} = c₀'`、`c'ⱼ = c_{j+1}`）——
   用的是 `Hyp195`（拆首项）＋ `Hyp196.sum_range_split_last`（拆末项）＋ `sᵖ = of π`。
4. `sⁿ x = s·(s^{n−1}x) = s·Σ c'ⱼ sʲ` ⟹ 用 `Hyp196.root_mul_left_cancel` **消去 `s`**
   ⟹ `s^{n−1}x = Σ c'ⱼ sʲ` ⟹ 与 `n` 极小性矛盾。故 **`n = 0`**。
5. `n = 0` ⟹ `x = Σ cᵢ sⁱ`；`Hyp190.norm_residue_eq_pow` 给 `red (N x) = (red (c 0))^p`。

## 与提示词的偏差（**更强，且是必要的**）

提示词 ④.1 假设「`N(x)` 是**单位**」。实测**不需要**：`Hyp194` 的推导只用 `n ≥ 1`
（`red b = 0` 使 `red (πⁿ N x) = 0`），而极小性论证只用「`c 0 ∈ 𝔪`」。故本件陈述为
**「`N(x) ∈ 𝒪_F` ⟹ 整」**，单位假设留给 ④.2（那里才要用 `red u = (red c₀)ᵖ` 是 `p` 次幂）。

## 非空性（L1／L10①）

假设类非空：`ValCompat` 在任一完备局部域上由 `Hyp189` 给出，`v π = ofAdd 1` 由
`TauCeti.exists_isUniformizer` 给出（见文末 `example`）；`N(x) ∈ 𝒪_F` 由 `x = 1` 满足。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section Integrality

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **④.1 整性判据**：`N(x) ∈ 𝒪_F` ⟹ `x ∈ 𝒪_F[s]`，且 `red (N x) = (red (c 0))^p`。 -/
theorem exists_coeff_of_norm_mem_integer (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    {x : AdjoinRoot (X ^ p - C (π : F))} (hx : (Algebra.norm F x : F) ∈ 𝒪[F]) :
    ∃ c : ℕ → ↥𝒪[F], x = sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))
      ∧ IsLocalRing.residue ↥𝒪[F] ⟨Algebra.norm F x, hx⟩
          = (IsLocalRing.residue ↥𝒪[F] (c 0)) ^ p := by
  classical
  have hπ𝒪 : (π : F) ∈ 𝒪[F] := valCompat_uniformizer_mem_integer (F := F) hv hπ
  set b : ↥𝒪[F] := ⟨(π : F), hπ𝒪⟩ with hbdef
  have hb : (b : F) = (π : F) := rfl
  obtain ⟨B, hB⟩ := basis_root_pow (F := F) p π
  -- 取极小的 `n`
  set P : ℕ → Prop := fun n => ∃ c : ℕ → ↥𝒪[F],
    (AdjoinRoot.root (X ^ p - C (π : F))) ^ n * x
      = sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F)) with hP
  have hex : ∃ n, P n := exists_pow_root_mul_coeff_mem_sumCoeff (F := F) p hv hπ x
  set n := Nat.find hex with hn
  obtain ⟨c, hc⟩ : P n := Nat.find_spec hex
  have hmin : ∀ m < n, ¬ P m := fun m hm => Nat.find_min hex hm
  have hn0 : n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h
    · exfalso
      -- `n ≥ 1`：常数项在 `𝔪` 中
      have hmem : (c 0 : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
        coeff_zero_mem_maximalIdeal (F := F) p hv hπ hp2 (b := b) hb (x := x) (n := n)
          h (c := c) hc hx
      obtain ⟨c₀, hc₀⟩ := exists_mul_uniformizer_of_mem_maximalIdeal (F := F) hv hπ hb hmem
      -- 提出一个 `s`
      have hsplit : sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))
          = (AdjoinRoot.root (X ^ p - C (π : F)))
            * sumCoeff (F := F) p π
                (fun j => ((if j = p - 1 then c₀ else c (j + 1) : ↥𝒪[F]) : F)) :=
        sumCoeff_eq_root_mul (F := F) p π hb (c := c) (c₀ := c₀) hc₀
      -- 降一阶
      have hstep : (AdjoinRoot.root (X ^ p - C (π : F))) ^ n * x
          = (AdjoinRoot.root (X ^ p - C (π : F)))
            * ((AdjoinRoot.root (X ^ p - C (π : F))) ^ (n - 1) * x) := by
        conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel h).symm]
        rw [pow_succ', mul_assoc]
      have hcontra : P (n - 1) := by
        refine ⟨fun j => if j = p - 1 then c₀ else c (j + 1), ?_⟩
        exact root_mul_left_cancel (F := F) p π (hstep ▸ (hc.trans hsplit))
      exact hmin (n - 1) (by omega) hcontra
  have hxe : x = sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F)) := by
    rw [hn0] at hc
    simpa using hc
  refine ⟨c, hxe, ?_⟩
  have hN : (⟨Algebra.norm F x, hx⟩ : ↥𝒪[F])
      = ⟨Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))),
          norm_mem_integer (F := F) p π hb hB c⟩ := by
    apply Subtype.ext
    show (Algebra.norm F x : F)
      = (Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))) : F)
    rw [hxe]
  rw [hN]
  exact norm_residue_eq_pow (F := F) p hv hπ hb (B := B) hB (c := c)
    (norm_mem_integer (F := F) p π hb hB c)

end Integrality

/-- **非空性见证（L1／L10①）**：`ValCompat` ＋ 「`v π = ofAdd 1`」的假设类非空 ——
任一完备局部域上都可取 `v := normalizedValuation`（`Hyp189`）与 `π := 某个一致化元`
（`TauCeti.exists_isUniformizer`）。 -/
example (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ (v : Kˣ →* Multiplicative ℤ) (π : Kˣ),
      ValCompat (F := K) v ∧ v π = Multiplicative.ofAdd (1 : ℤ) := by
  obtain ⟨π, hπ⟩ := TauCeti.exists_isUniformizer (K := K)
  exact ⟨_, π, valCompat_of_localField, hπ⟩

end L20261018

#print axioms L20261018.exists_coeff_of_norm_mem_integer
