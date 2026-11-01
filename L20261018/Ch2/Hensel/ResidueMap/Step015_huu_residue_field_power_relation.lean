import L20261018.Ch2.Hensel.ResidueMap.Step014_ker_v_one_dim_group_core

/-!
# R975：`hdep` 的域论侧 —— 剩余域单位群中任两元成幂关系（模 `p` 次幂）

R974 已证群论核心（`exists_pow_eq_of_pow_eq_one`）。本文件把它用到**剩余域单位群** `𝓀[F]ˣ` 上。

**★ 关键事实（本轮实测）**：`Finite 𝓀[F]` **是** `IsNonarchimedeanLocalField` 的现成实例
（`example : Finite 𝓀[F] := inferInstance` 过；TauCeti 自己在
`LocalField/QuadraticForm/OddResidue/Symbol.lean:41` 与 `LocalField/ResidueCorrespondence.lean:52`
就是 `Fintype.ofFinite 𝓀[K]`）。故本路线**不需要**额外的有限性假设。

结论：`b` 不是 `p` 次幂 ⟹ `∃ n, a · b⁻ⁿ` 是 `p` 次幂（在 `𝓀[F]ˣ` 中）。
下一轮用 `Hyp114.unitPow_iff_residuePow` 把它抬回 `Fˣ`，即得 `hdep`。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime]

/-- **剩余域单位群中任两元成幂关系（模 `p` 次幂）**。

对 `G := 𝓀[F]ˣ`、`H := (powMonoidHom p).range` 用 `exists_pow_eq_of_pow_eq_one`：
有限域单位群循环，商群的指数整除 `p`（因为 `y^p ∈ H`）。 -/
theorem residue_exists_mul_pow_inv_mem_range (a b : 𝓀[F]ˣ)
    (hb : b ∉ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range) :
    ∃ n : ℕ, a * (b ^ n)⁻¹ ∈ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range := by
  classical
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  set H : Subgroup 𝓀[F]ˣ := (powMonoidHom p).range with hHdef
  -- 商群指数整除 `p`
  have hpow : ∀ x : 𝓀[F]ˣ ⧸ H, x ^ p = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  -- `b ∉ H` ⟺ 商中 `↑b ≠ 1`
  have hbq : (QuotientGroup.mk b : 𝓀[F]ˣ ⧸ H) ≠ 1 := by
    intro h
    exact hb (QuotientGroup.eq_one_iff b |>.mp h)
  obtain ⟨n, hn⟩ := exists_pow_eq_of_pow_eq_one H p hpow a b hbq
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  have h1 : (QuotientGroup.mk a : 𝓀[F]ˣ ⧸ H) = QuotientGroup.mk (b ^ n) := by
    rw [hn, QuotientGroup.mk_pow]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]

end L20261018
#print axioms L20261018.residue_exists_mul_pow_inv_mem_range
