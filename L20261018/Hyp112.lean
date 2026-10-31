import Hyp109

/-!
# 第 4 章 T5：`raw/L20261018.tex:1646` 的未编号推论（4.4）—— 维数簿记

论文（`:1646`）：

> 若 $d_F=\dim_{\Fp}H^1(F,\mu_p)<\infty$，则由 $U^\perp=\ker\Phi=0$ 和秩--零化度公式得到
> $\rank(\Phi)=d_F$。若再记 $d_K=\dim_{\Fp}H^1(K,\mu_p)$，则 $d_F=d_K+1$，故 $\rank(\Phi)=d_K+1$。
> 特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。

三块，全部在 `Hyp109.ResidueCupData` 的抽象层：

| 论文 | 声明 |
|---|---|
| `rank(Φ) = d_F`（秩--零化度 ＋ `ker Φ = 0`） | `finrank_range_commonCupMap` |
| `d_F = d_K + 1` | `finrank_eq_finrank_add_one` |
| `d_K = 1 ⟹ rank(Φ) = 2` | `corollary_4_4` |
| 与 `rank(Φ) ≥ 3` 矛盾 | `corollary_4_4_contradiction` |

`d_F = d_K + 1` 的证明用 `ker \bar v = range inf`（`ker_val_eq_range_infl`）＋
秩--零化度：$\bar v$ 满（`\bar v(\pi)=1`）、$\inf$ 单（`inj_infl`）。
**注**：这也是 `inj_infl` 在整条链上唯一被用到的地方（T3 的证明没用到它）。
-/

set_option maxHeartbeats 2000000

namespace L20261018

namespace ResidueCupData

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {VK : Type*} [AddCommGroup VK] [Module k VK]
variable [NeZero (2 : k)]

/-- `v̄` 满射（`v̄(π) = 1`）。 -/
theorem val_surjective (D : ResidueCupData k V H2 VK) : Function.Surjective D.val := by
  intro y
  refine ⟨y • D.pi, ?_⟩
  rw [map_smul, D.val_pi, smul_eq_mul, mul_one]

/-- `ker v̄ = range inf`：(⊇) 是 `val_infl`；(⊆) 用赋值分解 `x = inf x₀ + mπ`，`v̄x = m = 0`。 -/
theorem ker_val_eq_range_infl (D : ResidueCupData k V H2 VK) :
    LinearMap.ker D.val = LinearMap.range D.infl := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x₀, m, hxm⟩ := D.split x
    have hm : m = 0 := by
      have h : D.val x = m := by
        rw [hxm, map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one]
      rw [hx] at h
      exact h.symm
    rw [LinearMap.mem_range]
    refine ⟨x₀, ?_⟩
    rw [hxm, hm, zero_smul, add_zero]
  · intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    rw [LinearMap.mem_ker, D.val_infl]

/-- **`d_F = d_K + 1`**（论文 4.4 的第二步）。 -/
theorem finrank_eq_finrank_add_one (D : ResidueCupData k V H2 VK) [FiniteDimensional k V] :
    Module.finrank k V = Module.finrank k VK + 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker D.val (V₂ := k)
  have htop : LinearMap.range D.val = ⊤ := LinearMap.range_eq_top.mpr D.val_surjective
  have hrange : Module.finrank k ↥(LinearMap.range D.val) = 1 := by
    rw [htop]
    rw [(Submodule.topEquiv (R := k) (M := k)).finrank_eq, Module.finrank_self]
  have hker : Module.finrank k ↥(LinearMap.ker D.val) = Module.finrank k VK := by
    rw [D.ker_val_eq_range_infl, ← (LinearEquiv.ofInjective D.infl D.inj_infl).finrank_eq]
  rw [hrange, hker] at hrn
  omega

/-- **`rank(Φ) = d_F`**（论文 4.4 的第一步，秩--零化度 ＋ `ker Φ = 0`）。 -/
theorem finrank_range_commonCupMap (D : ResidueCupData k V H2 VK) [FiniteDimensional k V] (a1 a2 : V)
    (hker : LinearMap.ker (commonCupMap D.cup a1 a2) = ⊥) :
    Module.finrank k ↥(commonCupMap D.cup a1 a2).range = Module.finrank k V := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (commonCupMap D.cup a1 a2) (V₂ := H2 × H2)
  rw [hker, finrank_bot] at hrn
  omega

/-- **4.4（未编号推论）**：`d_K = 1` 时 `rank(Φ) = 2` 且 `d_F = 2`。 -/
-- @source file=raw/L20261018.tex locator=line:1646 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4 (D : ResidueCupData k V H2 VK) [FiniteDimensional k V] (a1 a2 : V)
    (hne : D.cup a1 a2 ≠ 0)
    (hval : ∃ u ∈ plane (k := k) a1 a2, D.val u ≠ 0)
    (hK1 : Module.finrank k VK = 1) :
    Module.finrank k ↥(commonCupMap D.cup a1 a2).range = 2 ∧ Module.finrank k V = 2 := by
  have hU0 : orth D.cup a1 a2 = ⊥ := D.vanishing a1 a2 hne hval
  have hker : LinearMap.ker (commonCupMap D.cup a1 a2) = ⊥ := hU0
  have hrank : Module.finrank k ↥(commonCupMap D.cup a1 a2).range = Module.finrank k V :=
    D.finrank_range_commonCupMap a1 a2 hker
  have hdF : Module.finrank k V = 2 := by
    rw [D.finrank_eq_finrank_add_one, hK1]
  exact ⟨by rw [hrank, hdF], hdF⟩

/-- **4.4 的矛盾形态**：`d_K = 1` 时 `rank(Φ) = 2`，与 `thm:rank-barrier`(2) 的
`3 ≤ rank(Φ)` 矛盾。 -/
theorem corollary_4_4_contradiction (D : ResidueCupData k V H2 VK) [FiniteDimensional k V] (a1 a2 : V)
    (hne : D.cup a1 a2 ≠ 0)
    (hval : ∃ u ∈ plane (k := k) a1 a2, D.val u ≠ 0)
    (hK1 : Module.finrank k VK = 1)
    [Module.Finite k ↥(commonCupMap D.cup a1 a2).range]
    (h3 : (3 : Cardinal) ≤ Module.rank k ↥(commonCupMap D.cup a1 a2).range) : False := by
  obtain ⟨h2, _⟩ := D.corollary_4_4 a1 a2 hne hval hK1
  have h2' : Module.rank k ↥(commonCupMap D.cup a1 a2).range = (2 : Cardinal) := by
    rw [← Module.finrank_eq_rank, h2]
    norm_num
  rw [h2'] at h3
  exact absurd h3 (by norm_num)

end ResidueCupData

end L20261018

#print axioms L20261018.ResidueCupData.ker_val_eq_range_infl
#print axioms L20261018.ResidueCupData.finrank_eq_finrank_add_one
#print axioms L20261018.ResidueCupData.finrank_range_commonCupMap
#print axioms L20261018.ResidueCupData.corollary_4_4
#print axioms L20261018.ResidueCupData.corollary_4_4_contradiction
