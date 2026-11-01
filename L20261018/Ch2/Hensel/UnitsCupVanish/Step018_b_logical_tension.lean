import L20261018.Ch2.Hensel.UnitsCupVanish.Step016_b_pinned_to_equivalence

/-!
# S39 第 8 轮（B 第 4 步）：把 B 的**逻辑张力**机检（`Hyp434`）

## 本轮的两个发现

### 1. L46 侦察（三要件齐）：**HS transgression 全生态无**

| 要件 | 读数 |
|---|---|
| 版本 | mathlib@`aa35a481`（工作区 pin）；`raw/TauCeti`（`7d75b962`）；`raw/fermat`（`aa2d8b34`）；`raw/openai-math-formalized-algebra`（`7d75b962`…见名册） |
| 内容式关键词 | `transgression`／`HochschildSerre`／`hochschild` |
| 命中清单 | mathlib：**0 命中**；TauCeti：仅 `Profinite/Free/Transgression.lean`（**自由 pro-`p` 群**的 transgression，非 HS）；FLT／openai-algebra：同名不同物（`srlf1_rd120t3_transgressionSurjection`／`IntegralTransgressionFinite`） |

⟹ **HS transgression `H¹(H,A)^{G/H} → H²(G/H,A^H)` 必须自建**（照 NS​W `prop-1.6.6`）。

### 2. ⚠ **逻辑张力**：若 `residueSpan = ⊤`，则 `Disjoint` 会迫使 `Φ = 0`

本轮机检两条（纯抽象，两行）：

* **`phi_apply_eq_zero_of_residueSpan_eq_top`**：`residueSpan cup val = ⊤` ＋ `Disjoint (range Φ) residueSpan`
  ⟹ `∀ y, Φ y = 0`。
* **`residueSpan_ne_top_of_exists_phi_ne_zero`**（反证形）：若存在 `y` 使 `Φ y ≠ 0`
  且 `Disjoint` 成立，则 **`residueSpan ≠ ⊤`**。

**为什么这重要**：论文 `(R2)` 说 `∂₂` 在**单位杯积**上为零。若
（a）`residueSpan` 恰是单位杯积张成的块，且
（b）对 `κ = ℂ(t)` 有 `im(∪_κ) = H²(κ, μ_p^{⊗2})`（Merkurjev），
则 `residueSpan = ⊤`（在 `H²(F)` 里看即 `= range(infl₂)`）。
此时 `Disjoint` 会迫使 `Φ = 0`，即 `(c)∪(π) = 0` —— 与驯符号 `∂₂((c)∪(π)) = c̄ ≠ 0` **冲突**。

⟹ **在花钱建 `tg` 之前必须先裁决**：`residueSpan` 是否真的等于 `range(infl₂)`？
若等于，则本战役的 **`R2′`／`Disjoint` 形式化对 `∂₂` 的两条性质而言过强**，
而 `∂₂` 的正确形式化必须走**系数层**（`μ_p^{⊗j}` 的 Tate 扭曲），
不能停留在 `H²(F, Z/p)` 的裸 cup 上。
本件把该张力**机检为硬约束**（`⚠-contentious`，待人类裁决）。

## 机检件

| 件 | 内容 |
|---|---|
| **`disjoint_iff_forall`** | `Disjoint` 的点式等价：`∀ y, Φ y ∈ residueSpan → Φ y = 0` |
| **`phi_apply_eq_zero_of_residueSpan_eq_top`** | ★★★★ `residueSpan = ⊤` ＋ `Disjoint ⟹ Φ = 0` |
| **`residueSpan_ne_top_of_exists_phi_ne_zero`** | ★★★★★ 反证形：`∃ y, Φ y ≠ 0` ＋ `Disjoint ⟹ residueSpan ≠ ⊤` |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace L20261018

section Tension

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- ★★★★ **`Disjoint` 的点式等价**：`im Φ` 中每个落在 `residueSpan` 里的元素都是 `0`。 -/
theorem disjoint_iff_forall (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V) :
    Disjoint (LinearMap.range (residuePhi cup val π)) (residueSpan cup val)
      ↔ ∀ y : ↥(LinearMap.ker val),
          residuePhi cup val π y ∈ residueSpan cup val → residuePhi cup val π y = 0 := by
  rw [Submodule.disjoint_def]
  constructor
  · intro h y hy
    exact h _ ⟨y, rfl⟩ hy
  · rintro h z ⟨y, rfl⟩ hz
    exact h y hz

/-- ★★★★ **张力一**：若 `residueSpan = ⊤`，则 `Disjoint` 迫使 `Φ = 0`。 -/
theorem phi_apply_eq_zero_of_residueSpan_eq_top (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (htop : residueSpan cup val = ⊤)
    (hd : Disjoint (LinearMap.range (residuePhi cup val π)) (residueSpan cup val)) :
    ∀ y : ↥(LinearMap.ker val), residuePhi cup val π y = 0 := by
  rw [disjoint_iff_forall] at hd
  intro y
  exact hd y (by rw [htop]; exact Submodule.mem_top)

/-- ★★★★★ **张力二（反证形，本轮的硬约束）**：
若存在 `y` 使 `Φ y ≠ 0`（如驯符号给 `(c)∪(π) ≠ 0`），**且** `Disjoint` 成立，
则 **`residueSpan ≠ ⊤`**。

⟹ 论文 `(R2)` 若真能推出 `residueSpan = ⊤`（Merkurjev 的 `im(∪_κ) = H²(κ)`），
则与本战役的 `Disjoint`（`R2′`）**不能同时成立** —— 必须裁决哪一侧的形式化不对。 -/
theorem residueSpan_ne_top_of_exists_phi_ne_zero (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (hex : ∃ y : ↥(LinearMap.ker val), residuePhi cup val π y ≠ 0)
    (hd : Disjoint (LinearMap.range (residuePhi cup val π)) (residueSpan cup val)) :
    residueSpan cup val ≠ ⊤ := by
  intro htop
  obtain ⟨y, hy⟩ := hex
  exact hy (phi_apply_eq_zero_of_residueSpan_eq_top cup val π htop hd y)

end Tension

end L20261018

#print axioms L20261018.disjoint_iff_forall
#print axioms L20261018.phi_apply_eq_zero_of_residueSpan_eq_top
#print axioms L20261018.residueSpan_ne_top_of_exists_phi_ne_zero
