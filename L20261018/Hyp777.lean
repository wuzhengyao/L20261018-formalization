import Hyp776
import Hyp134

/-!
# S74 R3：**(甲1) 的"≤"那一半**无条件成立 —— `hne` 从 `finrank VKG ≤ 1` 上摘掉

## 为什么这一步有用

S74 R2（`Hyp776.finrank_VKG_eq_one`）把 (甲1) 归约到**一条非零杯积** `hne`。但 `hne` 的兑现
被**载体差**卡住：TauCeti 的非退化性来源（`separatingRight_localSymbol`／`tateDualityPairing_perfect`）
都在 `Field.absoluteGaloisGroup F`（`AlgebraicClosure` 载体）上，而本战役 `GaloBase.V` 用的是
`TauCeti.AbsoluteGaloisGroup F`（`SeparableClosure` 载体）—— `D84` 的"先测泛型度"在这里**不适用**
（那些定理的群是**固定**的 `Field.absoluteGaloisGroup`，不是泛型参数）。

**本轮实测**：`Hyp134.ker_dependent`（`\ker \bar v` 内任两元相关）**零假设**成立
（只要 `hp`、`∃ π, v π = 1`、`IsUnit (p : 𝒪[F])`）—— **不需要 `hne`**。
而 `Hyp148.finrank_ker_valLin_le_one` 之所以要 `hne`，只是因为它用 `hne` 去**造一个非零元**
（`exists_ne_zero_mem_ker`）。把那一处换成"结构上直接取非零元"，上界即无条件。

## 交付

| 声明 | 内容 |
|---|---|
| **`finrank_ker_le_one_of_exists_ne_zero`** | `∃ γ ≠ 0 ∈ ker v̄ ⟹ finrank ≤ 1`（把 `hne` 换成**更弱的**非平凡性） |
| **`finrank_ker_le_one`** | ★★★★ **无条件 `finrank (ker v̄) ≤ 1`**（分 `Nontrivial`／`Subsingleton` 两档） |
| **`finrank_VKG_le_one`** | ★★★★ 战役形（`v := normalizedValuation`） |
| **`finrank_VKG_eq_one_of_ne_zero`** | ★★★ `∃ y ≠ 0 ∈ VKG ⟹ finrank VKG = 1`（**新归约**） |

**⟹ (甲1) 的输入从「`∃ a₁ a₂, cup a₁ a₂ ≠ 0`」（需跨载体非退化性）降为
「`∃ y ∈ VKG, y ≠ 0`」（本战役内部，无载体问题）。**

## 诚实边界

* `[FiniteDimensional (ZMod p) (GaloBase.V F p)]`、`IsUnit (p : 𝒪[F])` 沿用既有口径（`Hyp342`／`Hyp385`）。
* `∃ y ≠ 0 ∈ VKG` **本件未兑现**：它等价于「单位群 `𝒪_F^×/𝒪_F^{×p} ≠ 1`」那一类非平凡性
  （`Hyp747.res1V_eq_zero_iff_exists_unit` 已把 `VKG` 认成单位类），仍需一块独立的基建。
  本件的价值是**把载体障碍从 (甲1) 上摘掉**，代价换成一条更弱、且纯本战役内部的非平凡性。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ## 1 `finrank (ker v̄) ≤ 1`：把 `Hyp148` 的 `hne` 换成非平凡性 -/

/-- ★★★★ **`ker v̄` 至多一维**（输入只是一条非零元）。

与 `Hyp148.finrank_ker_valLin_le_one` 的差别：那里用 `hne : cup a₁ a₂ ≠ 0` 经
`exists_ne_zero_mem_ker` 造非零元；这里直接吃非零元。**`ker_dependent` 本身零假设**。 -/
theorem finrank_ker_le_one_of_exists_ne_zero (hp : IsUnit (p : F))
    (hpu : IsUnit (p : ↥𝒪[F]))
    (h0 : ∃ γ : ↥(LinearMap.ker (valLin F p hp)), γ ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) ≤ 1 := by
  obtain ⟨π, hπ⟩ := TauCeti.exists_isUniformizer F
  rw [TauCeti.isUniformizer_def] at hπ
  obtain ⟨γ, hγne⟩ := h0
  rw [finrank_le_one_iff]
  refine ⟨γ, ?_⟩
  intro w
  rcases ker_dependent (F := F) (p := p) hp (hπ := hπ) hpu
    (w : GaloBase.V F p) (γ : GaloBase.V F p) w.2 γ.2 with h | h
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    exact ⟨c, Subtype.ext hc⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hγne (Subtype.ext hc.symm)
    refine ⟨c⁻¹, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- ★★★★ **无条件 `finrank (ker v̄) ≤ 1`**：分两档 —— 若 `ker` 平凡则 `finrank = 0`；
否则取任意非零元走上一条。 -/
theorem finrank_ker_le_one (hp : IsUnit (p : F)) (hpu : IsUnit (p : ↥𝒪[F]))
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) ≤ 1 := by
  by_cases h : Nontrivial ↥(LinearMap.ker (valLin F p hp))
  · obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(LinearMap.ker (valLin F p hp))
    exact finrank_ker_le_one_of_exists_ne_zero (F := F) (p := p) hp hpu
      ⟨a - b, fun h0 => hab (sub_eq_zero.mp h0)⟩
  · haveI : Subsingleton ↥(LinearMap.ker (valLin F p hp)) :=
      not_nontrivial_iff_subsingleton.mp h
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le 1

/-! ## 2 战役形（`v := TauCeti.normalizedValuation F`） -/

/-- ★★★★ **`finrank VKG ≤ 1`（无条件）**。

`valLin = valLinOf normalizedValuation`（`rfl`-级桥）＋ 上一条。 -/
theorem finrank_VKG_le_one (hp : IsUnit (p : F)) (hpu : IsUnit (p : ↥𝒪[F]))
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) (VKG F p (TauCeti.normalizedValuation F) hp) ≤ 1 := by
  have h := finrank_ker_le_one (F := F) (p := p) hp hpu
  rwa [← valLin_eq_valLinOf_normalizedValuation] at h

/-- ★★★★ **(甲1) 的新归约**：`VKG` 非平凡 ⟹ `finrank VKG = 1`。

与 `Hyp776.finrank_VKG_eq_one` 相比，输入从**跨载体的非零杯积** `hne` 换成本战役内部的
`∃ y ∈ VKG, y ≠ 0`。 -/
theorem finrank_VKG_eq_one_of_ne_zero (hp : IsUnit (p : F)) (hpu : IsUnit (p : ↥𝒪[F]))
    (h0 : ∃ y : VKG F p (TauCeti.normalizedValuation F) hp, y ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) (VKG F p (TauCeti.normalizedValuation F) hp) = 1 := by
  have hle := finrank_VKG_le_one (F := F) (p := p) hp hpu
  obtain ⟨γ, hγ⟩ := h0
  haveI : Nontrivial (VKG F p (TauCeti.normalizedValuation F) hp) :=
    ⟨γ, 0, fun h => hγ h⟩
  have hpos : 0 < Module.finrank (ZMod p) (VKG F p (TauCeti.normalizedValuation F) hp) :=
    Module.finrank_pos
  omega

end L20261018

#print axioms L20261018.finrank_ker_le_one_of_exists_ne_zero
#print axioms L20261018.finrank_ker_le_one
#print axioms L20261018.finrank_VKG_le_one
#print axioms L20261018.finrank_VKG_eq_one_of_ne_zero
