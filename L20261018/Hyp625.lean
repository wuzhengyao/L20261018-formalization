import L20261018.Hyp624

/-!
# S51 R18：惯性子群 `I` 的**极大理想判据** —— `I` 成为某个「剩余作用」的**核**

## 0 为什么需要这一格

`Hyp614` 的 `(CI)`（其 `hCI`）要用 `Γ_κ = Γ_F/I`。要让 `I` 成为**可辨认的核**，
必须把 `I` 的定义（`W (σ x − x) < 1`）翻译成 `↥W.valuationSubring` 的**剩余域语言**：

```
σ ∈ I  ⟺  ∀ x ∈ 𝒪_W,  σx − x ∈ 𝔪_W
```

`Valuation.mem_maximalIdeal_iff`（`a ∈ 𝔪 ↔ W a < 1`）＋ `IsLocalRing.residue_eq_zero_iff`
（`residue x = 0 ↔ x ∈ 𝔪`）给出 `residue (σx) = residue x ⟺ σx − x ∈ 𝔪`。
⟹ `I` 是「`Γ_F` 在 `κ̄ = 𝒪_W/𝔪_W` 上的作用」的**核**，`Γ_F/I` 于是可写。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`mem_inertia_iff_sub_mem_maximalIdeal`** | ★★★★★ `σ ∈ I ↔ ∀ x ∈ 𝒪_W, (σx − x) ∈ 𝔪_W` |
| **`mem_inertia_iff_residue_eq`** | ★★★★★ 同一件事的 `residue` 形态 |

## 2 诚实边界

* 仍**不证** `(CI)`；`FbarValuationHyp₄` 仍是假设。本轮**不增覆盖率**。
* **未做**：`Γ_F/I ≅ Γ_κ`（需 `κ̄` 与 `Γ_κ := Gal(κ̄/κ)` 的同一化，即 `hyp-residue-galois` 的 `φ` 的满射性）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section ResidueCriterion

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval in
/-- ★★★★★ **惯性子群的极大理想判据**：`σ ∈ I ⟺ σ 在每个 `x ∈ 𝒪_W` 上模 `𝔪_W` 不动。 -/
theorem mem_inertia_iff_sub_mem_maximalIdeal
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    σ ∈ inertia W hval ↔
      ∀ x : ↥W.valuationSubring,
        (⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩ - x)
          ∈ IsLocalRing.maximalIdeal ↥W.valuationSubring := by
  constructor
  · intro hσ x
    have hx : W (x : SeparableClosure F) ≤ 1 := by
      have h := x.2
      change W (x : SeparableClosure F) ≤ 1 at h
      exact h
    have hlt : W (σ (x : SeparableClosure F) - (x : SeparableClosure F)) < 1 := hσ _ hx
    rw [Valuation.mem_maximalIdeal_iff]
    change W (σ (x : SeparableClosure F) - (x : SeparableClosure F)) < 1
    exact hlt
  · intro h x hx
    have hx' : x ∈ W.valuationSubring := by
      change W x ≤ 1
      exact hx
    have hmem := h ⟨x, hx'⟩
    rw [Valuation.mem_maximalIdeal_iff] at hmem
    change W (σ x - x) < 1 at hmem
    exact hmem

include hval in
/-- ★★★★★ **惯性子群的剩余判据**：`σ ∈ I ⟺ σ 在 `𝒪_W/𝔪_W` 上作用平凡。 -/
theorem mem_inertia_iff_residue_eq (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    σ ∈ inertia W hval ↔
      ∀ x : ↥W.valuationSubring,
        IsLocalRing.residue ↥W.valuationSubring
            ⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩
          = IsLocalRing.residue ↥W.valuationSubring x := by
  rw [mem_inertia_iff_sub_mem_maximalIdeal W hval σ]
  constructor
  · intro h x
    have hmem := h x
    have hzero : IsLocalRing.residue ↥W.valuationSubring
        (⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩ - x) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  · intro h x
    have hsub : IsLocalRing.residue ↥W.valuationSubring
        (⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩ - x) = 0 := by
      rw [map_sub, h x, sub_self]
    exact (IsLocalRing.residue_eq_zero_iff _).mp hsub

end ResidueCriterion

end L20261018

#print axioms L20261018.mem_inertia_iff_sub_mem_maximalIdeal
#print axioms L20261018.mem_inertia_iff_residue_eq
