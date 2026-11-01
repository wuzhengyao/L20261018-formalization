import L20261018.Ch2.Hensel.ResidueMap.Step062_mu_p_residue_full_chain

/-!
# S51 R8：`μ_p ⊆ κ` 升格为**可用的 mathlib 实例** ＋ 延拓假设**类型锁定的更正**

## 0 两件事

**(甲)** S51 R6–R7 已机检 `μ_p ⊆ F ⟹ ∃ w : κ, IsPrimitiveRoot w p`。但下游要的是
**mathlib 的类** `HasEnoughRootsOfUnity κ p`（剩余侧 Kummer 理论的前提）。本件把它做成实例级事实。

`HasEnoughRootsOfUnity M n` 有两个字段（`Mathlib/RingTheory/RootsOfUnity/EnoughRootsOfUnity.lean:27`）：
```
prim : ∃ m : M, IsPrimitiveRoot m n
cyc  : IsCyclic (rootsOfUnity n M)
```
`cyc` **是 mathlib 的实例**（`rootsOfUnity.isCyclic`，`Basic.lean:249`，对任意 `CommRing`），
故只需补 `prim`。

**(乙) ⚠ 更正 S51 R7 的类型锁定**（`Hyp616.FbarValuationHyp`）：
它把延拓写成**群同态** `w : F̄ˣ →* Multiplicative ℚ`。**这不够**——
群同态**没有**加法相容性（超度量不等式），而定义赋值环 `𝒪_w = {x | w x ≤ 1}` 并让它成为**环**
正需要那条不等式。本件给出**正确**的锁定：用 mathlib 的 `Valuation`（不等式内建），
并用「与 `𝒪[F]` 的相容」把「延拓 `v`」表述为可机检的条件。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`hasEnoughRootsOfUnity_residue`** | ★★★★★★ **`HasEnoughRootsOfUnity F p ⟹ HasEnoughRootsOfUnity κ p`**（`μ_p ⊆ κ` 的实例形态） |
| **`FbarValuationHyp'`** | ★★★★★ **正确**的类型锁定：`∃ W : Valuation F̄ (WithZero (Multiplicative ℚ))`，且 `∀ x : F, W (x) ≤ 1 ↔ x ∈ 𝒪[F]` |
| — | 对照说明（散文，非声明）：R7 的群同态形态**严格更弱**，推不出本件形态（见 §3） |

## 2 `hasEnoughRootsOfUnity_residue` 的证明

```
HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p  →  ∃ ζ : F, IsPrimitiveRoot ζ p
Hyp616.exists_isPrimitiveRoot_residue hv hp hζ    →  ∃ w : κ, IsPrimitiveRoot w p      -- prim
rootsOfUnity.isCyclic                             →  IsCyclic (rootsOfUnity p κ)       -- cyc
```

## 3 诚实边界

* `FbarValuationHyp'` **仍是假设**（Krull 延拓的存在性未证，见 `wiki/hyp-fbar-valuation.md` §5 步 2–3）。
* 本件**不**声称 `FbarValuationHyp`（R7 版）与 `FbarValuationHyp'` 等价：前者严格**更弱**，
  故 R7 的锁定**不足**——这是本轮要登记的更正，不是定理。
* `hasEnoughRootsOfUnity_residue` 的假设：`ValCompat v` ＋ `IsUnit (p : ↥𝒪[F])` ＋ `[NeZero p] [Fact p.Prime]`。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

/-! ## 甲：`μ_p ⊆ κ` 的实例形态 -/

section ResidueRootsInstance

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  (p : ℕ) [NeZero p] [Fact p.Prime]
  {v : Fˣ →* Multiplicative ℤ}

/-- ★★★★★★ **`μ_p ⊆ F ⟹ μ_p ⊆ κ`（mathlib 实例形态）**。

剩余侧 Kummer 理论的类 `HasEnoughRootsOfUnity κ p` 由 `μ_p ⊆ F` 的同一类事实**推出**：
`prim` 来自 `Hyp616.exists_isPrimitiveRoot_residue`，`cyc` 是 mathlib 的 `rootsOfUnity.isCyclic`。 -/
theorem hasEnoughRootsOfUnity_residue (hv : ValCompat (F := F) v)
    (hp : IsUnit (p : ↥𝒪[F])) [hF : HasEnoughRootsOfUnity F p] :
    HasEnoughRootsOfUnity (IsLocalRing.ResidueField ↥𝒪[F]) p where
  prim := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p
    exact exists_isPrimitiveRoot_residue (F := F) p hv hp hζ
  cyc := rootsOfUnity.isCyclic _ p

end ResidueRootsInstance

/-! ## 乙：延拓假设的**正确**类型锁定 -/

section TypeLockCorrected

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★★ **正确**的类型锁定：`v` 延拓到 `F̄ = SeparableClosure F`。

用 mathlib 的 `Valuation`（**超度量不等式内建**，故其赋值环 `W.valuationSubring` 是**环**），
并用「赋值环与 `𝒪[F]` 一致」把「延拓 `v`」写成可机检的逐元条件。

⚠ 这是**假设的形态**，不是定理（Krull 延拓，见 `wiki/hyp-fbar-valuation.md` §5 步 2–3）。 -/
def FbarValuationHyp' : Prop :=
  ∃ W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)),
    ∀ x : F, W (algebraMap F (SeparableClosure F) x) ≤ 1 ↔ x ∈ 𝒪[F]

end TypeLockCorrected

end L20261018

#print axioms L20261018.hasEnoughRootsOfUnity_residue
