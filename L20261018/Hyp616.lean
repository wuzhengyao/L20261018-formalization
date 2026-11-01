import Hyp615
import Hyp187

/-!
# S51 R7：**`μ_p ⊆ F ⟹ μ_p ⊆ κ` 的完整链** ＋ 延拓假设的类型锁定

## 0 补的是哪一格

`Hyp615.isPrimitiveRoot_residue` 已给「`IsPrimitiveRoot ζ p`（`ζ ∈ ↥𝒪[F]`）⟹
`IsPrimitiveRoot (ρ ζ) p`」。但论文只假设 **`μ_p ⊆ F`**——单位根住在 `F` 里，**不在** `𝒪[F]` 里。
本件补上这一步：

```
μ_p ⊆ F  ⟹  ζ ∈ 𝒪[F] 且为单位  ⟹  ρ ζ 是 κ 中的本原 p 次单位根
```

第一步的数学只有一行：`ζ^p = 1` ⟹ `(v ζ)^p = 1` ⟹ `v ζ = 0`（`Multiplicative ℤ` 无挠）
⟹ `0 ≤ v ζ` ⟹ `ζ ∈ 𝒪[F]`（`ValCompat.mem_integer`）。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| `toAdd_eq_zero_of_pow_eq_one` | `u^p = 1` ⟹ `(v u).toAdd = 0`（`Multiplicative ℤ` 无挠） |
| `mem_integer_of_pow_eq_one` | 同上 ⟹ `(u : F) ∈ 𝒪[F]` |
| **`exists_isPrimitiveRoot_integer`** | ★★★★ `μ_p ⊆ F` ⟹ **存在 `ζ' : ↥𝒪[F]` 本原且 `(ζ' : F) = ζ`** |
| **`exists_isPrimitiveRoot_residue`** | ★★★★★ **完整链**：`μ_p ⊆ F` ⟹ **存在 `κ` 中的本原 `p` 次单位根** |
| **`FbarValuationHyp`** | ★★★ **类型锁定**：`v` 延拓到 `F̄` 的数据形态（[[hyp-fbar-valuation]] §5 步 1） |

## 2 诚实边界

* `exists_isPrimitiveRoot_residue` 要求 `IsUnit (p : ↥𝒪[F])`（由 `char κ ≠ p` 供给）与
  `ValCompat v`——两者都是论文设定里已有的。
* `FbarValuationHyp`（第 4 项）**只是把目标钉死**（`∃ w : F̄ˣ →* Multiplicative ℚ` 延拓 `v`），
  **不是**定理；Krull 延拓（[[hyp-fbar-valuation]] §5 步 2–3）仍未做。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

/-! ## 1 `v ζ = 0` 与 `ζ ∈ 𝒪[F]` -/

section Integer

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ} {p : ℕ}

/-- ★★★★ `u^p = 1` ⟹ `v u = 0`（`Multiplicative ℤ` 无挠）。 -/
theorem toAdd_eq_zero_of_pow_eq_one (hp0 : p ≠ 0) {u : Fˣ} (hu : (u : F) ^ p = 1) :
    (v u).toAdd = 0 := by
  have hu1 : u ^ p = 1 := Units.ext hu
  have hpow : (v u) ^ p = 1 := by rw [← map_pow, hu1, map_one]
  -- 局部版的 `toAdd_pow`（库内名字不可用，手写归纳）
  have hkey : ∀ n : ℕ, Multiplicative.toAdd ((v u) ^ n) = (n : ℤ) * (v u).toAdd := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        show Multiplicative.toAdd ((v u) ^ m) + Multiplicative.toAdd (v u)
          = ((m + 1 : ℕ) : ℤ) * Multiplicative.toAdd (v u)
        rw [ih]
        push_cast
        ring
  have h2 := congrArg Multiplicative.toAdd hpow
  rw [hkey p] at h2
  have h3 : (p : ℤ) * (v u).toAdd = 0 := by simpa using h2
  have hpZ : ((p : ℤ)) ≠ 0 := by exact_mod_cast hp0
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hpZ
  · exact h

/-- ★★★★ `u^p = 1` ⟹ `(u : F) ∈ 𝒪[F]`。 -/
theorem mem_integer_of_pow_eq_one (hv : ValCompat (F := F) v) (hp0 : p ≠ 0) {u : Fˣ}
    (hu : (u : F) ^ p = 1) : (u : F) ∈ 𝒪[F] :=
  hv.mem_integer u (by rw [toAdd_eq_zero_of_pow_eq_one hp0 hu])

end Integer

/-! ## 2 单位根落进 `𝒪[F]` 并保持本原 -/

section PrimitiveInteger

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- ★★★★ **`μ_p ⊆ F` ⟹ 存在 `↥𝒪[F]` 中的本原 `p` 次单位根，其像为 `ζ`**。 -/
theorem exists_isPrimitiveRoot_integer (hv : ValCompat (F := F) v) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ ζ' : ↥𝒪[F], IsPrimitiveRoot ζ' p ∧ (ζ' : F) = ζ := by
  have hp0 : p ≠ 0 := NeZero.ne p
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp0] at hζp
    exact zero_ne_one hζp
  obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = ζ := ⟨Units.mk0 ζ hζ0, rfl⟩
  have hu : (u : F) ^ p = 1 := hζp
  have hmem : (u : F) ∈ 𝒪[F] := mem_integer_of_pow_eq_one hv hp0 hu
  refine ⟨⟨(u : F), hmem⟩, ?_, rfl⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  have hpow' : (⟨(u : F), hmem⟩ : ↥𝒪[F]) ^ p = 1 := by
    refine Subtype.ext ?_
    show ((⟨(u : F), hmem⟩ : ↥𝒪[F]) : F) ^ p = ((1 : ↥𝒪[F]) : F)
    rw [hu]
    rfl
  refine orderOf_eq_prime hpow' ?_
  intro hcon
  have hu1 : (u : F) = 1 := by
    have : ((⟨(u : F), hmem⟩ : ↥𝒪[F]) : F) = ((1 : ↥𝒪[F]) : F) := by rw [hcon]
    simpa using this
  rw [IsPrimitiveRoot.iff_orderOf, hu1, orderOf_one] at hζ
  exact (Fact.out : p.Prime).ne_one hζ.symm

/-- ★★★★★ **完整链**：`μ_p ⊆ F` ⟹ `κ` 中存在本原 `p` 次单位根（即 **`μ_p ⊆ κ`**）。 -/
theorem exists_isPrimitiveRoot_residue (hv : ValCompat (F := F) v)
    (hp : IsUnit (p : ↥𝒪[F])) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    ∃ w : IsLocalRing.ResidueField ↥𝒪[F], IsPrimitiveRoot w p := by
  obtain ⟨ζ', hζ', rfl⟩ := exists_isPrimitiveRoot_integer (F := F) p hv hζ
  exact ⟨IsLocalRing.residue ↥𝒪[F] ζ', isPrimitiveRoot_residue (F := F) p hp hζ'⟩

end PrimitiveInteger

/-! ## 3 延拓假设的类型锁定（[[hyp-fbar-valuation]] §5 步 1） -/

section TypeLock

variable {F : Type} [Field F]

/-- ★★★ **类型锁定**：`v` 延拓到 `F̄ = SeparableClosure F` 的数据形态（值群扩到 `ℚ`）。

⚠ 这是**假设的形态**，不是定理；Krull 延拓的存在性是独立目标（见 `wiki/hyp-fbar-valuation.md`）。 -/
def FbarValuationHyp (v : Fˣ →* Multiplicative ℤ) : Prop :=
  ∃ w : (SeparableClosure F)ˣ →* Multiplicative ℚ,
    ∀ a : Fˣ,
      ((w (Units.map (algebraMap F (SeparableClosure F)).toMonoidHom a)).toAdd : ℚ)
        = ((v a).toAdd : ℚ)

end TypeLock

end L20261018

#print axioms L20261018.toAdd_eq_zero_of_pow_eq_one
#print axioms L20261018.mem_integer_of_pow_eq_one
#print axioms L20261018.exists_isPrimitiveRoot_integer
#print axioms L20261018.exists_isPrimitiveRoot_residue
