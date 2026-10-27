import L20261018.Hyp53
import Mathlib.FieldTheory.KummerExtension

/-!
# `(1b)` 第一阶段：Kummer 扩张 `L = K(a^{1/p})`、生成元 `α` 与 `σ(α) = ζ_p α`

非退化支（`a ∉ K^{×p}`）要把呈现代数 `SymbolAlg K p a b ζ` 认成**循环交叉积**：
`L := K(a^{1/p})` 上取 `σ(α) = ζ α`（`α^p = a`），再用 carry 余环 `c` 造 `CrossedProduct c`。

本文件提供第一批构件（全取自 mathlib `FieldTheory/KummerExtension`，不自建）：
`irreducible`、`L`（`AdjoinRoot` 模型）、`α`、`α_pow`、`σ`、`σ_α`，以及 `Structure` 段里的
域/Galois/循环结构与 `[L:K] = p`。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolKummerField

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

/-- `a` 不是 `p` 次幂 ⟹ `X ^ p - C a` 不可约（mathlib）。 -/
theorem irreducible (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a : K[X]) :=
  X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) ha

/-- **Kummer 扩张**的 `AdjoinRoot` 模型：`K(a^{1/p}) = K[p√a]`。 -/
abbrev L (K : Type u) [Field K] (p : ℕ) (a : K) : Type u :=
  AdjoinRoot (X ^ p - C a : K[X])

/-- 生成元 `α`（`X` 在 `AdjoinRoot` 中的像）。 -/
noncomputable def α : L K p a := AdjoinRoot.root (X ^ p - C a : K[X])

/-- **`α ^ p = a`**。 -/
theorem α_pow : (α (K := K) (p := p) (a := a)) ^ p = algebraMap K (L K p a) a := by
  have h := AdjoinRoot.eval₂_root (X ^ p - C a : K[X])
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  have h' : (AdjoinRoot.root (X ^ p - C a : K[X])) ^ p - algebraMap K (L K p a) a = 0 := h
  rwa [sub_eq_zero] at h'

/-- **`σ : α ↦ ζ α`**（mathlib 的 `autAdjoinRootXPowSubC`）。 -/
noncomputable def σ (hζ : IsPrimitiveRoot ζ p) : L K p a ≃ₐ[K] L K p a :=
  autAdjoinRootXPowSubC p a (rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one)

/-- **`σ α = ζ • α`**。 -/
theorem σ_α (hζ : IsPrimitiveRoot ζ p) :
    σ (a := a) hζ (α (K := K) (p := p) (a := a)) = ζ • α := by
  rw [α, σ, autAdjoinRootXPowSubC_root]
  rfl

/-! ### `L` 的域结构与 Galois 结构（逐条引入局部实例） -/

section Structure

variable (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)
  [Fact (Irreducible (X ^ p - C a : K[X]))]

include hζ ha

theorem isSplittingField : IsSplittingField K (L K p a) (X ^ p - C a : K[X]) :=
  isSplittingField_AdjoinRoot_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩ (irreducible ha)

/-- **`[L:K] = p`**。 -/
theorem finrank_eq [NeZero p] : Module.finrank K (L K p a) = p := by
  haveI : IsSplittingField K (L K p a) (X ^ p - C a : K[X]) := isSplittingField hζ ha
  exact finrank_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩ (irreducible ha) (L K p a)

theorem isGalois : IsGalois K (L K p a) := by
  haveI : IsSplittingField K (L K p a) (X ^ p - C a : K[X]) := isSplittingField hζ ha
  exact isGalois_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩ (irreducible ha) (L K p a)

theorem isCyclic [NeZero p] : IsCyclic (L K p a ≃ₐ[K] L K p a) := by
  haveI : IsSplittingField K (L K p a) (X ^ p - C a : K[X]) := isSplittingField hζ ha
  exact isCyclic_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩ (irreducible ha) (L K p a)

end Structure

end SymbolKummerField
