import L20261018.Hyp179

/-!
# R1033（路径 A · **·b·iii ② 的配套**）：剩余模型是**非平凡环** ⟹ `N(s) = 0`

R1026 留了一个小缺口：由 `s^p = 0`（`Hyp173.root_pow_eq_zero_adjoinRoot`）推 `N(s) = 0`
需要 `Nontrivial (AdjoinRoot (X^p))`（`Algebra.norm_zero` 的前提）。本轮补上：

* 用 `AdjoinRoot.lift (RingHom.id k) 0`（`X ↦ 0`，`k` 上恒等）得满射 `A_𝓀 →+* k`；
* `k` 非平凡 ⟹ `A_𝓀` 非平凡；
* 于是 `norm_eq_zero_of_nilpotent` 适用，`N(s) = 0`。

| 声明 | 内容 |
|---|---|
| **`nontrivial_adjoinRoot_X_pow`** | `Nontrivial (AdjoinRoot (X^p : k[X]))` |
| **`norm_root_eq_zero_adjoinRoot`** | 剩余模型里 **`N(s) = 0`** |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section NontrivialResidueModel

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime]

/-- 剩余模型 `𝓀[X]/(X^p)` **非平凡**（存在满射到 `𝓀`）。 -/
theorem nontrivial_adjoinRoot_X_pow : Nontrivial (AdjoinRoot (X ^ p : k[X])) := by
  have hzero : eval₂ (RingHom.id k) (0 : k) ((X : k[X]) ^ p) = 0 := by
    simp [eval₂_pow, eval₂_X, zero_pow (Fact.out : p.Prime).ne_zero]
  refine ⟨0, 1, fun h => ?_⟩
  have hmap := congrArg (AdjoinRoot.lift (RingHom.id k) (0 : k) hzero) h
  rw [map_zero, map_one] at hmap
  exact zero_ne_one hmap

/-- 剩余模型里 **`N(s) = 0`**（`s` 幂零）。 -/
theorem norm_root_eq_zero_adjoinRoot :
    Algebra.norm k (AdjoinRoot.root (X ^ p : k[X])) = 0 := by
  haveI := nontrivial_adjoinRoot_X_pow (k := k) p
  haveI : Module.Free k (AdjoinRoot (X ^ p : k[X])) :=
    Polynomial.Monic.free_adjoinRoot (monic_X_pow (R := k) p)
  haveI : Module.Finite k (AdjoinRoot (X ^ p : k[X])) :=
    Polynomial.Monic.finite_adjoinRoot (monic_X_pow (R := k) p)
  exact norm_eq_zero_of_nilpotent (k := k) (AdjoinRoot (X ^ p : k[X]))
    (Fact.out : p.Prime).pos (root_pow_eq_zero_adjoinRoot (k := k) p)

end NontrivialResidueModel

end L20261018

#print axioms L20261018.nontrivial_adjoinRoot_X_pow
#print axioms L20261018.norm_root_eq_zero_adjoinRoot
