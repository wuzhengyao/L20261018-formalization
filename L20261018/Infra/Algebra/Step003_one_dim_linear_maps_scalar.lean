import L20261018.Ch2.Hensel.ResidueMap.Step030_r1_scaled_bridge
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# R1062（**`(R1-σ)` 的代数内核**）：一维模上两个非零线性映射只差一个非零标量

`(R1-σ)`（缩放桥）的数学内容是：两套 Kummer 类的载体链，其差别**只是一个单位标量** `c ∈ (ZMod p)^×`。
其最终的代数原因是：`KummerCoeff F p` 与 `muNRep` 的系数空间都是**一维** `ZMod p`-模，而一维模上的
两个非零线性映射必然互为标量倍：

```
finrank K M = 1 → finrank K N = 1 → f ≠ 0 → g ≠ 0 → ∃ c : K, c ≠ 0 ∧ ∀ x, f x = c • g x
```

| 声明 | 内容 |
|---|---|
| **`exists_smul_eq_of_finrank_eq_one`** | 上述引理（线性映射版） |
| **`exists_smul_eq_of_linearEquiv`** | 线性**等价**版（`f`、`g` 自动非零） |
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace L20261018

section OneDim

variable {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- **一维模上两个非零线性映射只差一个非零标量**。 -/
theorem exists_smul_eq_of_finrank_eq_one (hM : Module.finrank K M = 1)
    (hN : Module.finrank K N = 1) {f g : M →ₗ[K] N} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ x, f x = c • g x := by
  classical
  obtain ⟨b, hb⟩ := DFunLike.ne_iff.mp hg
  simp only [LinearMap.zero_apply] at hb
  have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
  -- `M` 由 `b` 张成、`N` 由 `g b` 张成
  have hM' : ∀ x : M, ∃ a : K, a • b = x :=
    (finrank_eq_one_iff_of_nonzero' b hb0).mp hM
  have hN' : ∀ y : N, ∃ c : K, c • g b = y :=
    (finrank_eq_one_iff_of_nonzero' (g b) hb).mp hN
  obtain ⟨c, hc⟩ := hN' (f b)
  -- `f b ≠ 0`（否则 `f = 0`）
  have hfb : f b ≠ 0 := by
    intro h0
    apply hf
    ext x
    obtain ⟨a, ha⟩ := hM' x
    rw [← ha, map_smul, h0, smul_zero]
    simp
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hfb hc.symm
  refine ⟨c, hc0, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hM' x
  rw [← ha, map_smul, map_smul, ← hc, smul_comm a c (g b)]

/-- **线性等价版**：一维模上两个线性等价只差一个非零标量。 -/
theorem exists_smul_eq_of_linearEquiv (hM : Module.finrank K M = 1)
    (hN : Module.finrank K N = 1) (f g : M ≃ₗ[K] N) :
    ∃ c : K, c ≠ 0 ∧ ∀ x, f x = c • g x := by
  classical
  have hf : (f : M →ₗ[K] N) ≠ 0 := by
    rintro h0
    haveI : Subsingleton M := ⟨fun x y => by
      have hxy : (f : M →ₗ[K] N) x = (f : M →ₗ[K] N) y := by rw [h0]; rfl
      exact f.injective hxy⟩
    have h0' : Module.finrank K M = 0 := Module.finrank_zero_iff.mpr ‹Subsingleton M›
    omega
  have hg : (g : M →ₗ[K] N) ≠ 0 := by
    rintro h0
    haveI : Subsingleton M := ⟨fun x y => by
      have hxy : (g : M →ₗ[K] N) x = (g : M →ₗ[K] N) y := by rw [h0]; rfl
      exact g.injective hxy⟩
    have h0' : Module.finrank K M = 0 := Module.finrank_zero_iff.mpr ‹Subsingleton M›
    omega
  exact exists_smul_eq_of_finrank_eq_one hM hN hf hg

end OneDim

end L20261018

#print axioms L20261018.exists_smul_eq_of_finrank_eq_one
#print axioms L20261018.exists_smul_eq_of_linearEquiv
