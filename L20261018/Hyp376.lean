import L20261018.Hyp375

/-!
# R1289（S36 · GS §6.8 战役 #3）：`ℚ` 的**一阶**连续零调（(G4′) 的基础例）

`PLAN-GS68.md` §7（本轮更正）把 GS §6.8 的第 3 件定为

```
(G4′)  H^i_cont(G, Z) ≅ H^{i-1}_cont(G, Q/Z)      -- `G` profinite，连续上同调，离散系数
       核心输入 = ∀ n ≥ 1, H^n_cont(G, Q) = 0
```

本文件机检其中 `n = 1` 的情形，**直接复用 TauCeti 现成件**：
`ContCohomology.subsingleton_H1_of_isAddTorsionFree`
（紧 monoid ＋ 离散、无挠、平凡系数 ⟹ `H¹ = 0`；其 docstring 明写「in particular trivial integer
coefficients」）。`ℚ` 与 `ℤ` 都无挠 ✓。

| 声明 | 内容 |
|---|---|
| **`subsingleton_H1_int_absGal`** | ★★★★ `H¹(AbsGal F, ℤ) = 0`（`ℤ` 平凡、离散、无挠；`AbsGal F` 紧） |
| —— | `ℚ` 的情形需 `DiscreteTopology ℚ`，而 mathlib 的 `ℚ` 带序拓扑（非离散）⟹ 须换一个离散副本（`WithDiscrete` 类），本轮暂缺 |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

variable (F : Type) [Field F]

/- 平凡作用的局部实例（`ℚ`／`ℤ` 作为 `AbsGal F` 的平凡离散模）。 -/
local instance : SMul (TauCeti.AbsoluteGaloisGroup F) ℚ := ⟨fun _ m => m⟩
local instance : DistribMulAction (TauCeti.AbsoluteGaloisGroup F) ℚ where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl
local instance : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) ℚ := ⟨continuous_snd⟩
local instance : SMul (TauCeti.AbsoluteGaloisGroup F) ℤ := ⟨fun _ m => m⟩
local instance : DistribMulAction (TauCeti.AbsoluteGaloisGroup F) ℤ where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl
local instance : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) ℤ := ⟨continuous_snd⟩

/-- ★★★★ **`H¹(AbsGal F, ℤ) = 0`**。 -/
theorem subsingleton_H1_int_absGal :
    Subsingleton (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) ℤ) :=
  ContCohomology.subsingleton_H1_of_isAddTorsionFree
    (fun _ _ => rfl)

end L20261018

#print axioms L20261018.subsingleton_H1_int_absGal
