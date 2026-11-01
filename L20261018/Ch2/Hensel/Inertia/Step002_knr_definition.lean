import L20261018.Ch2.Hensel.Inertia.Step001_inertia_exact_sequence_first

/-!
# R1288（S36 · GS §6.8 战役 #2）：`K_nr` 的定义（一般 Hensel DVR，不用局部域假设）

`PLAN-GS68.md` §5 第 1 件的对象：**极大不分歧扩张 `K_nr`**。
本文件按 GS §6.8 的定义路线（惯性子群的固定域）给出**一般**定义 ——
**不**用 `IsNonarchimedeanLocalField`、**不**用有限剩余域、**不**用 `X^{q^f} − X`：

```
A  : 𝒪[K] 在 SeparableClosure K 中的一个赋值延拓（参数）
I  : A 的惯性子群（A.inertiaSubgroup K）
I* : I 在 AbsoluteGaloisGroup K 中的像
K_nr := fixedField I*
```

| 声明 | 内容 |
|---|---|
| **`inertiaAbs`** | `I ≤ D ≤ Gal(SepCl/K)` 的像 `I* : Subgroup (AbsoluteGaloisGroup K)` |
| **`Knr`** | ★★★★★ **极大不分歧扩张 `K_nr := fixedField I*`**（GS §6.8 的核心对象） |
| **`inertiaAbs_le_fixingSubgroup_Knr`** | `I* ≤ (K_nr).fixingSubgroup`（Galois 连接；即 `I ⊆ Gal(SepCl/K_nr)`） |
| `decomposition_infixingSubgroup` | `Gal(SepCl/K_nr)` 与 `D` 的关系留给下一轮（须证 `I` 在 Krull 拓扑下**闭**） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable {K : Type*} [Field K]

/-- 惯性子群在**绝对伽罗瓦群**中的像：`I ≤ D ≤ Gal(SepCl K/K)`。 -/
noncomputable def inertiaAbs (A : ValuationSubring (SeparableClosure K)) :
    Subgroup (TauCeti.AbsoluteGaloisGroup K) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

/-- ★★★★★ **极大不分歧扩张 `K_nr`**（GS §6.8）：惯性子群的固定域。

这是「一般 Hensel DVR 的 `K_nr`」，**不依赖** `IsNonarchimedeanLocalField`／有限剩余域，
也**不**用 `X^{q^f} − X` 的构造（TauCeti 的 `maximalUnramifiedExtension` 需要 `q = #κ`）。 -/
noncomputable def Knr (A : ValuationSubring (SeparableClosure K)) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField (inertiaAbs (K := K) A)

/-- `I* ≤ Gal(SepCl/K_nr)`（Galois 连接的 `l_u` 方向）。 -/
theorem inertiaAbs_le_fixingSubgroup_Knr (A : ValuationSubring (SeparableClosure K)) :
    inertiaAbs (K := K) A ≤ (Knr (K := K) A).fixingSubgroup :=
  ((IntermediateField.le_iff_le (H := inertiaAbs (K := K) A) (Knr (K := K) A)).mp le_rfl)

/-- `K_nr` 的定义层展开（便于下游 `simp`）。 -/
theorem Knr_def (A : ValuationSubring (SeparableClosure K)) :
    Knr (K := K) A = IntermediateField.fixedField (inertiaAbs (K := K) A) := rfl

end L20261018

#print axioms L20261018.inertiaAbs
#print axioms L20261018.Knr
#print axioms L20261018.inertiaAbs_le_fixingSubgroup_Knr
