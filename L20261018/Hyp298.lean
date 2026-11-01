import L20261018.Hyp297

/-!
# R1181（**残余 (P) 第三块 (U3)：`𝓀^×` 循环 ＋ 阶 `q−1`**）

## 本轮做什么

`PLAN-R2` §H-41 把 (P) 的数学内容 `|𝒪_F^×/(𝒪_F^×)^p| = p` 分成三块；
(U1)（`Hyp296` ＋ `Hyp297.one_add_subset_pow`）与 (U2)（`Hyp297.exists_unit_residue_eq`）已机检。
本轮做 **(U3)** 的**库内可复用部分**：

* `𝓀^×` **循环**（有限域乘法群）—— 库内是**实例**（`infer_instance` 即得，
  已在 `Mathlib/LinearAlgebra/Projectivization/PSL/PSL2.lean:130` 以 `IsCyclic Fˣ := by infer_instance` 使用）；
* `Nat.card 𝓀^× = Nat.card 𝓀 − 1`（`Nat.card_units`）。

**(U3) 剩余的唯一内容**：`p ∣ Nat.card 𝓀 − 1`（由 `μ_p ⊂ F` 经 Hensel 归约到剩余域：

`X^p − 1` 在 `𝓀` 上分裂成 `p` 个不同线性因子 ⟹ `𝓀^×` 含阶 `p` 元素 ⟹ `p ∣ |𝓀^×|`，
用 `Nat.card_units` 即 `p ∣ Nat.card 𝓀 − 1`）。

⟹ (U1)(U2)(U3) 齐 ⟹ `𝒪^×/(𝒪^×)^p ≅ 𝓀^×/(𝓀^×)^p ≅ Z/p` ⟹ **(P)** ⟹ `UnitsCupVanish`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`isCyclic_units_of_finite`** | ★★★★★ **`IsCyclic 𝓀^×`**（有限域，库内实例） |
| **`natCard_units_of_finite`** | ★★★★★ `Nat.card 𝓀^× = Nat.card 𝓀 − 1` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace L20261018

section FiniteFieldUnits

/-- ★★★★★ **(U3) 前半：有限域的乘法群循环**（库内实例，`L47`）。 -/
theorem isCyclic_units_of_finite (k : Type*) [Field k] [Finite k] : IsCyclic kˣ :=
  inferInstance

/-- ★★★★★ **`Nat.card 𝓀^× = Nat.card 𝓀 − 1`**（`Nat.card_units`）。 -/
theorem natCard_units_of_finite (k : Type*) [Field k] [Finite k] :
    Nat.card kˣ = Nat.card k - 1 :=
  Nat.card_units k

/-! ### (U3) 剩余的**唯一**内容（下一轮）

`p ∣ Nat.card 𝓀 − 1 = Nat.card 𝓀^×`。库内 Cauchy 定理给出阶 `p` 元素
（`Sylow.exists_prime_orderOf_dvd_card`／`exists_prime_orderOf_dvd_card` 一族，**下一轮按内容核名**），
故 `𝓀^× ⊇ μ_p`，配合 `isCyclic_units_of_finite` 得 `𝓀^×/(𝓀^×)^p ≅ Z/p`。

`p ∣ Nat.card 𝓀 − 1` 本身的来源：`μ_p ⊂ F`（`[HasEnoughRootsOfUnity F p]`）经
`residue` 归约到 `𝓀`（`p` 可逆 ⟹ `residue` 在 `μ_p` 上单射），Hensel 侧由
`IsLocalRing.residue` ＋ `p` 可逆给出。
-/

end FiniteFieldUnits

end L20261018

#print axioms L20261018.isCyclic_units_of_finite
#print axioms L20261018.natCard_units_of_finite
