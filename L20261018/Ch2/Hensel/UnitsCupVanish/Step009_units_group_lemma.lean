import L20261018.Ch2.Hensel.UnitsCupVanish.Step008_residue_field_units_cyclic

/-!
# R1183（**残余 (P) 的最后一条群论引理**）

## 本轮做什么

`PLAN-R2` §H-42 把 `UnitsCupVanish` 的残余压成**一条群论引理**：

> 循环群、指数整除素数 `p` ⟹ 任一非平凡元素生成全群。

本轮把它机检。它就是 `𝒪^×/(𝒪^×)^p` 上的核心：该商群
* **循环**（经 (U2) `𝒪^× ↠ 𝓀^×` 与 (U1) `1+𝔪 ⊆ (𝒪^×)^p`，同构于循环群 `𝓀^×` 的商），
* **指数整除 `p`**（任一元的 `p` 次幂落在 `(𝒪^×)^p` 里）

⟹ 阶整除素数 `p` ⟹ 阶 `1` 或 `p` ⟹ 任一非零类生成 ⟹ 对 `w ∉ (Fˣ)^p`（故 `w̄ ≠ 0`），
每个单位 `u` 都是 `w^k · z^p`，即 **(P)**（`Hyp292.PowClassGen`）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`orderOf_eq_prime_of_pow_eq_one`** | 有限群中 `x^p = 1`、`x ≠ 1`、`p` 素 ⟹ `orderOf x = p` |
| **`zpowers_eq_top_of_pow_eq_one`** | ★★★★★ **核心引理**：循环有限群、指数整除素数 `p` ⟹ 任一非平凡元素生成 |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace L20261018

section GroupCore

/-- 有限群中 `x^p = 1`、`x ≠ 1`、`p` 素 ⟹ `orderOf x = p`。 -/
theorem orderOf_eq_prime_of_pow_eq_one {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (hH : ∀ x : H, x ^ p = 1) {y : H} (hy : y ≠ 1) : orderOf y = p := by
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf y)
    (orderOf_dvd_of_pow_eq_one (hH y)) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hy
  · exact h

/-- ★★★★★ **残余 (P) 的核心引理**：**循环有限群、指数整除素数 `p` ⟹ 任一非平凡元素生成全群**。

设 `H = 𝒪^×/(𝒪^×)^p`：`H` 循环（`≅ 𝓀^×/(𝓀^×)^p`），且 `∀ x : H, x^p = 1`
（指数整除 `p`）。则任一非平凡元生成 `H` ⟹ `H` 的阶为 `p` ⟹ `H ≅ Z/p`
⟹ 任一非零类（如 `w̄`，`w ∉ (Fˣ)^p` 时）生成 ⟹ **(P)**。 -/
theorem zpowers_eq_top_of_pow_eq_one {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {p : ℕ} (hp : p.Prime) (hH : ∀ x : H, x ^ p = 1) {y : H} (hy : y ≠ 1) :
    Subgroup.zpowers y = ⊤ := by
  have hyord : orderOf y = p := orderOf_eq_prime_of_pow_eq_one hp hH hy
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hgtop : Subgroup.zpowers g = ⊤ := by
    refine top_le_iff.mp ?_
    intro x _
    exact hg x
  have hgord : orderOf g = Nat.card H := by
    rw [← Nat.card_zpowers, hgtop, Subgroup.card_top]
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hH g)
  have hcard : Nat.card H = p := by
    rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf g) hdvd with h | h
    · have hg1 : g = 1 := orderOf_eq_one_iff.mp h
      have hy1 : y = 1 := by
        have hmem : y ∈ Subgroup.zpowers g := hg y
        rw [hg1] at hmem
        simpa using hmem
      exact absurd hy1 hy
    · rwa [hgord] at h
  have hcard' : Nat.card ↥(Subgroup.zpowers y) = Nat.card H := by
    rw [Nat.card_zpowers, hyord, hcard]
  exact Subgroup.eq_top_of_card_eq _ hcard'

end GroupCore

end L20261018

#print axioms L20261018.orderOf_eq_prime_of_pow_eq_one
#print axioms L20261018.zpowers_eq_top_of_pow_eq_one
