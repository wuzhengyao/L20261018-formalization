import L20261018.Ch2.Hensel.UnitsCupVanish.Step009_units_group_lemma

/-!
# R1185（**(P) 收口的算术核心：`p ∤ j ⟹ ∃ k, p ∣ i − k·j`**）

## 本轮做什么

`PLAN-R2` §H-43 把 (P) 的收口写成「生成元两情形」。本轮实测发现**情形分析可以完全消掉**：

设 `G` 循环有限、`g` 生成元、`U = g^i`、`W = g^j`。

* `∀ c, c^p ≠ W` ⟹ **`p ∤ j`**（若 `p ∣ j`，则 `W = (g^{j/p})^p` 是 `p` 次幂，矛盾）——
  **注意不需要分 `p ∣ |G|` 与否**；
* `p` 素 ＋ `p ∤ j` ⟹ `j` 与 `p` 互素 ⟹ 存在 `k` 使 **`p ∣ (i − k·j)`**（Bézout）；
* 于是 `U W^(−k) = g^(i−k·j) = (g^((i−k·j)/p))^p` ⟹ **`U = W^k · Z^p`**。

⟹ (P) 的群论部分只剩「生成元写下 `i`、`j`」的记账（下一步），**没有情形分裂、不需要商群、
不需要 `p ∣ q−1`**。

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_dvd_sub_mul`** | ★★★★★ `p` 素、`p ∤ j` ⟹ `∃ k : ℤ, (p:ℤ) ∣ i − k·j`（Bézout） |
| **`exists_pow_mul_pow_of_isCyclic`** | ★★★★★ **循环有限群上 (P) 的群论形态**：`W` 非 `p` 次幂 ⟹ `∀ U, ∃ k Z, U = W^k Z^p` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

namespace L20261018

section Arith

/-- ★★★★★ **Bézout 形式**：`p` 素、`p ∤ j` ⟹ 对任意 `i` 存在 `k` 使 `p ∣ i − k·j`。

⟹ 在 `G = ⟨g⟩` 中，`U = g^i`、`W = g^j`（`p ∤ j`）时可取 `k` 使 `U W^(−k) = g^(i−k·j)` 是 `p` 次幂。 -/
theorem exists_dvd_sub_mul {p : ℕ} (hp : p.Prime) {j : ℤ} (hj : ¬ (p : ℤ) ∣ j) (i : ℤ) :
    ∃ k : ℤ, (p : ℤ) ∣ i - k * j := by
  have hg : Int.gcd j (p : ℤ) = 1 := by
    have hdvd : (Int.gcd j (p : ℤ) : ℤ) ∣ (p : ℤ) := Int.gcd_dvd_right j (p : ℤ)
    have hdvdn : Int.gcd j (p : ℤ) ∣ p := by exact_mod_cast hdvd
    rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvdn with h1 | h1
    · exact h1
    · exfalso
      apply hj
      have hleft : (Int.gcd j (p : ℤ) : ℤ) ∣ j := Int.gcd_dvd_left j (p : ℤ)
      rw [h1] at hleft
      exact hleft
  have hbez : (1 : ℤ) = j * Int.gcdA j (p : ℤ) + (p : ℤ) * Int.gcdB j (p : ℤ) := by
    have := Int.gcd_eq_gcd_ab j (p : ℤ)
    rw [hg] at this
    exact_mod_cast this
  refine ⟨i * Int.gcdA j (p : ℤ), i * Int.gcdB j (p : ℤ), ?_⟩
  linear_combination i * hbez

end Arith

section GroupForm

/-- ★★★★★ **(P) 的群论形态**：循环有限群中，非 `p` 次幂的 `W` 能把任意 `U` 写成 `W^k · Z^p`。

由 `exists_dvd_sub_mul`（Bézout）＋ 生成元写法给出。**无情形分裂、无商群、无 `p ∣ |G|` 假设。** -/
theorem exists_pow_mul_pow_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} (hp : p.Prime) {W : G} (hW : ∀ c : G, c ^ p ≠ W) (U : G) :
    ∃ (k : ℤ) (Z : G), U = W ^ k * Z ^ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg U)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg W)
  have hpdvd : ¬ (p : ℤ) ∣ j := by
    intro hd
    obtain ⟨m, hm⟩ := hd
    refine hW (g ^ m) ?_
    rw [← hj]
    rw [← zpow_natCast (n := p) (a := g ^ m), ← zpow_mul]
    congr 1
    rw [hm]; ring
  obtain ⟨k, hk⟩ := exists_dvd_sub_mul hp hpdvd i
  obtain ⟨m, hm⟩ := hk
  refine ⟨k, g ^ m, ?_⟩
  rw [← hi, ← hj]
  rw [← zpow_natCast (n := p) (a := g ^ m), ← zpow_mul, ← zpow_mul, ← zpow_add]
  congr 1
  linear_combination hm

end GroupForm

end L20261018

#print axioms L20261018.exists_dvd_sub_mul
#print axioms L20261018.exists_pow_mul_pow_of_isCyclic
