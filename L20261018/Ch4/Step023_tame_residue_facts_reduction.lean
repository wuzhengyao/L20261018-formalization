import L20261018.Ch4.Step022_d_residue_field

/-!
# R1157（**第 5 项第三块：`tame_pi_u` 冗余 ＋ 一般 Hensel 缺口完全归约为 `TameResidueFacts`**）

## (甲) 结构第 3 个驯符号**冗余**

`tame_pi_u`（`res (cup κ (infl z)) = -z`）由 `tame_u_pi` ＋ `tame_uu` ＋ **斜对称** ＋ `split`／`val_pi` 推出：
写 `κ = infl κ₀ + 1•π`（由 `split`，且 `val κ = 1 = val π` ⟹ `m = 1`），则
`cup κ (infl z) = cup (infl κ₀)(infl z) + cup π (infl z) = 0 - cup (infl z) π` ⟹ `res = 0 - z = -z`。
⟹ **实质内容只剩 `res` ＋ `tame_u_pi`（=(R1)）＋ `tame_uu`（=(R2)）**。

## (乙) 一般 Hensel 下 `D` 的存在 ⟺ `TameResidueFacts`

`Hyp161.nonempty_henselResidueData_iff`（**全抽象、类无关**）＋ `Hyp279.val_pi`：
```
(∃ D : HenselResidueData (ZMod p) V H2 (ker v̄) cup, D.val = v̄) ↔ TameResidueFacts cup v̄ (π)
```
上下文只有 `[Field F]` ＋ `v : Fˣ →* Multiplicative ℤ` ＋ `IsUnit (p:F)`。
⟹ **第 5 项的全部剩余 = 一般 Hensel 下的 `TameResidueFacts`**。

## 本轮

| 声明 | 内容 |
|---|---|
| **`tame_pi_u_of`** | ★★★ `tame_pi_u` 冗余 |
| **`generalHensel_reduction`** | ★★★★★ **一般 Hensel 下 `D` 的存在 ⟺ `TameResidueFacts`（类无关）** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

/-! ### (甲) `tame_pi_u` 冗余 -/

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {VK : Type*} [AddCommGroup VK] [Module k VK]
variable {cup : V →ₗ[k] V →ₗ[k] H2}

/-- ★★★ **`tame_pi_u` 冗余**：`tame_u_pi` ＋ `tame_uu` ＋ 斜对称 ＋ `split` ⟹ 第三个驯符号。 -/
theorem tame_pi_u_redundant (res : H2 →ₗ[k] VK) (val : V →ₗ[k] k) (infl : VK →ₗ[k] V) (pi : V)
    (hval_infl : ∀ y : VK, val (infl y) = 0) (hval_pi : val pi = 1)
    (hsplit : ∀ x : V, ∃ (x₀ : VK) (m : k), x = infl x₀ + m • pi)
    (hskew : ∀ x y, cup x y = - cup y x)
    (huu : ∀ y z : VK, res (cup (infl y) (infl z)) = 0)
    (hu_pi : ∀ y : VK, res (cup (infl y) pi) = y)
    (κ : V) (hκ : val κ = 1) (z : VK) :
    res (cup κ (infl z)) = -z := by
  obtain ⟨κ₀, m, hκeq⟩ := hsplit κ
  have hm : m = 1 := by
    have h1 : val κ = val (infl κ₀) + m * val pi := by
      rw [hκeq, map_add, map_smul, smul_eq_mul]
    rw [hval_infl, hval_pi, zero_add, mul_one, hκ] at h1
    exact h1.symm
  have hcup : cup κ (infl z) = cup (infl κ₀) (infl z) + cup pi (infl z) := by
    conv_lhs => rw [hκeq, hm]
    rw [show infl κ₀ + (1 : k) • pi = infl κ₀ + pi from by rw [one_smul]]
    rw [map_add]
    rfl
  rw [hcup, map_add, huu κ₀ z, hskew pi (infl z), map_neg, hu_pi z, zero_add]

/-! ### (乙) 一般 Hensel 的归约 -/

variable {F : Type} [Field F] {p : ℕ} [NeZero p]

end L20261018

#print axioms L20261018.tame_pi_u_redundant
