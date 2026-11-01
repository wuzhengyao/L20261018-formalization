import L20261018.Hyp293

/-!
# R1177（**去掉「不可约」输入：Capelli 判据 ⟹ `X^p − C w` 不可约 ⟺ `w` 不是 `p` 次幂**）

## 本轮做什么

`Hyp293.mem_normGroup_adjoinRoot` 需要 `[Fact (Irreducible (X ^ p − C w))]`。
`Hyp201` 对 `π`（一致化元）曾以「`v(π) = 1` 时自动成立」打发；但 `UnitsCupVanish` 里的 `w`
是**单位**（`v w = 1` 即 `v`-值 0），**不能用同一个理由**。本轮把这条输入**变成定理**。

## 用的库内定理（`L47`；`L46` 教训：按内容搜）

**`Mathlib/FieldTheory/KummerExtension.lean:139`**

```lean
theorem X_pow_sub_C_irreducible_iff_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ ∀ (d : ℕ), d ∣ n → d ≠ 1 → ∀ (b : K), b ^ d ≠ a
```

这正是 **Capelli 判据**（`n` 奇情形）。本处 `n = p` 素数 ⟹ `d ∣ p` 且 `d ≠ 1` ⟹ `d = p`，故

```
Irreducible (X^p − C a)  ⟺  ∀ b : F, b^p ≠ a     （即 a ∉ (Fˣ)^p）
```

⟹ 「不可约」这条输入**可以完全去掉**，代价是**情形分裂**：
* `a = w` 是 `p` 次幂 ⟹ `(w) = 0`（Kummer 类平凡）⟹ 杯积平凡；
* `a = w` 不是 `p` 次幂 ⟹ Capelli 给不可约。

## 本轮

| 声明 | 内容 |
|---|---|
| **`capelli_irreducible_iff`** | ★★★★★ `Irreducible (X^p − C a) ↔ (∀ b : F, b^p ≠ a)` |
| **`capelli_irreducible_of_not_pow`** | ★★★★★ Capelli 的用向：`a` 非 `p` 次幂 ⟹ 不可约 |
| **`not_pow_of_irreducible`** | 反向用向 |
| **`finrank_adjoinRoot`** | ★★★★★ `Module.finrank F (AdjoinRoot (X^p − C a)) = p`（去掉 `Hyp293` 的 `hfr` 输入） |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace L20261018

section Capelli

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime]

/-- ★★★★★ **Capelli 判据（`p` 素数）**：`X^p − C a` 不可约 ⟺ `a` 不是 `F` 中的 `p` 次幂。

由 `X_pow_sub_C_irreducible_iff_of_odd`（`KummerExtension.lean:139`）＋`p` 素数的因数集
`{1, p}` 化简。 -/
theorem capelli_irreducible_iff (hp2 : p ≠ 2) {a : F} :
    Irreducible (X ^ p - C a) ↔ ∀ b : F, b ^ p ≠ a := by
  rw [X_pow_sub_C_irreducible_iff_of_odd (Nat.Prime.odd_of_ne_two Fact.out hp2)]
  constructor
  · intro h b hb
    exact h p (dvd_refl p) (Fact.out : p.Prime).ne_one b hb
  · intro h d hd hd1 b hb
    rcases (Nat.Prime.eq_one_or_self_of_dvd Fact.out d hd) with rfl | rfl
    · exact absurd rfl hd1
    · exact h b hb

/-- ★★★★★ **Capelli 的用向**：`a` 不是 `p` 次幂 ⟹ `X^p − C a` 不可约。

⟹ `Hyp293` 的 `[Fact (Irreducible (X^p − C w))]` 输入**可被 `w ∉ (Fˣ)^p` 替换**。 -/
theorem capelli_irreducible_of_not_pow (hp2 : p ≠ 2) {a : F}
    (ha : ∀ b : F, b ^ p ≠ a) : Irreducible (X ^ p - C a) :=
  (capelli_irreducible_iff (p := p) hp2).mpr ha

/-- 反向用向：若 `X^p − C a` 不可约，则 `a` 不是 `p` 次幂。 -/
theorem not_pow_of_irreducible (hp2 : p ≠ 2) {a : F}
    (h : Irreducible (X ^ p - C a)) : ∀ b : F, b ^ p ≠ a :=
  (capelli_irreducible_iff (p := p) hp2).mp h

/-- ★★★★★ **`finrank F (AdjoinRoot (X^p − C a)) = p`**（去掉 `Hyp293` 的 `hfr` 输入）。

`AdjoinRoot.powerBasis_dim` ＋ `natDegree_X_pow_sub_C`。 -/
theorem finrank_adjoinRoot (a : F) :
    Module.finrank F (AdjoinRoot (X ^ p - C a)) = p := by
  have hf : (X ^ p - C a : F[X]) ≠ 0 :=
    X_pow_sub_C_ne_zero (Fact.out : p.Prime).pos a
  rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim hf,
    natDegree_X_pow_sub_C]

end Capelli

end L20261018

#print axioms L20261018.capelli_irreducible_iff
#print axioms L20261018.capelli_irreducible_of_not_pow
#print axioms L20261018.not_pow_of_irreducible
#print axioms L20261018.finrank_adjoinRoot
