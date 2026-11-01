import L20261018.Ch2.Hensel.UnitsCupVanish.Step002_units_cup_vanish_reduction
import Mathlib.FieldTheory.KummerExtension

/-!
# R1176（**(N2) 收口：`w ∈ normGroup F (AdjoinRoot (X^p − C w))`，无条件**）

## 本轮做什么

`Hyp292` 把 `UnitsCupVanish` 归结为 **(N2) `w ∈ normGroup F L`** ＋ **(P) `𝒪^×/(𝒪^×)^p` 由 `w` 生成**。
本轮把 **(N2) 变成定理**，取 `L := AdjoinRoot (X ^ p − C w)`（最规范的 Kummer 模型）。

## 用的库内定理（`L47`：库内已有，零自建）

**`Mathlib/FieldTheory/KummerExtension.lean:108`**

```lean
theorem norm_root_X_pow_sub_C {n : ℕ} {a : K} (hn : n ≠ 0) :
    Algebra.norm K (AdjoinRoot.root (X ^ n - C a)) = (-1) ^ n * -a
```

取 `n = p`（`p` 素数故 `p ≠ 0`）、`a = w`。`p ≠ 2` ⟹ `p` 奇（`Nat.Prime.odd_of_ne_two`）
⟹ `(-1)^p = -1`（`Odd.neg_one_pow`）⟹ `N(root) = -1 * -w = w`。**（N2）即得。**

> 这条正是 `PLAN-R2` §H-40 里记为「残余 (N2)」的那一步 —— 库内**早已有**，
> 只是此前按名字（`norm_gen`／`AdjoinRoot.finrank`）搜不到；按**内容**（Kummer、`X^n − C a`、
> `Algebra.norm`）搜到 `KummerExtension.lean` 即命中。**`L46` 教训第 6 次。**

## 本轮

| 声明 | 内容 |
|---|---|
| **`root_ne_zero_of_ne_zero`** | `w ≠ 0 ⟹ AdjoinRoot.root (X^p − C w) ≠ 0`（由 `N(root) = w ≠ 0`） |
| **`norm_root_eq`** | ★★★★★ **`Algebra.norm F (root (X^p − C w)) = w`**（`p` 奇） |
| **`mem_normGroup_adjoinRoot`** | ★★★★★ **(N2)：`w ∈ normGroup F (AdjoinRoot (X^p − C w))`，无条件** |
| **`adjoin_root_eq_top`** | `F⟮root⟯ = ⊤`（自足重证，不拖 `Hyp201` 的赋值上下文） |
| **`cup_kummerClass_unit_eq_zero_of_powClassGen'`** | ★★★★★ **合成：只剩 (P)** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti Polynomial

namespace L20261018

section AdjoinRootNorm

variable {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime]

/-- ★★★★★ **`N(root) = w`**：`minpoly = X^p − C w` 时根 `root` 的范数就是 `w`。

直接由 `norm_root_X_pow_sub_C`（`KummerExtension.lean:108`）＋ `p` 奇
（`p ≠ 2` ⟹ `(-1)^p = -1`）给出。 -/
theorem norm_root_eq (_hp2 : p ≠ 2) (a : F) :
    Algebra.norm F (AdjoinRoot.root (X ^ p - C a)) = (-1) ^ p * -a :=
  norm_root_X_pow_sub_C (Fact.out : p.Prime).ne_zero

/-- ★★★★★ **`N(root) = w`（`p` 奇时的化简形式）**。 -/
theorem norm_root_eq' (hp2 : p ≠ 2) (a : F) :
    Algebra.norm F (AdjoinRoot.root (X ^ p - C a)) = a := by
  rw [norm_root_eq (p := p) hp2,
    Odd.neg_one_pow (Nat.Prime.odd_of_ne_two Fact.out hp2)]
  ring

/-- `w ≠ 0` ⟹ `root (X^p − C w) ≠ 0`（由 `N(root) = w ≠ 0`）。 -/
theorem root_ne_zero_of_ne_zero {a : F} (ha : a ≠ 0)
    [Fact (Irreducible (X ^ p - C a))] :
    AdjoinRoot.root (X ^ p - C a) ≠ 0 := by
  have hpow : (AdjoinRoot.root (X ^ p - C a)) ^ p = algebraMap F (AdjoinRoot (X ^ p - C a)) a := by
    have h := AdjoinRoot.eval₂_root (R := F) (f := X ^ p - C a)
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
    exact sub_eq_zero.mp h
  intro h0
  rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hpow
  rw [Algebra.algebraMap_eq_smul_one] at hpow
  exact ha ((smul_eq_zero.mp hpow.symm).resolve_right one_ne_zero)

/-- ★★★★★ **(N2)：`w ∈ normGroup F (AdjoinRoot (X^p − C w))`，无条件**。

取 `y = root`（它是 `Lˣ` 的元素，由 `root ≠ 0`），`Algebra.norm F ↑y = w`。 -/
theorem mem_normGroup_adjoinRoot (hp2 : p ≠ 2) (a : Fˣ)
    [Fact (Irreducible (X ^ p - C (a : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (a : F)))] :
    a ∈ normGroup F (AdjoinRoot (X ^ p - C (a : F))) := by
  rw [mem_normGroup_iff]
  refine ⟨Units.mk0 (AdjoinRoot.root (X ^ p - C (a : F)))
    (root_ne_zero_of_ne_zero (p := p) (Units.ne_zero a)), ?_⟩
  show Algebra.norm F (AdjoinRoot.root (X ^ p - C (a : F))) = (a : F)
  exact norm_root_eq' (p := p) hp2 (a : F)

/-- `F⟮root⟯ = ⊤`（`AdjoinRoot` 的根生成整个模型；自足重证）。 -/
theorem adjoin_root_eq_top' (a : F) [Fact (Irreducible (X ^ p - C a))] :
    IntermediateField.adjoin F ({AdjoinRoot.root (X ^ p - C a)} :
      Set (AdjoinRoot (X ^ p - C a))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [IntermediateField.mem_adjoin_simple_iff]
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨q, 1, ?_⟩
  rw [map_one, div_one, AdjoinRoot.aeval_eq]

end AdjoinRootNorm

/-! ## 组装：只剩 (P) -/

section Assembly

variable {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **单位 × 单位杯积为零 —— 唯一假设是 (P)**。

`Hyp292.cup_kummerClass_unit_eq_zero_of_norm_pow` 的 (N2) 假设
（`w ∈ normGroup F L`）已由 `mem_normGroup_adjoinRoot` 消去；`L` 固定为 `AdjoinRoot (X^p − C w)`。
`hfr`（`finrank = p`）留作显式输入（`AdjoinRoot.powerBasis` 可给，下一轮）。 -/
theorem cup_kummerClass_unit_eq_zero_of_powClassGen' {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {v : Fˣ →* Multiplicative ℤ} (w : Fˣ)
    [Fact (Irreducible (X ^ p - C (w : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (w : F)))]
    (hfr : Module.finrank F (AdjoinRoot (X ^ p - C (w : F))) = p)
    (hP : PowClassGen (p := p) v w)
    {u : Fˣ} (hu : v u = 1) :
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 :=
  cup_kummerClass_unit_eq_zero_of_norm_pow (p := p) hζ hp (v := v) (w := w)
    (L := AdjoinRoot (X ^ p - C (w : F))) (s := AdjoinRoot.root (X ^ p - C (w : F)))
    hfr
    (by
      have h := AdjoinRoot.eval₂_root (R := F) (f := X ^ p - C (w : F))
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
      exact sub_eq_zero.mp h)   -- s^p = algebraMap w
    (adjoin_root_eq_top' (p := p) (a := (w : F)))
    (mem_normGroup_adjoinRoot (p := p) hp2 w)
    hP hu

end Assembly

end L20261018

#print axioms L20261018.norm_root_eq
#print axioms L20261018.norm_root_eq'
#print axioms L20261018.root_ne_zero_of_ne_zero
#print axioms L20261018.mem_normGroup_adjoinRoot
#print axioms L20261018.adjoin_root_eq_top'
#print axioms L20261018.cup_kummerClass_unit_eq_zero_of_powClassGen'
