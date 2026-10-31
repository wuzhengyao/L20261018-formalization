import Hyp294

/-!
# R1178（**`UnitsCupVanish` 的最终形态：唯一假设 = `𝒪^×` 的一条有限性陈述**）

## 本轮做什么

`Hyp292` → `Hyp293` → `Hyp294` 已把 `UnitsCupVanish` 的全部零件机检：

| 零件 | 件 | 状态 |
|---|---|---|
| (N1) `(x)^p ∈ normGroup` | `Hyp292.pow_mem_normGroup` | ✅ |
| (N2) `w ∈ normGroup F (AdjoinRoot (X^p − C w))` | `Hyp293.mem_normGroup_adjoinRoot` | ✅ |
| 模型不可约（原为 `[Fact (Irreducible …)]`） | `Hyp294.capelli_irreducible_of_not_pow` | ✅ **改为 `w ∉ (Fˣ)^p`** |
| `finrank F (AdjoinRoot (X^p − C w)) = p` | `Hyp294.finrank_adjoinRoot` | ✅ |
| `(P)` `𝒪^×/(𝒪^×)^p` 由 `w` 的类生成 | —— | 🟡 **唯一残余** |

本轮把它们组装成 `UnitsCupVanish` 的**最终形态**：唯一假设是一条**纯 `𝒪_F` 的有限性陈述**

```
PowClassGen v w :  ∀ u, v u = 1 → ∃ k : ℤ, ∃ z : Fˣ, u * w ^ (-k) = z ^ p
```

（数学内容：`𝒪_F^×/(𝒪_F^×)^p ≅ Z/p`，故任一非 `p` 次幂单位 `w` 的类生成它。
零件在库内：`TauCeti.integerUnitsEquivProd`（Teichmüller 分解，绑完备性，须去完备）
＋ Hensel 给 `(1+𝔪)^p = 1+𝔪`。**不涉 `L`、不涉赋值延拓、不涉不分歧性。**）

## 情形分裂（Capelli 逼出来的）

`w` 是 `p` 次幂时 (P) **不成立**（`u` 未必是 `p` 次幂），但此时 `(w) = 0` ⟹ 杯积平凡。
故最终假设取「**要么 `w` 是 `p` 次幂，要么 (P)**」。

## 本轮

| 声明 | 内容 |
|---|---|
| **`kummerClass_pow_eq_zero`** | `w = c^p ⟹ (w) = 0` |
| **`cup_unit_eq_zero_of_pow`** | `w = c^p ⟹ (u)∪(w) = 0` |
| **`cup_unit_eq_zero_of_powClassGen`** | ★★★★★ `w ∉ (Fˣ)^p` ＋ **(P) ⟹ `(u)∪(w) = 0`**（Capelli ＋ (N1)(N2) ＋ `finrank` 全自动） |
| **`unitsCupVanish_of_powClassGen`** | ★★★★★ **`UnitsCupVanish` 的标准形态，唯一假设 = 「`w` 是 `p` 次幂 或 (P)」** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti Polynomial

namespace L20261018

section Final

variable {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`w = c^p ⟹ (w) = 0`**：`(c^p) = p • (c) = 0`（`ZMod p`-模是 `p`-挠的）。 -/
theorem kummerClass_pow_eq_zero (hp : IsUnit (p : F)) {c : Fˣ} :
    ClassFieldTheory.kummerClass F hp (c ^ p) = 0 := by
  have h1 : ClassFieldTheory.kummerClass F hp (c ^ p)
      = (p : ℤ) • ClassFieldTheory.kummerClass F hp c := by
    rw [← zpow_natCast, ClassFieldTheory.kummerClass_zpow]
  rw [h1]
  have h2 : ((p : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_self]
  rw [← Int.cast_smul_eq_zsmul (ZMod p), h2, zero_smul]

/-- ★★★★★ **`w` 是 `p` 次幂 ⟹ `(u)∪(w) = 0`**（平凡情形）。 -/
theorem cup_unit_eq_zero_of_pow {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : F))
    {c u : Fˣ} :
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp (c ^ p)) = 0 := by
  rw [kummerClass_pow_eq_zero (p := p) hp, map_zero]

/-- ★★★★★ **`w ∉ (Fˣ)^p` ＋ (P) ⟹ `(u)∪(w) = 0`**（Capelli ＋ (N1)(N2) ＋ `finrank` 全自动）。

`w ∉ (Fˣ)^p` 由 Capelli（`Hyp294.capelli_irreducible_of_not_pow`）给出模型的不可约性；
`finrank` 由 `Hyp294.finrank_adjoinRoot`；`(N2)` 由 `Hyp293.mem_normGroup_adjoinRoot`；
`(N1)` 由 `Hyp292.pow_mem_normGroup`。**唯一输入是 (P)。** -/
theorem cup_unit_eq_zero_of_powClassGen {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {v : Fˣ →* Multiplicative ℤ} (w : Fˣ)
    (hnotpow : ∀ c : F, c ^ p ≠ (w : F))
    (hP : PowClassGen (p := p) v w)
    {u : Fˣ} (hu : v u = 1) :
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 := by
  letI : Fact (Irreducible (X ^ p - C (w : F))) :=
    ⟨capelli_irreducible_of_not_pow (p := p) hp2 hnotpow⟩
  haveI : Module.Finite F (AdjoinRoot (X ^ p - C (w : F))) :=
    (monic_X_pow_sub_C (w : F) (Fact.out : p.Prime).ne_zero).finite_adjoinRoot
  exact cup_kummerClass_unit_eq_zero_of_powClassGen' (p := p) hζ hp hp2 w
    (finrank_adjoinRoot (p := p) (a := (w : F))) hP hu

/-- ★★★★★ **`UnitsCupVanish` 的最终标准形态**：唯一假设是
「**非 `p` 次幂的单位 `w` 满足 (P)**」（`w` 是 `p` 次幂时杯积平凡，见 `cup_unit_eq_zero_of_pow`）。

数学内容：`𝒪_F^×/(𝒪_F^×)^p ≅ Z/p`（Neukirch 1999 `:4535` Teichmüller 分解 ＋ Hensel 给
`(1+𝔪)^p = 1+𝔪`），故任一非 `p` 次幂单位的类生成它。**这是 `UnitsCupVanish` 的最后一条数学内容。** -/
theorem unitsCupVanish_of_powClassGen {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (v : Fˣ →* Multiplicative ℤ)
    (hP : ∀ w : Fˣ, v w = 1 → (∀ c : F, c ^ p ≠ (w : F)) →
      PowClassGen (p := p) v w) :
    ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 := by
  intro u w hu hw
  by_cases hpow : ∃ c : F, c ^ p = (w : F)
  · obtain ⟨c, hc⟩ := hpow
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hc
      exact (Units.ne_zero w) hc.symm
    have hcw : (Units.mk0 c hc0) ^ p = w := Units.ext hc
    rw [← hcw]
    exact cup_unit_eq_zero_of_pow (p := p) hζ hp
  · exact cup_unit_eq_zero_of_powClassGen (p := p) hζ hp hp2 w
      (fun c hc => hpow ⟨c, hc⟩) (hP w hw fun c hc => hpow ⟨c, hc⟩) hu

end Final

end L20261018

#print axioms L20261018.kummerClass_pow_eq_zero
#print axioms L20261018.cup_unit_eq_zero_of_pow
#print axioms L20261018.cup_unit_eq_zero_of_powClassGen
#print axioms L20261018.unitsCupVanish_of_powClassGen
