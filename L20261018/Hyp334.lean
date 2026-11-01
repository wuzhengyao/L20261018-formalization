import L20261018.Hyp333

/-!
# R1240（S34 第 12 轮）：**`hK1`（4.4 的 `L1` 残余）在 `ℚ_[7]` 上机检**

`corollary_4_4_noBridge`（4.4）的 `L1` 见证缺三块中最大的一块：**`finrank (ker v̄) = 1`**。
本轮把 `v` 换成 TauCeti 的 `normalizedValuation`（`Hyp333` 已证它满足 `ValCompat`），
于是 `valLinOf normalizedValuation = valLin`（`rfl`-级桥 `valLin_eq_valLinOf_normalizedValuation`），
`Hyp148.finrank_ker_valLin_eq_one`（完备情形的「`hne` ⟹ `finrank ker = 1`」）**直接可用**。

同时补上 `π = 7` 的 `Fact (Irreducible (X³ − 7))`（`D` 的构造需要）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`seven_not_cube_Q7`** | ★★ `∀ c : ℚ_[7], c³ ≠ 7`（赋值论证：`3·v(c) = 1` 无整数解） |
| `seven_irred_Q7` | `Fact (Irreducible (X³ − C 7))`（Capelli） |
| **`finrank_ker_valLinOf_Q7`** | ★★★★★★ **`finrank (ker v̄) = 1`**（`v := normalizedValuation`） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section Q7

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity ℚ_[7] 3 := hasEnoughRootsOfUnity_Q7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- ★★ **`7` 不是 `ℚ_[7]` 中的立方**（赋值：`v(c³) = 3·v(c)` 而 `v(7) = 1`）。 -/
theorem seven_not_cube_Q7 : ∀ c : ℚ_[7], c ^ 3 ≠ (7 : ℚ_[7]) := by
  intro c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  have hunit : (Units.mk0 c hc0) ^ 3 = Units.mk0 (7 : ℚ_[7]) (by norm_num) := by
    ext
    simpa using hc
  have hmap := congrArg (TauCeti.normalizedValuation ℚ_[7]) hunit
  rw [map_pow, normalizedValuation_seven_Q7] at hmap
  have h1 : (3 : ℤ) * Multiplicative.toAdd
      ((TauCeti.normalizedValuation ℚ_[7]) (Units.mk0 c hc0)) = 1 := by
    have h2 : Multiplicative.toAdd
        ((TauCeti.normalizedValuation ℚ_[7]) (Units.mk0 c hc0) ^ 3) = 1 := by
      rw [hmap]
      simp
    have h3 : Multiplicative.toAdd
        ((TauCeti.normalizedValuation ℚ_[7]) (Units.mk0 c hc0) ^ 3)
        = 3 * Multiplicative.toAdd
            ((TauCeti.normalizedValuation ℚ_[7]) (Units.mk0 c hc0)) := by
      rw [pow_three]
      simp
      ring
    rw [h3] at h2
    exact h2
  omega

/-- `X³ − C 7` 在 `ℚ_[7]` 上不可约（Capelli）。 -/
instance seven_irred_Q7 : Fact (Irreducible (X ^ 3 - C (7 : ℚ_[7]))) :=
  ⟨(capelli_irreducible_iff (F := ℚ_[7]) (p := 3) (by decide)).mpr seven_not_cube_Q7⟩

/-- ★★★★★★ **`finrank (ker v̄) = 1`**（`v := TauCeti.normalizedValuation ℚ_[7]`）—— 4.4 的 `hK1`。

`valLinOf normalizedValuation = valLin`（`rfl`-级），故直接用 `Hyp148.finrank_ker_valLin_eq_one`
（`hne` ＋ `[FiniteDimensional]` ＋ `NeZero (2 : ZMod 3)` ⟹ `finrank ker = 1`）。 -/
theorem finrank_ker_valLinOf_Q7 :
    Module.finrank (ZMod 3) ↥(LinearMap.ker (valLinOf (F := ℚ_[7]) (p := 3)
      (TauCeti.normalizedValuation ℚ_[7]) three_isUnit_F)) = 1 := by
  rw [valLin_eq_valLinOf_normalizedValuation]
  exact finrank_ker_valLin_eq_one (F := ℚ_[7]) (p := 3) three_isUnit_F ⟨by decide⟩
    three_isUnit_O hne_Q7

end Q7

end L20261018

#print axioms L20261018.seven_not_cube_Q7
#print axioms L20261018.finrank_ker_valLinOf_Q7
