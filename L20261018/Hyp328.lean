import L20261018.Hyp327

/-!
# R1234（S34 第 6 轮）：`ℚ_[7]` 的**非立方单位** —— `hne` 的第一步

`Hyp321` 三条的 `L1` 残余需要一个**真实的非零杯积类**（`hne`）。正路是：
取一个**单位** `u`（`v u = 0`）其 Kummer 类非零（即 `u` 不是 `p` 次幂），
则 `u ∈ ker v̄`，而 `HenselResidueData.tame_pi_u`（或 `tame_u_pi`）给出
`res (cup (inf .) π) = ·`，故 `cup (u) (π) ≠ 0`（`D.res` 把非零送到非零）。

本轮落地第一块：**`2` 在 `ℚ_[7]` 中不是立方**（TauCeti 只给了平方版
`not_isSquare_intCast_of_not_isSquare_zmod`；立方版照抄）。

| 声明 | 内容 |
|---|---|
| **`not_exists_cube_two_Q7`** | ★★★ `¬ ∃ b : ℚ_[7], b ^ 3 = 2`（模 `7` 判据） |
| **`kummerClass_two_ne_zero_Q7`** | ★★★★ `kc (2) ≠ 0`（经 `Hyp19.kummerClass_eq_zero_iff`） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity ℚ_[7] 3 := hasEnoughRootsOfUnity_Q7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- ★★★ **`2` 不是 `ℚ_[7]` 中的立方**。

证明：若 `b ^ 3 = 2`，则 `‖b‖^3 = ‖2‖ = 1`（`Padic.norm_natCast_eq_one_iff`，因 `7 ∤ 2`）
⟹ `‖b‖ = 1` ⟹ `b ∈ ℤ_[7]`；把 `b ^ 3 = 2` 送到 `ZMod 7` 得「`2` 是模 `7` 的立方」，与
`decide` 矛盾。 -/
theorem not_exists_cube_two_Q7 : ¬ ∃ b : ℚ_[7], b ^ 3 = (2 : ℚ_[7]) := by
  rintro ⟨b, hb⟩
  have hnorm2 : ‖(2 : ℚ_[7])‖ = 1 := by
    have h : (2 : ℚ_[7]) = ((2 : ℕ) : ℚ_[7]) := by norm_num
    rw [h, Padic.norm_natCast_eq_one_iff]
    decide
  have hnorm : ‖b‖ ^ 3 = 1 := by
    have h : ‖b ^ 3‖ = ‖b‖ ^ 3 := by rw [_root_.norm_pow]
    rw [hb, hnorm2] at h
    exact h.symm
  have hb1 : ‖b‖ = 1 := by
    have hnn : 0 ≤ ‖b‖ := norm_nonneg b
    have hpos : 0 < ‖b‖ ^ 2 + ‖b‖ + 1 := by positivity
    nlinarith [hnorm, hnn, hpos]
  obtain ⟨c, rfl⟩ : ∃ c : ℤ_[7], (c : ℚ_[7]) = b := ⟨⟨b, le_of_eq hb1⟩, rfl⟩
  have hc : c ^ 3 = (2 : ℤ_[7]) := PadicInt.ext (by push_cast; exact hb)
  have h2 : ((PadicInt.toZModPow 1 c) : ZMod (7 ^ 1)) ^ 3 = ((2 : ℕ) : ZMod (7 ^ 1)) := by
    rw [← map_pow, hc]
    show (PadicInt.toZModPow 1) ((2 : ℕ) : ℤ_[7]) = ((2 : ℕ) : ZMod (7 ^ 1))
    rw [map_natCast]
  have hno : ∀ x : ZMod (7 ^ 1), x ^ 3 ≠ ((2 : ℕ) : ZMod (7 ^ 1)) := by decide
  exact hno _ h2

/-- ★★★★ **`2` 的 Kummer 类非零**（`2` 不是 `3` 次幂）。

经 `Hyp19.KummerBridge.kummerClass_eq_zero_iff`：`kc a = 0 ↔ a ∈ range (powMonoidHom p)`。 -/
theorem kummerClass_two_ne_zero_Q7 :
    KummerBridge.kummerClass ℚ_[7] 3 three_isUnit_F
      (Units.mk0 (2 : ℚ_[7]) (by norm_num)) ≠ 0 := by
  intro h
  rw [KummerBridge.kummerClass_eq_zero_iff] at h
  obtain ⟨c, hc⟩ := h
  apply not_exists_cube_two_Q7
  refine ⟨(c : ℚ_[7]), ?_⟩
  have hc' : (c : ℚ_[7]) ^ 3 = ((Units.mk0 (2 : ℚ_[7]) (by norm_num) : ℚ_[7]ˣ) : ℚ_[7]) := by
    exact congrArg (fun u : ℚ_[7]ˣ => (u : ℚ_[7])) hc
  simpa using hc'

end L20261018

#print axioms L20261018.not_exists_cube_two_Q7
#print axioms L20261018.kummerClass_two_ne_zero_Q7
