import L20261018.Ch2.Hensel.ResidueMap.Step032_hskew_discharged
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.RingTheory.Henselian.Basic

/-!
# R1230（S34 第 2 轮）：**`L1` 非空见证 —— `F = ℚ_[7]`，`p = 3`**

## 为什么需要这一件

`L1`（＋ `L10①`）要求条件定理的**假设类自带机检非空见证**。`Hyp321`／`Hyp323` 的
论文层级假设（`HenselianRing`／`IsDiscreteValuationRing`／`Finite (ResidueField)`／
`HasEnoughRootsOfUnity`）此前**全仓无实例**。本轮把它们逐个落地在 `F = ℚ_[7]`、`p = 3`：

| 需要 | 来源 |
|---|---|
| `[] [ValuativeRel ℚ_[p]] [TopologicalSpace] [IsNonarchimedeanLocalField]` | mathlib `Padics/*`（实例化即得） |
| `IsDiscreteValuationRing ↥𝒪[ℚ_[p]]` | mathlib `NumberTheory/LocalField/Basic.lean:109`（自动） |
| `HenselianRing ↥𝒪[ℚ_[p]] 𝓂` | mathlib `IsAdicComplete.henselianRing`（`LocalField/Basic.lean:178` 给出 `IsAdicComplete`） |
| `Finite (IsLocalRing.ResidueField ↥𝒪[ℚ_[p]])` | 自动（`Nat.card = p`） |
| `IsUnit (3 : ↥𝒪[ℚ_[7]])` | `Padic.isUnit_intCast_integerRing`（`LocalField/Padic.lean:123`） |
| **`HasEnoughRootsOfUnity ℚ_[7] 3`** | 本轮构造：**Hensel 提升** `X²+X+1` 模 7 的根 `2` |

**为什么是 `7` 与 `3`**：`μ_3 ⊂ ℚ_[ℓ] ⟺ 3 ∣ ℓ−1`；`ℓ = 5` 时不成立（TauCeti 已证
`X²+X+1` 在 `ℚ_[5]` 上不可约，`LocalField/Padic.lean:255`）⟹ 取 `ℓ = 7`。
`p = 3` 是满足 `p ≠ 2`（`hp2`）且 `μ_p ⊂ ℚ_[ℓ]` 的最小组合。

## 本轮

| 声明 | 内容 |
|---|---|
| `seven_mem_maximalIdeal` | `7 ∈ 𝓂[ℚ_[7]]` |
| `five_isUnit` | `IsUnit (5 : ↥𝒪[ℚ_[7]])` |
| `exists_root_X_sq_add_X_add_one` | ★ Hensel：`∃ a, a²+a+1 = 0 ∧ a ≡ 2 (mod 𝓂)` |
| **`exists_primitiveRoot_three_Q7`** | ★★ `∃ ζ : ℚ_[7], IsPrimitiveRoot ζ 3` |
| **`hasEnoughRootsOfUnity_Q7_three`** | ★★ `HasEnoughRootsOfUnity ℚ_[7] 3` |
| **`exists_henselResidueData_witness_Q7`** | ★★★★★★ **`∃ v, ValCompat v ∧ ∃ D, D.val = v̄`** —— `Hyp323` 的**非空见证** |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Q7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `7` 落在 `𝒪[ℚ_[7]]` 的极大理想里（`7` 不可约 ⟹ 非单位）。 -/
theorem seven_mem_maximalIdeal : (7 : ↥𝒪[ℚ_[7]]) ∈ IsLocalRing.maximalIdeal ↥𝒪[ℚ_[7]] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact (TauCeti.Padic.irreducible_natCast_self 7).not_isUnit

/-- `5` 是 `𝒪[ℚ_[7]]` 的单位（`7 ∤ 5`）。 -/
theorem five_isUnit : IsUnit (5 : ↥𝒪[ℚ_[7]]) :=
  Padic.isUnit_intCast_integerRing (p := 7) (m := 5) (by decide)

/-- ★ **Hensel 提升**：`X²+X+1` 模 `7` 的根 `2` 提升为 `𝒪[ℚ_[7]]` 里的真根。

`f(2) = 7 ∈ 𝓂`、`f'(2) = 5` 为单位 ⟹ `HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal`。 -/
theorem exists_root_X_sq_add_X_add_one :
    ∃ a : ↥𝒪[ℚ_[7]], a ^ 2 + a + 1 = 0 ∧
      a - 2 ∈ IsLocalRing.maximalIdeal ↥𝒪[ℚ_[7]] := by
  haveI hHL : HenselianLocalRing ↥𝒪[ℚ_[7]] :=
    TauCeti.HenselianRing.henselianLocalRing ↥𝒪[ℚ_[7]]
  have hval : (X ^ 2 + X + 1 : (↥𝒪[ℚ_[7]])[X]).eval 2 = (7 : ↥𝒪[ℚ_[7]]) := by
    simp
    norm_num
  have hder : (X ^ 2 + X + 1 : (↥𝒪[ℚ_[7]])[X]).derivative.eval 2 = (5 : ↥𝒪[ℚ_[7]]) := by
    simp
    norm_num
  obtain ⟨a, ha, hmem⟩ :=
    TauCeti.HenselianLocalRing.exists_isRoot_sub_mem_maximalIdeal
      (X ^ 2 + X + 1 : (↥𝒪[ℚ_[7]])[X]) (a₀ := 2)
      (by rw [hval]; exact seven_mem_maximalIdeal)
      (by rw [hder]; exact five_isUnit)
  refine ⟨a, ?_, hmem⟩
  simpa [Polynomial.IsRoot] using ha

/-- ★★ **`ℚ_[7]` 含本原 `3` 次单位根**：(Hensel 提升出的) `a` 满足 `a³ = 1`、`a ≠ 1`。 -/
theorem exists_primitiveRoot_three_Q7 : ∃ ζ : ℚ_[7], IsPrimitiveRoot ζ 3 := by
  obtain ⟨a, hroot, hmem⟩ := exists_root_X_sq_add_X_add_one
  have h1 : (a : ℚ_[7]) ^ 3 = 1 := by
    have key : (a : ℚ_[7]) ^ 3 = ((a : ℚ_[7]) - 1) * ((a : ℚ_[7]) ^ 2 + a + 1) + 1 := by ring
    rw [key]
    have : ((a : ℚ_[7]) ^ 2 + (a : ℚ_[7]) + 1) = 0 := by
      have h := congrArg (fun z : ↥𝒪[ℚ_[7]] => (z : ℚ_[7])) hroot
      push_cast at h ⊢
      linear_combination h
    rw [this]
    ring
  have h2 : (a : ℚ_[7]) ≠ 1 := by
    intro h
    have hae : a = 1 := Subtype.coe_injective h
    have hmem' : (-1 : ↥𝒪[ℚ_[7]]) ∈ IsLocalRing.maximalIdeal ↥𝒪[ℚ_[7]] := by
      have : a - 2 = (-1 : ↥𝒪[ℚ_[7]]) := by rw [hae]; ring
      rwa [this] at hmem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem'
    exact hmem' (isUnit_one.neg)
  refine ⟨(a : ℚ_[7]), h1, fun l hl => ?_⟩
  have hd : orderOf (a : ℚ_[7]) ∣ l := orderOf_dvd_of_pow_eq_one hl
  rwa [orderOf_eq_prime h1 h2] at hd

/-- ★★ **`HasEnoughRootsOfUnity ℚ_[7] 3`**。 -/
theorem hasEnoughRootsOfUnity_Q7_three : HasEnoughRootsOfUnity ℚ_[7] 3 where
  prim := exists_primitiveRoot_three_Q7
  cyc := inferInstance

end Q7

section Witness

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity ℚ_[7] 3 := hasEnoughRootsOfUnity_Q7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

theorem three_isUnit_O : IsUnit (3 : ↥𝒪[ℚ_[7]]) :=
  Padic.isUnit_intCast_integerRing (p := 7) (m := 3) (by decide)

theorem three_isUnit_F : IsUnit (3 : ℚ_[7]) :=
  three_isUnit_O.map (algebraMap ↥𝒪[ℚ_[7]] ℚ_[7])

/-- 选择的 `3` 次本原单位根。 -/
noncomputable def zeta3 : ℚ_[7] := Classical.choose exists_primitiveRoot_three_Q7

theorem zeta3_spec : IsPrimitiveRoot zeta3 3 := Classical.choose_spec exists_primitiveRoot_three_Q7

/-- ★★★★★★ **`L1` 非空见证**：`Hyp323.exists_henselResidueData_uncond_noBridge'`
在 `F = ℚ_[7]`、`p = 3` 上确实有实例 —— `∃ v, ValCompat v ∧ ∃ D, D.val = v̄`。

这同时是 `HenselResidueData` 在**真实局部域**上的第一份机检实例（`ℚ_[7]`）。 -/
theorem exists_henselResidueData_witness_Q7 :
    ∃ (v : ℚ_[7]ˣ →* Multiplicative ℤ),
      ValCompat (F := ℚ_[7]) v ∧
      ∃ D : HenselResidueData (ZMod 3)
          ↑(continuousCohomology 1 (ClassFieldTheory.muNRep 3 ℚ_[7])).toModuleCat
          ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep 3 ℚ_[7])).toModuleCat
          ↥(LinearMap.ker (valH1LinearGen (p := 3) v three_isUnit_F))
          ((ClassFieldTheory.kummerCupPairing zeta3 zeta3_spec).cup 1 1),
        D.val = valH1LinearGen (p := 3) v three_isUnit_F :=
  exists_henselResidueData_uncond_noBridge' (F := ℚ_[7]) (p := 3)
    (ζ := zeta3) zeta3_spec three_isUnit_O three_isUnit_F (by decide)

end Witness

end L20261018

#print axioms L20261018.exists_primitiveRoot_three_Q7
#print axioms L20261018.hasEnoughRootsOfUnity_Q7_three
#print axioms L20261018.exists_henselResidueData_witness_Q7
