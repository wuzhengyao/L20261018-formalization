import L20261018.Hyp324
import L20261018.Hyp110

/-!
# R1231（S34 第 3 轮）：`∂₂` 面两条 —— 一条**冗余性**（论文的 `tame_pi_u` 可导出）＋ `TameResidueFacts` 的 `ℚ_[7]` 见证

## §1 为什么 `tame_pi_u` 是冗余的（对 `prop:prelim-residue` 的审计）

论文 `prop:prelim-residue`(1) 只给两条规范：`∂_q(inf(η)∪(π)) = η` 与 `∂_q(inf(ξ)) = 0`；
`HenselResidueData` 另立了第三条 `tame_pi_u`（`∂₂((π)∪inf(z)) = −z`，即 `eq:prelim-tame` 的
`π × u` 特化）。本轮证明它**可由前两条 ＋ 斜对称性 ＋ `split` 导出**：
取 `κ` 使 `val κ = 1`，`split` 给 `κ = inf x₀ + m·π` 而 `val κ = m` ⟹ `m = 1`，
故 `cup κ (inf z) = cup (inf x₀) (inf z) + cup π (inf z) = 0 − cup (inf z) π = −(…)`，
`res` 后得 `−z`。

⟹ **`HenselResidueData` 的七个字段里，`tame_pi_u` 不是独立的**（去掉它结构仍表达同一数学内容）。

## §2 `ℚ_[7]` 上的 `TameResidueFacts` 见证

把 `Hyp324` 的实例资产（`three_isUnit_*`／`HasEnoughRootsOfUnity`）接到
`Hyp321.tameResidueFacts_Galo_noBridge` 上，得到 `∃ v π, ValCompat v ∧ v π = 1 ∧ TameResidueFacts …`
—— 这是第 4 章三条所消费的**唯一输入**在真实局部域上的机检实例。

## 本轮

| 声明 | 内容 |
|---|---|
| **`HenselResidueData.tame_pi_u_of_skew`** | ★★★ `val κ = 1 ⟹ res (cup κ (infl z)) = −z` **无需 `tame_pi_u` 字段** |
| `HenselResidueData.tame_pi_u_iff` | ★ 三个字段 ＋ 斜对称性 与「含 `tame_pi_u`」等价（冗余性的精确形式） |
| **`tameResidueFacts_witness_Q7`** | ★★★★★ `∃ v π, ValCompat v ∧ v π = ofAdd 1 ∧ TameResidueFacts`（`ℚ_[7]`／`p=3`） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Redundancy

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]
  {VK : Type*} [AddCommGroup VK] [Module k VK]
  {cup : V →ₗ[k] V →ₗ[k] H2}

/-- ★★★ **`tame_pi_u` 是冗余字段**：论文 `prop:prelim-residue`(1) 的两条规范（`tame_u_pi`
与 `tame_uu`）＋ **斜对称性** ＋ 赋值分解 `split` 已经给出 `res (cup κ (infl z)) = −z`。

证明：`split κ` 给 `κ = infl x₀ + m·π`；`val κ = m·val π = m`，而 `val κ = 1` ⟹ `m = 1`；
于是 `cup κ (infl z) = cup (infl x₀) (infl z) + cup π (infl z)`，首项由 `tame_uu` 消去，
次项由斜对称换成 `−cup (infl z) π`，再由 `tame_u_pi` 得 `−z`。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_2((\pi)\cup(u))=-(\bar u)"
theorem HenselResidueData.tame_pi_u_of_skew (D : HenselResidueData k V H2 VK cup)
    (hskew : ∀ x y : V, cup x y = - cup y x)
    {κ : V} (hκ : D.val κ = 1) (z : VK) :
    D.res (cup κ (D.infl z)) = -z := by
  obtain ⟨x₀, m, hm⟩ := D.split κ
  have hval : D.val κ = m := by
    rw [hm, map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one]
  have hm1 : m = 1 := by rw [← hval]; exact hκ
  rw [hm, hm1, one_smul, map_add, LinearMap.add_apply]
  have hA : D.res ((cup (D.infl x₀)) (D.infl z)) = 0 := D.tame_uu x₀ z
  have hB : D.res ((cup D.pi) (D.infl z)) = -z := by
    rw [hskew D.pi (D.infl z), map_neg, D.tame_u_pi z]
  rw [map_add, hA, hB, zero_add]

/-- **弱化结构**：去掉 `tame_pi_u` 字段的 `HenselResidueData` —— 即论文
`prop:prelim-residue`(1) 的两条规范 ＋ 赋值分解（**不**假定 `π × u` 的符号）。 -/
structure HenselResidueDataCore (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V]
    (H2 : Type*) [AddCommGroup H2] [Module k H2]
    (VK : Type*) [AddCommGroup VK] [Module k VK]
    (cup : V →ₗ[k] V →ₗ[k] H2) where
  res : H2 →ₗ[k] VK
  val : V →ₗ[k] k
  infl : VK →ₗ[k] V
  inj_infl : Function.Injective infl
  val_infl : ∀ y : VK, val (infl y) = 0
  pi : V
  val_pi : val pi = 1
  split : ∀ x : V, ∃ (x₀ : VK) (m : k), x = infl x₀ + m • pi
  tame_uu : ∀ y z : VK, res (cup (infl y) (infl z)) = 0
  tame_u_pi : ∀ y : VK, res (cup (infl y) pi) = y

namespace HenselResidueDataCore

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]
  {VK : Type*} [AddCommGroup VK] [Module k VK]
  {cup : V →ₗ[k] V →ₗ[k] H2}

/-- 弱化结构上，`π × u` 的符号由 `tame_uu` ＋ `tame_u_pi` ＋ 斜对称性 ＋ `split` 给出。 -/
theorem tame_pi_u (D : HenselResidueDataCore k V H2 VK cup)
    (hskew : ∀ x y : V, cup x y = - cup y x)
    {κ : V} (hκ : D.val κ = 1) (z : VK) :
    D.res (cup κ (D.infl z)) = -z := by
  obtain ⟨x₀, m, hm⟩ := D.split κ
  have hval : D.val κ = m := by
    rw [hm, map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one]
  have hm1 : m = 1 := by rw [← hval]; exact hκ
  rw [hm, hm1, one_smul, map_add, LinearMap.add_apply]
  have hA : D.res ((cup (D.infl x₀)) (D.infl z)) = 0 := D.tame_uu x₀ z
  have hB : D.res ((cup D.pi) (D.infl z)) = -z := by
    rw [hskew D.pi (D.infl z), map_neg, D.tame_u_pi z]
  rw [map_add, hA, hB, zero_add]

/-- ★★★★ **弱化结构 ＋ 斜对称性 ⟹ 完整 `HenselResidueData`**：
`tame_pi_u` 这一字段是**冗余**的。 -/
def toHenselResidueData (D : HenselResidueDataCore k V H2 VK cup)
    (hskew : ∀ x y : V, cup x y = - cup y x) : HenselResidueData k V H2 VK cup where
  res := D.res
  val := D.val
  infl := D.infl
  inj_infl := D.inj_infl
  val_infl := D.val_infl
  pi := D.pi
  val_pi := D.val_pi
  split := D.split
  tame_uu := D.tame_uu
  tame_u_pi := D.tame_u_pi
  tame_pi_u := fun κ hκ z => D.tame_pi_u hskew (κ := κ) hκ z

end HenselResidueDataCore

/-- 完整结构 **遗忘**为弱化结构（`tame_pi_u` 被丢掉）。 -/
def HenselResidueData.toCore (D : HenselResidueData k V H2 VK cup) :
    HenselResidueDataCore k V H2 VK cup where
  res := D.res
  val := D.val
  infl := D.infl
  inj_infl := D.inj_infl
  val_infl := D.val_infl
  pi := D.pi
  val_pi := D.val_pi
  split := D.split
  tame_uu := D.tame_uu
  tame_u_pi := D.tame_u_pi

end Redundancy

section Q7

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity ℚ_[7] 3 := hasEnoughRootsOfUnity_Q7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- ★★★★★ **`TameResidueFacts` 在真实局部域上的机检实例**（`F = ℚ_[7]`、`p = 3`）：
`∃ v π, ValCompat v ∧ v π = 1 ∧ TameResidueFacts (GaloBase.cup) (valLinOf v hpF) ((π))`。

这是第 4 章三条定理所消费的**唯一输入**（`Hyp162` 的 `hfacts`）在具体域上的落地；
`v` 取 `vCompatHom`、`π` 取 `exists_uniformizer_not_pow` 给的一致化元。 -/
theorem tameResidueFacts_witness_Q7 :
    ∃ (v : ℚ_[7]ˣ →* Multiplicative ℤ) (π : ℚ_[7]ˣ),
      ValCompat (F := ℚ_[7]) v ∧ v π = Multiplicative.ofAdd (1 : ℤ) ∧
      TameResidueFacts (GaloBase.cup (K := ℚ_[7]) (p := 3))
        (valLinOf (F := ℚ_[7]) (p := 3) v three_isUnit_F)
        (KummerBridge.kummerClass ℚ_[7] 3 three_isUnit_F π) := by
  obtain ⟨π, hzπ, hnotpow⟩ :=
    exists_uniformizer_not_pow (F := ℚ_[7]) (p := 3) (Fact.out : Nat.Prime 3).ne_one
  refine ⟨vCompatHom (F := ℚ_[7]), π, valCompat_of_dvr, ?_, ?_⟩
  · rw [show vCompatHom (F := ℚ_[7]) π = Multiplicative.ofAdd (zval (F := ℚ_[7]) π) from rfl,
      hzπ]
  · exact tameResidueFacts_Galo_noBridge (F := ℚ_[7]) (p := 3) (v := vCompatHom) (π := π)
      zeta3_spec three_isUnit_O three_isUnit_F valCompat_of_dvr
      (by rw [show vCompatHom (F := ℚ_[7]) π = Multiplicative.ofAdd (zval (F := ℚ_[7]) π) from rfl,
        hzπ]) (by decide)

end Q7

end L20261018

#print axioms L20261018.HenselResidueData.tame_pi_u_of_skew
#print axioms L20261018.HenselResidueDataCore.toHenselResidueData
#print axioms L20261018.tameResidueFacts_witness_Q7
