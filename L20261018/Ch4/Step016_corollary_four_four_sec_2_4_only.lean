import L20261018.Ch4.Step015_thm_ramified_1_sec_2_4_only

/-!
# R1003：**4.4 只依赖 §2.4** —— `D` 作输入（`hK1` 保留为论文假设）

R1002 把 4.3(1) 降到"`D` 作输入"。本轮做 **4.4**（`:1646` 的未编号推论）的同一层：
把任意 `D : HenselResidueData` 沿 `Θ₁／Θ₂` 搬到显式载体（`Hyp141` 的搬运器，实测类无关），
再套 `Hyp112.ResidueCupData.corollary_4_4`。

**与 S25（完备层）的区别**：S25 的 `corollary_4_4_uncond'` 用**构造的** `D`（`henselResidueDataOfCup`）
＋ 已证的 `hK1`（`finrank_ker_valLin_eq_one`）；本文件用**任意** `D`（= 论文 §2.4）＋
**`hK1` 作论文假设**——这正是论文的层级（论文写「若 `d_K=1`」）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

section Part44

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- **把任意 `D` 搬到显式载体**（`Hyp141` 的搬运器 ＋ `Hyp145` 的 `Θ₁／Θ₂`）。
`VK` 取 `\ker D.val`（搬运前后同一类型）。 -/
noncomputable def henselResidueData_explicit_of_D {VK : Type} [AddCommGroup VK]
    [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p))) :
    HenselResidueData (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))
      (H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) VK
      (Theo352.cupLin (F := F) (p := p)) :=
  henselResidueDataTransport (theta1 (F := F) p) (theta2 (F := F) p)
    (LinearEquiv.refl (ZMod p) VK) (cup_compat_theta (F := F) (p := p)) D

/-- 搬运用到的 `val` 口径：`D_expl.val u = D.val (h1ToVEquiv u)`（`def` 体可见）。 -/
theorem henselResidueData_explicit_of_D_val {VK : Type} [AddCommGroup VK]
    [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p)))
    (u : H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :
    (henselResidueData_explicit_of_D (F := F) (p := p) D).val u
      = D.val (KummerBridge.h1ToVEquiv F p u) := rfl

/-- 显式载体的 `ResidueCupData`（由任意 `D` 搬来）。 -/
noncomputable def residueCupData_explicit_of_D {VK : Type} [AddCommGroup VK]
    [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p))) :
    ResidueCupData (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))
      (H2 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) VK :=
  (henselResidueData_explicit_of_D (F := F) (p := p) D).toResidueCupData
    (fun x y => Theo352.cupLin_skew (F := F) (p := p) x y)

end Part44

end L20261018
#print axioms L20261018.henselResidueData_explicit_of_D
