import L20261018.Infra.Cohomology.Conjugation.Step003_m_body_complete

/-!
# S47 R5：γ 的第一块 —— `H1` 上 `G ⧸ N`-标量作用（良定义性）

`M` 的 `Γ`-层等变性已由 `Hyp574`–`Hyp576` 机检。要把 `M` 做成 **`(Γ⧸I)`-模态射**
（`∂₂` 的靶是 `H¹(Γ⧸I, H¹(I,μ_p))`），靶侧载体 `H1 ↥I (ZMod p)` 必须先带
`DistribMulAction (Γ⧸I)`。

本件交付这条下降的**良定义性**部分：

* `h1_smul_eq_self_of_mem`：`N` 在 `H1 ↥N M` 上作用平凡
  （库内 `Conjugation/Basic.lean:332 smul_eq_self_of_mem` 的 `H1` 形态）；
* `instSMulQuotientH1`：`SMul (G ⧸ N) (H1 ↥N M)`，由 `Quotient.liftOn` 经
  「`a⁻¹ * b ∈ N ⟹ a • x = b • x`」下降；
* `quotient_smul_mk`：定义式 `(↑g : G ⧸ N) • x = g • x`。

**此处已踩掉的坑（写下来省下一轮）**：`Quotient.liftOn` 的良定义性假设给的是
**`Setoid` 关系** `a ≈ b`（显示形态），`rw [QuotientGroup.leftRel_apply] at hab` **不匹配**；
正确转法是
`QuotientGroup.eq.mp (Quotient.sound hab : (mk a : G⧸N) = mk b)`。

**未完成（R6 起手）**：`DistribMulAction (G⧸N) (H1 ↥N M)` 的四条公理。实测卡点：
在结构体内 `smul_zero`／`smul_add` 的 `q • 0` 里 `•` 被解析到 **`G`-作用**上
（报 `typeclass instance problem is stuck: SMulZeroClass G ?m`），且用
`show (instSMulQuotientH1 N).smul q 0 = 0` 提到 `SMul.smul` 层后又有
`rw [quotient_smul_mk]` 不匹配的问题。**下轮的三条候选**：
① `letI` 局部装 `SMul` 再 `refine ⟨…⟩` 匿名构造（注意字段序 `smul / one_smul / mul_smul / smul_zero / smul_add`）；
② 走 `AddMonoid.End` 路线：`QuotientGroup.lift N (explicitConj1 N)` 造
`(G⧸N) →* AddMonoid.End (H1 ↥N M)`（`explicitConj1_one`／`_mul` ＋ `explicitConj1_eq_id_of_mem`
免费给齐），再由此造 `DistribMulAction`；
③ 借 `FixedPoints`：`N` 作用平凡 ⟹ `H1 ↥N M = FixedPoints.addSubgroup ↥N (H1 ↥N M)`，
用库内 `distribMulActionQuotientFixedPointsAddSubmonoid` 免费拿 `G⧸N`-作用再沿
`↥⊤ ≃ H1 ↥N M` 运输。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SeparatelyContinuousMul G] [CompactSpace G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]

/-- ★★★ **`N` 在 `H1 ↥N M` 上作用平凡**（`G`-共轭作用限制到 `N` 是恒等）。 -/
theorem h1_smul_eq_self_of_mem (n : ↥N) (x : H1 ↥N M) : (n : G) • x = x :=
  smul_eq_self_of_mem N n x

/-- ★★★ **`H1 ↥N M` 上的 `G ⧸ N`-标量作用**（`N` 作用平凡 ⟹ 良定义）。

良定义性：若 `a⁻¹ * b ∈ N`，则 `b = a * (a⁻¹ * b)`，故 `b • x = a • ((a⁻¹b) • x) = a • x`。 -/
noncomputable instance instSMulQuotientH1 : SMul (G ⧸ N) (H1 ↥N M) :=
  ⟨fun q x => Quotient.liftOn q (fun g : G => g • x) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ N :=
      QuotientGroup.eq.mp
        (Quotient.sound hab : (QuotientGroup.mk a : G ⧸ N) = QuotientGroup.mk b)
    clear hab
    show a • x = b • x
    have hb : b = a * (⟨a⁻¹ * b, hab'⟩ : ↥N) := by
      show b = a * (a⁻¹ * b)
      rw [mul_inv_cancel_left]
    rw [hb, mul_smul, h1_smul_eq_self_of_mem N ⟨a⁻¹ * b, hab'⟩ x])⟩

/-- 该作用的定义式。 -/
theorem quotient_smul_mk (g : G) (x : H1 ↥N M) : (g : G ⧸ N) • x = g • x := rfl

end General

end L20261018

#print axioms L20261018.h1_smul_eq_self_of_mem
#print axioms L20261018.instSMulQuotientH1
#print axioms L20261018.quotient_smul_mk
