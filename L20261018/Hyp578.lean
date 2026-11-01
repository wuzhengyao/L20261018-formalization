import L20261018.Hyp577

/-!
# S47 R6：★★★★ **γ 完成** —— `H1` 上的 `(Γ⧸I)`-`DistribMulAction` 与 `M` 的商群等变性

`Hyp577` 给了 `H1 ↥N M` 上 `G ⧸ N`-标量作用的**良定义性**（`instSMulQuotientH1`）。
本件补四条公理（走 R6 判定的 **`AddMonoid.End` 路线**，完全绕开 `Quotient.liftOn` 的 `•` 解析问题）：

```
conjEndH1   : G →* AddMonoid.End (H1 ↥N M)         -- g ↦ explicitConj1 N g
conjEndQuot : (G ⧸ N) →* AddMonoid.End (H1 ↥N M)   -- QuotientGroup.lift（N ⊆ ker 由 explicitConj1_eq_id_of_mem）
instDistribMulActionQuotientH1 : DistribMulAction (G ⧸ N) (H1 ↥N M)
```

**关键工艺（R5 的卡点及其解法）**：结构体内四条公理一律先
`show (instSMulQuotientH1 N).smul q x = …`（把 `•` 提到 `SMul.smul` 层），再
`rw [← conjEndQuot_apply]` 换成 `AddMonoid.End` 的应用，最后 `map_one` / `map_mul` / `map_zero` /
`map_add` + `rfl`。**不这样写就会拿到 `G`-作用的 `SMulZeroClass G ?m`（stuck）。**

战役形态：
```
contM_quotient_smul (q : Γ ⧸ I) (x : Cᴵ) : contM (q • x) = q • contM x
```
⟹ **`M` 现在是 `(Γ⧸I)`-等变映射，`∂₂` 的第三因子完成**（源侧 `Cᴵ` 的 `Γ⧸I`-作用是
`FixedPoints.addSubgroup` 免费给的，靶侧本件补上）。
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

/-! ## 一般形态 -/

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SeparatelyContinuousMul G] [CompactSpace G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]

/-- 共轭作用的 `AddMonoid.End` 形态：`g ↦ explicitConj1 N g`。 -/
noncomputable def conjEndH1 : G →* AddMonoid.End (H1 ↥N M) where
  toFun g := explicitConj1 N g
  map_one' := explicitConj1_one N
  map_mul' g h := explicitConj1_mul N g h

/-- ★★★ `N` 作用平凡 ⟹ 共轭作用下降到 `G ⧸ N`。 -/
noncomputable def conjEndQuot : (G ⧸ N) →* AddMonoid.End (H1 ↥N M) :=
  QuotientGroup.lift N (conjEndH1 N) (fun n hn => explicitConj1_eq_id_of_mem N ⟨n, hn⟩)

/-- 下降到 `G ⧸ N` 后与 `Hyp577` 的标量作用是同一个函数。 -/
theorem conjEndQuot_apply (q : G ⧸ N) (x : H1 ↥N M) :
    (conjEndQuot N q) x = (instSMulQuotientH1 N).smul q x := by
  induction q using Quotient.inductionOn with
  | h g => rfl

/-- ★★★★ **`H1 ↥N M` 上的 `G ⧸ N`-`DistribMulAction`**（四条公理）。

原因子 `N` 作用平凡，故 `G`-共轭作用下降；四条公理由 `AddMonoid.End` 给出。 -/
noncomputable instance instDistribMulActionQuotientH1 :
    DistribMulAction (G ⧸ N) (H1 ↥N M) where
  smul := (instSMulQuotientH1 N).smul
  one_smul x := by
    show (instSMulQuotientH1 N).smul (1 : G ⧸ N) x = x
    rw [← conjEndQuot_apply N]
    show (conjEndQuot N 1) x = x
    rw [map_one]
    rfl
  mul_smul q₁ q₂ x := by
    show (instSMulQuotientH1 N).smul (q₁ * q₂) x =
      (instSMulQuotientH1 N).smul q₁ ((instSMulQuotientH1 N).smul q₂ x)
    rw [← conjEndQuot_apply N, ← conjEndQuot_apply N, ← conjEndQuot_apply N]
    show (conjEndQuot N (q₁ * q₂)) x = (conjEndQuot N q₁) ((conjEndQuot N q₂) x)
    rw [map_mul]
    rfl
  smul_zero q := by
    show (instSMulQuotientH1 N).smul q (0 : H1 ↥N M) = 0
    rw [← conjEndQuot_apply N]
    exact map_zero _
  smul_add q x y := by
    show (instSMulQuotientH1 N).smul q (x + y) =
      (instSMulQuotientH1 N).smul q x + (instSMulQuotientH1 N).smul q y
    rw [← conjEndQuot_apply N, ← conjEndQuot_apply N, ← conjEndQuot_apply N]
    exact map_add _ x y

end General

/-! ## 战役形态：`M` 的 `(Γ⧸I)`-等变性 -/

section Campaign

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [CompactSpace ↥I]

/-- 定义式：`(↑g : Γ ⧸ I)` 在 `H1 ↥I (ZMod p)` 上作用即 `g • ·`。 -/
theorem quotient_smul_mk_h1 (g : AbsoluteGaloisGroup F) (y : H1 ↥I (ZMod p)) :
    (g : AbsoluteGaloisGroup F ⧸ I) • y = g • y :=
  quotient_smul_mk I g y

/-- ★★★★★ **`M` 的 `(Γ⧸I)`-等变性**。

`∂₂` 的靶是 `H¹(Γ⧸I, H¹(I,μ_p))`，故 `M` 必须是 `(Γ⧸I)`-模态射；源侧 `Cᴵ` 的
`(Γ⧸I)`-作用由 `FixedPoints.addSubgroup` 免费给出，靶侧由
`instDistribMulActionQuotientH1` 给出。 -/
theorem contM_quotient_smul (q : AbsoluteGaloisGroup F ⧸ I) (x : contInvC (F := F) p I) :
    contM (F := F) p I (q • x) = q • contM (F := F) p I x := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [coe_quotient_smul_fixedPoints_addSubgroup, contM_smul, quotient_smul_mk_h1]

end Campaign

end L20261018

#print axioms L20261018.conjEndH1
#print axioms L20261018.conjEndQuot
#print axioms L20261018.conjEndQuot_apply
#print axioms L20261018.instDistribMulActionQuotientH1
#print axioms L20261018.quotient_smul_mk_h1
#print axioms L20261018.contM_quotient_smul
