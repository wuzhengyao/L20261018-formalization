import L20261018.Infra.Cohomology.ResidueLES.Step017_delta_t_iso_upper

/-!
# S46 R6：★★★ **`contInvB` 的逐点形态** ＋ **下降映射的良定义性**

这是 `contInvB ≅ DiscreteCoind (Γ⧸I) ⊥ μ_p`（`S46-DIGEST` §4c-i 施工图）的**第一步**：
把「`I`-不动」从 `i • g = g`（抽象作用）翻成**逐点**的 `g (x * i) = g x`，
再用 `QuotientGroup.eq` 把它接到商关系上，得到下降映射的良定义性。

## 关键约定（§4c-i 已定死，这里落地）

`coind` 的 `Γ`-作用是**右平移**：库内 `DiscreteCoind.coe_smul`
（`Coinduced/Discrete.lean:239`，逐字）：
```lean
@[simp] theorem coe_smul (g : G) (f : DiscreteCoind G U A) (x : G) : (g • f) x = f (x * g)
```
故 `i • g = g` ⟺ `∀ x, g (x * i) = g x` —— 右 `I`-不变；
而 `QuotientGroup` 的关系 `x⁻¹ * y ∈ I` 给出 `y = x * (x⁻¹ * y)` ⟹ **方向恰好匹配**（不需 `I◁Γ` 硬掰）。

## 诚实边界

* 本件**不证** `IsLocallyConstant` 那一半，也不构造完整的 `≃+`。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
  (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- ★★★ **`I`-不变性的逐点形态**：`g` 在 `Γ` 上是**右 `I`-不变**的。 -/
theorem mem_contInvB_iff {g : contB (F := F) p} :
    g ∈ FixedPoints.addSubgroup (↥I) (contB (F := F) p)
      ↔ ∀ (i : ↥I) (x : AbsoluteGaloisGroup F),
          g (x * (i : AbsoluteGaloisGroup F)) = g x := by
  rw [FixedPoints.mem_addSubgroup]
  constructor
  · intro h i x
    have hx : ((i : AbsoluteGaloisGroup F) • g) x = g x :=
      congrArg (fun f : contB (F := F) p => f x) (h i)
    simpa only [DiscreteCoind.coe_smul] using hx
  · intro h i
    ext x
    have hx : g (x * (i : AbsoluteGaloisGroup F)) = g x := h i x
    show ((i : AbsoluteGaloisGroup F) • g) x = g x
    simpa only [DiscreteCoind.coe_smul] using hx

/-- ★★★★ **下降映射的良定义性**：`g ∈ Bᴵ` 在 `Γ⧸I` 的右陪集上是常值。

`QuotientGroup.eq` 把 `mk a = mk b` 翻成 `a⁻¹ * b ∈ I`；`b = a * (a⁻¹ * b)` 后由
`mem_contInvB_iff` 的**右**不变性读出常值。 -/
theorem contInvB_apply_eq_of_mk_eq (g : contInvB (F := F) p I) {a b : AbsoluteGaloisGroup F}
    (hab : (a : (AbsoluteGaloisGroup F) ⧸ I) = b) : (g : contB (F := F) p) a
      = (g : contB (F := F) p) b := by
  have hmem : a⁻¹ * b ∈ I := QuotientGroup.eq.mp hab
  have hstep : (a * (a⁻¹ * b)) = b := by group
  rw [← hstep]
  exact ((mem_contInvB_iff (F := F) p I).mp g.2 ⟨a⁻¹ * b, hmem⟩ a).symm

/-- 良定义性（函数形式，供 `Quotient.lift` 直接消费）。 -/
theorem contInvB_lift_wd (g : contInvB (F := F) p I) :
    ∀ a b : AbsoluteGaloisGroup F, (a : (AbsoluteGaloisGroup F) ⧸ I) = b
      → (g : contB (F := F) p) a = (g : contB (F := F) p) b :=
  fun _ _ hab => contInvB_apply_eq_of_mk_eq (F := F) p I g hab

end L20261018

#print axioms L20261018.mem_contInvB_iff
#print axioms L20261018.contInvB_apply_eq_of_mk_eq
