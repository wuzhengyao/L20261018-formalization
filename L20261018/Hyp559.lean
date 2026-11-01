import Hyp558

/-!
# S46 R7：★★★ **下降映射（函数层）** —— `contInvB → (Γ⧸I → μ_p)` 及其单射性

`S46-DIGEST` §4c-i 施工图的第二步。`Hyp558` 给了下降的**良定义性**（`contInvB_lift_wd`）；
本件把它装成 `Quotient.lift`，得到

```
contInvBDescend : Bᴵ →+ (Γ⧸I → ZMod p)
```

并机检三条：`_comp_mk`（`descend g ∘ mk = g`）、`_add`（加性，逐点）、**`_injective`**（由 `_comp_mk`
立即得：`descend g₁ = descend g₂ ⟹ g₁ = g₂`）。

## 诚实边界

* `descend` 的靶仍是**纯函数类型** `Γ⧸I → ZMod p`，尚未装进 `DiscreteCoind (Γ⧸I) ⊥ μ_p`
  ——缺的是 `IsLocallyConstant`（`h ∘ mk = g` ＋ `mk` 是商映射 ⟹ `h` 连续 ⟹ 局部常值）。
* 反向（`h ↦ h ∘ mk`）也**未做**。
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

/-- ★★★★ **下降映射（函数层）**：`g ∈ Bᴵ` ↦ 它在 `Γ⧸I` 上的下降，`Quotient.lift` 于
`Hyp558.contInvB_lift_wd`。 -/
noncomputable def contInvBDescendFun (g : contInvB (F := F) p I) :
    ((AbsoluteGaloisGroup F) ⧸ I) → ZMod p :=
  Quotient.lift (fun x : AbsoluteGaloisGroup F => (g : contB (F := F) p) x)
    (fun a b hab => contInvB_lift_wd (F := F) p I g a b (Quotient.sound hab))

/-- 计算律：`descend g` 沿商映射就是 `g` 本身。 -/
@[simp]
theorem contInvBDescendFun_comp_mk (g : contInvB (F := F) p I)
    (x : AbsoluteGaloisGroup F) :
    contInvBDescendFun (F := F) p I g (x : (AbsoluteGaloisGroup F) ⧸ I)
      = (g : contB (F := F) p) x := (rfl)

/-- 加性（逐点）。 -/
theorem contInvBDescendFun_add (g₁ g₂ : contInvB (F := F) p I) :
    contInvBDescendFun (F := F) p I (g₁ + g₂)
      = contInvBDescendFun (F := F) p I g₁ + contInvBDescendFun (F := F) p I g₂ := by
  funext q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  simp

/-- ★★★★ **下降映射是单射**：`descend g₁ = descend g₂ ⟹ g₁ = g₂`（由 `_comp_mk` 立得）。 -/
theorem contInvBDescendFun_injective :
    Function.Injective (contInvBDescendFun (F := F) p I) := by
  intro g₁ g₂ h
  apply Subtype.ext
  apply DiscreteCoind.ext
  intro x
  have := congrArg (fun f => f (x : (AbsoluteGaloisGroup F) ⧸ I)) h
  simpa using this

/-- ★★★ `contInvB` 到**函数加法群**的加法同态（`descend` 的有结构版本）。 -/
noncomputable def contInvBDescend :
    contInvB (F := F) p I →+ (((AbsoluteGaloisGroup F) ⧸ I) → ZMod p) where
  toFun := contInvBDescendFun (F := F) p I
  map_zero' := by
    funext q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    simp
  map_add' := contInvBDescendFun_add (F := F) p I

@[simp]
theorem contInvBDescend_apply (g : contInvB (F := F) p I) :
    contInvBDescend (F := F) p I g = contInvBDescendFun (F := F) p I g := (rfl)

/-- `contInvBDescend` 的单射性。 -/
theorem contInvBDescend_injective : Function.Injective (contInvBDescend (F := F) p I) :=
  contInvBDescendFun_injective (F := F) p I

end L20261018

#print axioms L20261018.contInvBDescendFun_comp_mk
#print axioms L20261018.contInvBDescendFun_injective
#print axioms L20261018.contInvBDescend
#print axioms L20261018.contInvBDescend_injective
