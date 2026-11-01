import L20261018.Infra.Cohomology.ResidueLES.Step025_delta_t_iso_usable

/-!
# S46 R14：★★ **`Aᴵ ≅ A`**（`μ_p` 上 `Γ`-作用平凡的一个机检推论）＋ 路线更正

## 数学内容

`μ_p` 上 `Γ`-作用**定义平凡**（`GaloBase.muP_ρ : ρ g x = x` 是 `rfl`），故
`Aᴵ = ↥(FixedPoints.addSubgroup (↥I) (ZMod p))` 就是 `ZMod p` 全体。本件把它机检成 `≃+`，
并锁死等变性（平凡作用对平凡作用是恒等）。

**用途**：把 `contInvSES : 0 → Aᴵ → Bᴵ → T → 0` 与库内
`coindShortExact (Γ⧸I) ⊥ (ZMod p) : 0 → A → DiscreteCoind → CoindQuotient → 0`
对齐时，左端这一格的等价是必需的（`Hyp563` 已给中项 `Bᴵ ≅ DiscreteCoind`）。

## ★ 路线更正（S46 R14）

此前 digest §5 记的「路线 B：`∂₂ := δ_T⁻¹ ≫ i_* ≫ M`」**是错的**：
`contInvSES` 的 `delta n` 是 `Hⁿ(Γ⧸I, T) → Hⁿ⁺¹(Γ⧸I, Aᴵ)`，故 `δ_T⁻¹` 的**源**是 `H²(Γ⧸I, Aᴵ)`，
不是 `H²(Γ, A)`。`∂₂` 必须从 `H²(Γ, A)` 出发，故只能用 **路线 A**：

```
∂₂ := δ_Γ⁻¹ ≫ Inf_C⁻¹ ≫ M           -- δ_Γ ✓(Hyp554)、Inf_C⁻¹ ✗、M ✗
```

`δ_T` 同构（`Hyp564`）用在本该用的地方：**(d) 的收口**（`Inf_A ≫ δ_Γ⁻¹ = δ_T⁻¹ ≫ map Φ fC`），
而不是 `∂₂` 的定义。
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

/-- `Γ⧸I` 在 `ZMod p` 上的平凡作用（`μ_p` 上 `Γ`-作用平凡）。 -/
local instance trivialActionZModQuot :
    DistribMulAction ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulZModQuot :
    ContinuousSMul ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★ **`Aᴵ = A`**：`μ_p` 上 `Γ`-作用平凡，故 `I`-不变点子群是全空间。 -/
noncomputable def contInvAEquiv : contInvA (F := F) p I ≃+ ZMod p where
  toFun x := (x : ZMod p)
  invFun x := ⟨x, by
    rw [FixedPoints.mem_addSubgroup]
    intro i
    rfl⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- `contInvAEquiv` 的等变性（平凡作用对平凡作用，恒等即兼容）。 -/
theorem contInvAEquiv_smul (q : (AbsoluteGaloisGroup F) ⧸ I) (x : contInvA (F := F) p I) :
    contInvAEquiv (F := F) p I (q • x)
      = q • contInvAEquiv (F := F) p I x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective I q
  show ((I.quotientMkContinuousMonoidHom h) • x : ZMod p) = (x : ZMod p)
  rw [show ((I.quotientMkContinuousMonoidHom h) • x : ZMod p) = h • (x : ZMod p) from
    I.fixedPoints_subtype_quotientMk_smul (M := ZMod p) h x]
  rfl

end L20261018

#print axioms L20261018.contInvAEquiv
#print axioms L20261018.contInvAEquiv_smul

