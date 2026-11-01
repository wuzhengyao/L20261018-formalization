import L20261018.Hyp559

/-!
# S46 R8：★★ **反向映射 `DiscreteCoind (Γ⧸I) ⊥ μ_p → Bᴵ`**（`h ↦ h ∘ mk`）

把 `Γ⧸I` 上的局部常值函数拉回成 `Γ` 上 `I`-不变的局部常值函数，两步：
局部常值 = `DiscreteCoind.isLocallyConstant` ＋ `IsLocallyConstant.comp_continuous` 于连续的 `mk`；
`I`-不变 = `DiscreteCoind.coe_smul`（`(i • f) x = f (x * i)`）＋ `mk (x * i) = mk x`（`QuotientGroup.eq`）。

## 诚实边界

* `≃+` 装配与 `IsLocallyConstant (contInvBDescend g)` 仍缺（下一件）。
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

/-- `↥(⊥ : Subgroup (Γ⧸I))` 在 `ZMod p` 上的平凡作用（Hyp557 的样板，`local` 不跨文件）。 -/
local instance trivialActionBotQuot :
    DistribMulAction (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulBotQuot :
    ContinuousSMul (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  continuous_smul := continuous_snd

/-- `mk (x * i) = mk x`（`i ∈ I`）：右乘 `I` 在商里不改变类。 -/
theorem quotientMk_mul_mem_eq (x : AbsoluteGaloisGroup F) (i : ↥I) :
    ((x * (i : AbsoluteGaloisGroup F) : AbsoluteGaloisGroup F) : (AbsoluteGaloisGroup F) ⧸ I)
      = (x : (AbsoluteGaloisGroup F) ⧸ I) := by
  have hmem : x⁻¹ * (x * (i : AbsoluteGaloisGroup F)) ∈ I := by
    have h : x⁻¹ * (x * (i : AbsoluteGaloisGroup F)) = (i : AbsoluteGaloisGroup F) := by group
    rw [h]; exact i.2
  exact (QuotientGroup.eq.mpr hmem).symm

/-- ★★★ **拉回的底层元素**：`h ↦ h ∘ mk` 作为 `B` 的元素（局部常值 ＋ `⊥`-等变性平凡）。 -/
noncomputable def coindBotPull (h : DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)) :
    contB (F := F) p :=
  ⟨fun x : AbsoluteGaloisGroup F => (h : ((AbsoluteGaloisGroup F) ⧸ I) → ZMod p)
      (x : (AbsoluteGaloisGroup F) ⧸ I), by
    refine ⟨?_, ?_⟩
    · exact (DiscreteCoind.isLocallyConstant h).comp_continuous continuous_quotient_mk'
    · intro u g
      rw [show u = 1 from Subsingleton.elim u 1]
      simp⟩

/-- 计算律：`coindBotPull h` 在 `x` 处的值。 -/
@[simp]
theorem coindBotPull_apply (h : DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p))
    (x : AbsoluteGaloisGroup F) :
    (coindBotPull (F := F) p I h) x = (h : ((AbsoluteGaloisGroup F) ⧸ I) → ZMod p)
      (x : (AbsoluteGaloisGroup F) ⧸ I) := (rfl)

/-- ★★★★ **拉回是 `I`-不变的**。 -/
theorem coindBotPull_mem (h : DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)) :
    coindBotPull (F := F) p I h ∈ FixedPoints.addSubgroup (↥I) (contB (F := F) p) := by
  rw [mem_contInvB_iff (F := F) p I]
  intro i x
  simp only [coindBotPull_apply, quotientMk_mul_mem_eq (F := F) I x i]

/-- ★★★★ **反向映射**：`DiscreteCoind (Γ⧸I) ⊥ μ_p →+ Bᴵ`。 -/
noncomputable def coindBotToContInvB :
    DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p) →+ contInvB (F := F) p I where
  toFun h := ⟨coindBotPull (F := F) p I h, coindBotPull_mem (F := F) p I h⟩
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show (coindBotPull (F := F) p I 0 : contB (F := F) p) x = (0 : contB (F := F) p) x
    rw [coindBotPull_apply]
    simp
  map_add' h₁ h₂ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show (coindBotPull (F := F) p I (h₁ + h₂) : contB (F := F) p) x
      = (coindBotPull (F := F) p I h₁ + coindBotPull (F := F) p I h₂ : contB (F := F) p) x
    rw [coindBotPull_apply]
    simp

end L20261018

#print axioms L20261018.quotientMk_mul_mem_eq
#print axioms L20261018.coindBotPull_mem
#print axioms L20261018.coindBotToContInvB
