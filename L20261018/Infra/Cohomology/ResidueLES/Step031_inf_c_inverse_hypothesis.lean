import L20261018.Infra.Cohomology.ResidueLES.Step030_right_square_closed

/-!
# S46 R19：★★★ **`Inf_C⁻¹` 的假设**：`Subsingleton (H¹(I, C))`

`∂₂ := δ_Γ⁻¹ ≫ Inf_C⁻¹ ≫ M`（路线 A）。`Inf_C : H¹(Γ⧸I, Cᴵ) → H¹(Γ, C)` 是 inflation，
其同构性只需 `Subsingleton (H¹(I, C))`（inflation 单射恒真）。本件把这条假设**化归**为
一条更容易供给的条件：

```
Subsingleton (H¹(I, Bᴵ))  ∧  Subsingleton (H²(I, μ_p))   ⟹   Subsingleton (H¹(I, C))
```

证明 = 连续长正合列在 `H¹(I,C)` 处的正合性 `longExact_exact₃`（`HomologySequence.lean:243`）：
`δ¹ : H¹(I,C) → H²(I,μ_p)` 的靶是子单点 ⟹ `δ¹ y = 0` 恒成立 ⟹ 由正合性
`H¹(I,B) ↠ H¹(I,C)` 满 ⟹ 靶是子单点。

`Subsingleton (H²(I,μ_p))` 已由 `Hyp517.inertiaLoc_subsingleton_H2_zmod` 无条件供给；
`Subsingleton (H¹(I, Bᴵ))` 仍缺（`Bᴵ` 作为 `↥I`-模不是 `DiscreteCoind ↥I` 形态）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
  (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [CompactSpace ↥I]

/-- ★★★★ **`Subsingleton (H¹(I, C))`**（条件于 `H¹(I,Bᴵ)` 与该处 `H²` 的零调性）。 -/
theorem subsingleton_H1_contC
    [Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥I (contB (F := F) p)))]
    [Subsingleton (continuousCohomology 2
      (ofDiscreteModule ℤ ↥I (ZMod p)))] :
    Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥I (contC (F := F) p))) := by
  -- 正合性：`H¹(I,B) → H¹(I,C) → H²(I,Aᴵ)` 在中项正合
  have hex : Function.Exact
      (⇑(TauCeti.ContinuousCohomology.coeffMap
        (ofDiscreteModuleMap (contDimShiftSES (F := F) p I).proj.toIntLinearMap
          (fun _ _ => rfl)) 1))
      (⇑((contDimShiftSES (F := F) p I).delta 1)) :=
    DiscreteShortExact.longExact_exact₃ (contDimShiftSES (F := F) p I) 1
  -- 靶是子单点 ⟹ `δ¹` 恒取 0
  have hdelta : ∀ y, (contDimShiftSES (F := F) p I).delta 1 y = 0 :=
    fun y => Subsingleton.elim _ _
  refine ⟨fun x y => ?_⟩
  -- 由正合性取原像
  obtain ⟨a, ha⟩ := (hex y).mp (by simpa using hdelta y)
  obtain ⟨b, hb⟩ := (hex x).mp (by simpa using hdelta x)
  rw [← ha, ← hb]
  exact congrArg _ (Subsingleton.elim b a)

end L20261018

#print axioms L20261018.subsingleton_H1_contC
