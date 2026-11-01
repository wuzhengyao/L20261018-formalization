import Hyp568

/-!
# S46 R17：★★★ **`hK` 的内容层**：`e (contInvIncl a) = unit a`

`Hyp568` 把右格 `T ≅ CoindQuotient (Γ⧸I) ⊥ μ_p` 压到假设 `hK`（子群对应）。
`hK` 的内容是「`contKI` 在 `e` 下的像 = 常值子群」＝「`e ∘ contInvIncl` 与 `unit ∘ subtype` 相等」。
本件证这条**主等式**：

```
e (contInvIncl a) = DiscreteCoind.unit (Γ⧸I) ⊥ μ_p (a : μ_p)        (a : Aᴵ)
```

两侧底层都是**常值函数 `↑a`**：
* 左：`contInvIncl a = S.incl ↑a`，而 `coindShortExact` 的 `incl` **就是** `DiscreteCoind.unit`
  （库内 `Coinduced/Quotient.lean:141` 逐字），`unit_apply : unit m g = g • m`，`μ_p` 上作用平凡；
* 右：同一个 `unit_apply`。

## 诚实边界

* 本件**不证** `hK` 本身（还差 `range` 的搬运：`(contInvIncl.range).map e = (e ∘ contInvIncl).range`
  与 `range (unit ∘ subtype) = range unit`，须 `contInvAEquiv` 的满射性）。
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

/-- `Γ⧸I` 在 `ZMod p` 上的平凡作用（每件换新名字）。 -/
local instance trivialActionZModQuotR17 :
    DistribMulAction ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulZModQuotR17 :
    ContinuousSMul ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★★ **`hK` 的内容**：`e` 把 `Aᴵ ↪ Bᴵ` 送到 `unit`（常值函数）。 -/
theorem contInvIncl_equiv_unit (a : contInvA (F := F) p I) :
    contInvBEquivCoindBot (F := F) p I (contInvIncl (F := F) p I a)
      = DiscreteCoind.unit ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p) (a : ZMod p) := by
  apply DiscreteCoind.ext
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  show contInvBDescendFun (F := F) p I (contInvIncl (F := F) p I a)
      (x : (AbsoluteGaloisGroup F) ⧸ I)
    = DiscreteCoind.unit ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p) (a : ZMod p)
        (x : (AbsoluteGaloisGroup F) ⧸ I)
  rw [contInvBDescendFun_comp_mk, contInvIncl_coe]
  show ((contCoindSES (F := F) p).incl (a : ZMod p)) x = _
  rw [show (contCoindSES (F := F) p).incl
      = (DiscreteCoind.unit (AbsoluteGaloisGroup F) ⊥ (ZMod p)).toAddMonoidHom from rfl]
  rw [DiscreteCoind.unit_apply]
  show x • (a : ZMod p) = (x : (AbsoluteGaloisGroup F) ⧸ I) • (a : ZMod p)
  rfl

end L20261018

#print axioms L20261018.contInvIncl_equiv_unit
