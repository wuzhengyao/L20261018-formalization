import Hyp567

/-!
# S46 R16：★★★ **右格 `T ≅ CoindQuotient (Γ⧸I) ⊥ μ_p`（商同余，条件于子群对应）**

`contInvSES : 0 → Aᴵ → Bᴵ → T → 0` 与库内 `coindShortExact (Γ⧸I) ⊥ μ_p` 逐格对齐，
左格（`Hyp567` `Aᴵ ≅ A`）与中格（`Hyp564` `Bᴵ ≅ DiscreteCoind`）已备；本件做**右格**。

两条事实：
* `T = Bᴵ ⧸ contKI`，其中 `contKI = (contInvIncl).range`（`Hyp552`）；
* `CoindQuotient Γ' ⊥ A = DiscreteCoind Γ' ⊥ A ⧸ (DiscreteCoind.unit).range`（库内 `Quotient.lean:71`）。

于是 `QuotientAddGroup.congr`（mathlib：`e : G ≃ H` 提升为 `G⧸G' ≃ H⧸H'`）给出右格同构，
**唯一前提**是「`contKI` 在 `e` 下的像 = 常值子群」——本件把它留成显式假设 `hK`。

## 诚实边界

* `hK` 未证。它等于「`S.incl : A → DiscreteCoind Γ ⊥ A` 是常值嵌入」＋「`e` 把常值送到常值」
  ＋ `Aᴵ ≅ A`（`Hyp567`）。下一件做。
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
local instance trivialActionZModQuotR16 :
    DistribMulAction ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulZModQuotR16 :
    ContinuousSMul ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★★ **右格**：`T ≅ CoindQuotient (Γ⧸I) ⊥ μ_p`（条件于子群对应 `hK`）。 -/
theorem contT_equiv_coindQuotient
    (hK : (contKI (F := F) p I).map
        (contInvBEquivCoindBot (F := F) p I).toAddMonoidHom
      = (DiscreteCoind.unit ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)).toAddMonoidHom.range) :
    Nonempty (contT (F := F) p I
      ≃+ CoindQuotient ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)) :=
  ⟨QuotientAddGroup.congr (contKI (F := F) p I)
    ((DiscreteCoind.unit ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)).toAddMonoidHom.range)
    (contInvBEquivCoindBot (F := F) p I) hK⟩

end L20261018

#print axioms L20261018.contT_equiv_coindQuotient
