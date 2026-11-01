import L20261018.Hyp556

/-!
# S46 R5：★★★ **`δ_T` iso 的「上半」** —— 零调性传输 ＋ 余诱导块在 `Γ⧸I` 上零调

## 两块内容

**(A) `subsingleton_of_topRep_iso`**：`TopRep` 同构传递 `Subsingleton`——若 `Hⁿ(G,N)` 是
子单点，则 `Hⁿ(G,M)` 也是（`coeffMap e.hom n` 有左逆 `coeffMap e.inv n` ⟹ 单射）。
这把「`contInvB ≅ DiscreteCoind (Γ⧸I) ⊥ μ_p`」的**下游义务**一次做掉：
一旦同构到手，`H^{1,2}(Γ⧸I, contInvB)` 的零调性自动成立，再由 `Hyp556.isIso_contInvSES_delta` 收口 `δ_T` iso。

**(B) `subsingleton_continuousCoindBot`**：`Hⁿ(Γ⧸I, DiscreteCoind (Γ⧸I) ⊥ A) = 0`（`n ≥ 1`）
——库内 `subsingleton_continuousCohomology_discreteCoind_iff`（Shapiro 的零调性传输）
＋ 平凡群零调（`subsingleton_continuousCohomology_succ_of_subsingleton`）。

## 诚实边界

* 本件**不证** `contInvB ≅ DiscreteCoind (Γ⧸I) ⊥ μ_p` 本身（施工图见 `S46-DIGEST` §4c-i）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

/-- ★★★ **`TopRep` 同构传递零调性**：`M ≅ N` ⟹ `Subsingleton (Hⁿ(N)) → Subsingleton (Hⁿ(M))`。 -/
theorem subsingleton_of_topRep_iso {R : Type} [Ring R] [TopologicalSpace R]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M N : TopRep R G} (e : M ≅ N) (n : ℕ)
    [Subsingleton (continuousCohomology n N)] :
    Subsingleton (continuousCohomology n M) := by
  have hcomp : TauCeti.ContinuousCohomology.coeffMap e.hom n
      ≫ TauCeti.ContinuousCohomology.coeffMap e.inv n
      = 𝟙 (continuousCohomology n M) := by
    rw [← TauCeti.ContinuousCohomology.coeffMap_comp]
    rw [Iso.hom_inv_id, TauCeti.ContinuousCohomology.coeffMap_id]
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : continuousCohomology n M,
      TauCeti.ContinuousCohomology.coeffMap e.inv n
        (TauCeti.ContinuousCohomology.coeffMap e.hom n z) = z := by
    intro z
    have := ConcreteCategory.congr_hom hcomp z
    simpa using this
  have h : TauCeti.ContinuousCohomology.coeffMap e.hom n x
      = TauCeti.ContinuousCohomology.coeffMap e.hom n y := Subsingleton.elim _ _
  calc x = TauCeti.ContinuousCohomology.coeffMap e.inv n
              (TauCeti.ContinuousCohomology.coeffMap e.hom n x) := (key x).symm
    _ = TauCeti.ContinuousCohomology.coeffMap e.inv n
              (TauCeti.ContinuousCohomology.coeffMap e.hom n y) := by rw [h]
    _ = y := key y

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
  (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [IsClosed (I : Set (AbsoluteGaloisGroup F))]

/-- `↥(⊥ : Subgroup (Γ⧸I))` 在 `ZMod p` 上的平凡作用（平凡群，唯一可能）。 -/
local instance trivialActionBotZMod :
    DistribMulAction (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulBotZMod :
    ContinuousSMul (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  continuous_smul := continuous_snd

/-- `⊥ : Subgroup (Γ⧸I)` 在环境空间中是闭的（`= {1}`，射有限群 `T1`）。 -/
theorem isClosed_bot_quot : IsClosed ((⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I)) :
    Set ((AbsoluteGaloisGroup F) ⧸ I)) := by
  rw [Subgroup.coe_bot]
  exact isClosed_singleton

/-- ★★★★ **(B)** `Hⁿ(Γ⧸I, DiscreteCoind (Γ⧸I) ⊥ A) = 0`（`n ≥ 1`）。

= 库内 `subsingleton_continuousCohomology_discreteCoind_iff`（Shapiro 零调性传输）
＋ 平凡群零调 `subsingleton_continuousCohomology_succ_of_subsingleton`。 -/
theorem subsingleton_continuousCoindBot (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (continuousCohomology n
      (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I)
        (DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rw [TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_iff
    (U := ⊥) (hU := isClosed_bot_quot (F := F) I) (A := ZMod p) m.succ]
  exact TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_succ_of_subsingleton
    (n := m) (X := ofDiscreteModule ℤ
      (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p))

end L20261018

#print axioms L20261018.subsingleton_of_topRep_iso
#print axioms L20261018.subsingleton_continuousCoindBot
