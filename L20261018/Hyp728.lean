import Hyp727

/-!
# S65 R1：分片 **4b** —— GS `lemma-coinduced-invariants`

> `H^i(G ⧸ I, (Coind_⊥^G A)^I) = 0`（`i ≥ 1`，`I` 闭正规、`A` 离散）

这就是 GS 用来拆 (6.17)、进而得 `∂^i ∘ Inf = 0`（**C4**）的那条零调性。

## 路线（三步，全部库内 ＋ 4a）

1. **4a 的等变性** `coindBotInvariantsEquiv_smul`：`↥((Coind_⊥^G A)^I) ≃+ Coind_⊥^{G⧸I} A`
   是 `G ⧸ I`-等变的（左：`(g • m) x = m (x * g)`；右：`(q • F) y = F (y * q)`）——
   于是可经 `ofDiscreteModuleIso` ＋ `subsingleton_continuousCohomology_of_iso` **运输**；
2. **Shapiro（`U = ⊥`）**：`H^i(G⧸I, Coind_⊥^{G⧸I} A) = H^i(⊥, A)`；
3. **平凡群正次数零**：`subsingleton_continuousCohomology_succ_of_subsingleton`。

## 工艺要点

* `⊥ : Subgroup (G ⧸ I)` 上 `A` 的 `DistribMulAction` 由 `Hyp727.trivialBotActionU`（低优先）提供——
  `Shapiro` 与 `DiscreteCoind` 两侧必须取**同一个**实例，否则类型对不上；
* `⊥` 闭由 `Subgroup.coe_bot ▸ isClosed_singleton`（`G ⧸ I` 是 T1，profinit 商）；
* `TotallyDisconnectedSpace (G ⧸ I)` 用 `QuotientGroup.instTotallyDisconnectedSpace`（需 `I` 闭）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G] [TotallyDisconnectedSpace G]
variable (I : Subgroup G) [I.Normal] [IsClosed (I : Set G)]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-! ## 1 4a 的 `G ⧸ I`-等变性 -/

/-- ★ **4a 的等变性**：`((Coind_⊥^G A)^I) ≅ Coind_⊥^{G⧸I} A` 与 `G ⧸ I`-作用交换。 -/
theorem coindBotInvariantsEquiv_smul (g : G)
    (m : ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))) :
    coindBotInvariantsEquiv (I := I) ((g : G ⧸ I) • m)
      = (g : G ⧸ I) • coindBotInvariantsEquiv (I := I) m := by
  refine DiscreteCoind.ext fun q => ?_
  induction q using Quotient.inductionOn with
  | _ x =>
    have hmul : ((x : G ⧸ I)) * ((g : G ⧸ I)) = (((x * g) : G) : G ⧸ I) := rfl
    have hL : coindBotInvariantsEquiv (I := I) ((g : G ⧸ I) • m)
        (Quotient.mk (QuotientGroup.leftRel I) x) = (m : DiscreteCoind G ⊥ A) (x * g) := by
      show coindInvFun (I := I) ((g : G ⧸ I) • m) (Quotient.mk (QuotientGroup.leftRel I) x)
        = (m : DiscreteCoind G ⊥ A) (x * g)
      show (((g : G ⧸ I) • m : ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))) :
        DiscreteCoind G ⊥ A) x = (m : DiscreteCoind G ⊥ A) (x * g)
      rw [TauCeti.coe_quotient_smul_fixedPoints_addSubgroup,
        TauCeti.coe_smul_fixedPoints_addSubgroup, DiscreteCoind.coe_smul]
    have hR : ((g : G ⧸ I) • coindBotInvariantsEquiv (I := I) m)
        (Quotient.mk (QuotientGroup.leftRel I) x) = (m : DiscreteCoind G ⊥ A) (x * g) := by
      show (coindBotInvariantsEquiv (I := I) m) (((x : G ⧸ I)) * ((g : G ⧸ I)))
        = (m : DiscreteCoind G ⊥ A) (x * g)
      rw [hmul]
      show coindInvFun (I := I) m (((x * g) : G) : G ⧸ I) = (m : DiscreteCoind G ⊥ A) (x * g)
      rfl
    rw [hL, hR]

/-- 4a 的 **`ℤ`-线性版**：`AddEquiv.toIntLinearEquiv` 的 `Module ℤ` 隐式参数须在**已知类型**下合成
（元变量上合成失败，`L50`①）——故立为**顶层声明**，让 delta 展开负责 defeq。 -/
noncomputable def coindBotInvariantsIntLinearEquiv :
    ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A)) ≃ₗ[ℤ] DiscreteCoind (G ⧸ I) ⊥ A :=
  (coindBotInvariantsEquiv (I := I)).toIntLinearEquiv

/-! ## 2 分片 4b：零调性 -/

/-- `⊥ : Subgroup (G ⧸ I)` 在 `A` 上连续作用（平凡作用 ＋ `A` 离散）。 -/
theorem continuousSMul_bot_quotient : ContinuousSMul (⊥ : Subgroup (G ⧸ I)) A where
  continuous_smul := by
    have h : ∀ p : (⊥ : Subgroup (G ⧸ I)) × A, p.1 • p.2 = p.2 := fun p => rfl
    simpa only [h] using continuous_snd (X := (⊥ : Subgroup (G ⧸ I))) (Y := A)

/-- ★★ **GS `lemma-coinduced-invariants`（`i ≥ 1`）**：
`H^i(G ⧸ I, (Coind_⊥^G A)^I) = 0`。

`I` 闭正规、`G` profinite（紧 ＋ 全不连通 ＋ 分离乘）、`A` 离散连续 `G`-模。 -/
theorem subsingleton_H_quot_coindBot_invariants (i : ℕ) (hi : 1 ≤ i) :
    Subsingleton (continuousCohomology i (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A)))) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  haveI hCS : ContinuousSMul (⊥ : Subgroup (G ⧸ I)) A := continuousSMul_bot_quotient (I := I)
  -- 第 3 步 ＋ 第 2 步：`H^{j+1}(G⧸I, Coind_⊥^{G⧸I} A) = H^{j+1}(⊥, A) = 0`
  have hY : Subsingleton (continuousCohomology (j + 1) (ofDiscreteModule ℤ (G ⧸ I)
      (DiscreteCoind (G ⧸ I) ⊥ A))) := by
    have hbot : Subsingleton (continuousCohomology (j + 1)
        (ofDiscreteModule ℤ ↥(⊥ : Subgroup (G ⧸ I)) A)) :=
      ContinuousCohomology.subsingleton_continuousCohomology_succ_of_subsingleton (k := ℤ)
        (G := ↥(⊥ : Subgroup (G ⧸ I))) _ j
    exact (ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_iff (G := G ⧸ I)
      ⊥ (Subgroup.coe_bot (G := G ⧸ I) ▸ isClosed_singleton) A (j + 1)).mpr hbot
  -- 第 1 步：沿 4a（等变）运输
  haveI hMC : SMulCommClass (⊥ : Subgroup (G ⧸ I)) ℤ A := ⟨fun _ _ _ => rfl⟩
  have he : ∀ (q : G ⧸ I) (m : ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))),
      coindBotInvariantsIntLinearEquiv (I := I) (q • m)
        = q • coindBotInvariantsIntLinearEquiv (I := I) m := by
    intro q m
    have hq : q = ((Quotient.out q : G) : G ⧸ I) := (Quotient.out_eq q).symm
    rw [hq]
    exact coindBotInvariantsEquiv_smul (I := I) (g := Quotient.out q) m
  have e : ofDiscreteModule ℤ (G ⧸ I) ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A)) ≅
      ofDiscreteModule ℤ (G ⧸ I) (DiscreteCoind (G ⧸ I) ⊥ A) :=
    ofDiscreteModuleIso (coindBotInvariantsIntLinearEquiv (I := I)) he
  exact ContinuousCohomology.subsingleton_continuousCohomology_of_iso e (j + 1)

end L20261018

#print axioms L20261018.coindBotInvariantsEquiv_smul
#print axioms L20261018.coindBotInvariantsIntLinearEquiv
#print axioms L20261018.subsingleton_H_quot_coindBot_invariants
