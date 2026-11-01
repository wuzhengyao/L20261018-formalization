import L20261018.Infra.Cohomology.Coinduced.Step024_explicit_coeff_one_zero

/-!
# S66 R9：4d 第二步 —— **方块消去**：`(δ¹_Γ)⁻¹ ∘ Inf₂ = map φ fC ∘ (δ¹_{SES1})⁻¹`

`Hyp729` 给出方块（**连续模型**，`T` 任意）

```
δ¹_{SES1} ≫ Inf₂ = map φ fC 1 ≫ δ¹_Γ
```

`Hyp731` 给出 `δ¹_{SES1}` **可逆**（`Bᴵ` 在 `G⧸I` 上零调），
而 `δ¹_Γ` 可逆由 `Hyp492` 的判据（本仓 `Hyp731` 的局部重推 `delta_bijective_sesCoind1`）给
（`B` 在 `G` 上相邻两度零调 —— 战役里 `B = contB` 是余诱导模，`Hyp719` 已在用）。

**结论（4d 的第一格）**：对 `x : H²(G⧸I, Aᴵ)`，

```
(δ¹_Γ)⁻¹ (Inf₂ x)  =  map φ fC 1 ( (δ¹_{SES1})⁻¹ x )
```

**推导（一行代数）**：令 `y := (δ¹_{SES1})⁻¹ x`，则 `δ¹_{SES1} y = x`。把方块作用在 `y` 上：
`Inf₂ (δ¹_{SES1} y) = δ¹_Γ (map φ fC 1 y)`，即 `Inf₂ x = δ¹_Γ (map φ fC 1 y)`；
两边施 `(δ¹_Γ)⁻¹` 即得。**注意这里用到 `δ¹_{SES1}` 的满射性**（`y` 存在）与 `δ¹_Γ` 的**单射性**。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]
variable {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

/-- ★★★★ **一般短正合列的 `δ_n` 打包成加性等价**（`B` 在 `n`／`n+1` 两度零调）。

与 `Hyp731.deltaAddEquiv_sesCoind1` 同型，但**对任意 `S`**（后者是 `SES1` 的专用版）。 -/
noncomputable def deltaAddEquivOfSub (S : DiscreteShortExact G A B C) (n : ℕ)
    (h1 : Subsingleton ↑(continuousCohomology n
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (h2 : Subsingleton ↑(continuousCohomology (n + 1)
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat) :
    ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ G C)).toModuleCat ≃+
      ↑(continuousCohomology (n + 1) (TauCeti.ofDiscreteModule ℤ G A)).toModuleCat :=
  AddEquiv.ofBijective (S.delta n).hom.toLinearMap.toAddMonoidHom
    (delta_bijective_sesCoind1 S n h1 h2)

/-- `deltaAddEquivOfSub` 的前向作用就是 `δ_n` 本身。 -/
theorem deltaAddEquivOfSub_apply (S : DiscreteShortExact G A B C) (n : ℕ)
    (h1 : Subsingleton ↑(continuousCohomology n
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (h2 : Subsingleton ↑(continuousCohomology (n + 1)
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (y : ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ G C)).toModuleCat) :
    deltaAddEquivOfSub S n h1 h2 y = ⇑(ConcreteCategory.hom (S.delta n)) y :=
  rfl


/-! ## 2 4d 第一步：方块消去 -/

/-- ★★★★★ **4d 的方块消去**：`(δ¹_Γ)⁻¹ (Inf₂ x) = map φ fC 1 ((δ¹_{SES1})⁻¹ x)`。

输入即 `Hyp729` 的方块与 `Hyp731` 的可逆性；证明是**一行代数**（见 module docstring）。 -/
theorem delta_inv_comp_infl_eq (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (fC : TBI S I →+ C) (hfC : ∀ (g : G) (x : TBI S I), fC ((g : G ⧸ I) • x) = g • fC x)
    (hincl : ∀ a : FixedPoints.addSubgroup (↥I) A, (inclI S I a : B) = S.incl ↑a)
    (hproj : ∀ b : FixedPoints.addSubgroup (↥I) B,
      fC (QuotientAddGroup.mk' (inclI S I).range b) = S.proj ↑b)
    (hB1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat)
    (hB2 : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat)
    (hA1 : Subsingleton ↑(continuousCohomology 1
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (hA2 : Subsingleton ↑(continuousCohomology 2
      (TauCeti.ofDiscreteModule ℤ G B)).toModuleCat)
    (x : ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) A))).toModuleCat) :
    (deltaAddEquivOfSub S 1 hA1 hA2).symm
        ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
            (FixedPoints.addSubgroup (↥I) A).subtype.toIntLinearMap
            I.fixedPoints_subtype_quotientMk_smul) 2) x)
      = (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
            fC.toIntLinearMap hfC) 1)
        ((deltaAddEquiv_sesCoind1 S I hB1 hB2).symm x) := by
  -- 方块（`Hyp729`）在 `y := (δ¹_{SES1})⁻¹ x` 上的点值形态
  have hsq := delta_map_quotient_T (N := I) S (sesCoind1 S I) fC hfC hincl hproj 1
  have hy := ConcreteCategory.congr_hom hsq
    ((deltaAddEquiv_sesCoind1 S I hB1 hB2).symm x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hy
  -- `δ¹_{SES1} ((δ¹_{SES1})⁻¹ x) = x`
  have hxx : ⇑(ConcreteCategory.hom ((sesCoind1 S I).delta 1))
      ((deltaAddEquiv_sesCoind1 S I hB1 hB2).symm x) = x :=
    AddEquiv.apply_symm_apply (deltaAddEquiv_sesCoind1 S I hB1 hB2) x
  rw [hxx] at hy
  rw [AddEquiv.symm_apply_eq, deltaAddEquivOfSub_apply]
  simpa only [Nat.reduceAdd] using hy

end L20261018

#print axioms L20261018.deltaAddEquivOfSub
#print axioms L20261018.deltaAddEquivOfSub_apply
#print axioms L20261018.delta_inv_comp_infl_eq
