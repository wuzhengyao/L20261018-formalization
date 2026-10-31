import Hyp219

/-!
# R1089（**T1 第四归约：群变元完全消掉 —— `bridgeKc` 的 `G_m`-绕行被消去**）

## 本轮结论

在 `Hyp219.cohomFpMap_ofDiscrete`（`cohomFpMap φ 1 ∘ OfDiscrete = OfDiscrete ∘ explicitMap1 φ id`）之上，
用 `explicitMap1_comp` ＋ `(restrictEquiv).comp (restrictEquiv).symm = id`，把**群变元完全消掉**：

```
cohomFpMap (restrictEquiv).symm 1 (OfDiscrete(trivialFp@G_m) (explicitMap1 restrictEquiv μ x))
  = OfDiscrete(trivialFp@G_a) (explicitMap1 id μ x)
```

**⟹ `bridgeKc` 链**（`coeffMap iso ∘ cohomFpMap (restrictEquiv).symm ∘ muNRepCohomologyEquivTrivialFp ∘ kummerClass`）
经 R1087 的望远镜化（`muNRepCohomologyEquivTrivialFp_one_kummerClass`）＋ 本轮，变成

```
bridgeKc a = coeffMap (GaloTrivialFp.iso).hom 1
               ( OfDiscrete(trivialFp@G_a) (explicitMap1 id μ (kummerMap a)) )
```

而战役侧是

```
kummerClass a = RS ( OfDiscrete(ZMod p@G_a) (explicitMap1 id e_c (kummerMap a)) )
```

**两侧群变元同为 `G_a`**，只剩「`coeffMap iso ∘ OfDiscrete(trivialFp)` ＋ `RS ∘ OfDiscrete(ZMod p)` 的模型比对」
与**系数层识别之差**（`e_c` 对 `trivialFpEquiv ∘ μ`，一维 ⟹ 非零标量，`Hyp206`）。

| 声明 | 内容 |
|---|---|
| **`restrictEquiv_comp_symm`** | `(restrictEquiv).comp (restrictEquiv).symm = ContinuousMonoidHom.id G_a` |
| **`cohomFpMap_symm_comp_restrict`** | ★ 上式与 `explicitMap1_comp` 复合后的**群变元抵消** |
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

section Cancel

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `(restrictEquiv).comp (restrictEquiv).symm = id`（作为 `→ₜ*`）。 -/
theorem restrictEquiv_comp_symm :
    (((absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F)) :
      Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F).comp
      (((absoluteGaloisGroupRestrictEquiv F).symm :
        AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F))
    = ContinuousMonoidHom.id (AbsoluteGaloisGroup F) := by
  refine ContinuousMonoidHom.ext fun x => ?_
  exact (absoluteGaloisGroupRestrictEquiv F).apply_symm_apply x

/-- **`μ` 搬到 `G_a`-侧**（载体 `(trivialFp p G_a).V` 与 `(trivialFp p G_m).V` **定义相等**，
都是 `ULift.{0} (ZMod p)`；探针 `rfl` 已确认）。 -/
noncomputable def muHomAbs (hζ : IsPrimitiveRoot ζ p) :
    KummerCoeff F p →+ (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V where
  toFun y := muHom (F := F) (p := p) hζ y
  map_zero' := map_zero (muHom (F := F) (p := p) hζ)
  map_add' a b := map_add (muHom (F := F) (p := p) hζ) a b

/-- **`μ`（`G_a` 侧）关于 `G_a`-作用的等变性**：两侧作用都平凡。 -/
theorem muHomAbs_equivariant (hζ : IsPrimitiveRoot ζ p) (k : AbsoluteGaloisGroup F)
    (y : KummerCoeff F p) :
    muHomAbs (F := F) (p := p) hζ (k • y) = k • muHomAbs (F := F) (p := p) hζ y := by
  show muHom (F := F) (p := p) hζ (k • y) = k • muHomAbs (F := F) (p := p) hζ y
  rw [show k • y = y from smul_kummerCoeff_eq_self hζ k y]
  rfl

/-- ★ **群变元抵消**：`cohomFpMap (restrictEquiv).symm` 与 `explicitMap1 restrictEquiv` 复合后群变元消掉。 -/
theorem cohomFpMap_symm_comp_restrict (hζ : IsPrimitiveRoot ζ p)
    (x : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p)) :
    (TauCeti.cohomFpMap p
        (((absoluteGaloisGroupRestrictEquiv F).symm :
          AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F)) 1).hom
        ((TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (Field.absoluteGaloisGroup F)
            (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V
            (((absoluteGaloisGroupRestrictEquiv F :
                Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F)) :
              Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
            (muHom (F := F) (p := p) hζ) continuous_of_discreteTopology
            (muHom_equivariant (F := F) (p := p) hζ) x))
      = (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (AbsoluteGaloisGroup F)
            (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
            (muHomAbs (F := F) (p := p) hζ) continuous_of_discreteTopology
            (muHomAbs_equivariant (F := F) (p := p) hζ) x) := by
  -- `explicitMap1_comp`：(第一因子 `restrictEquiv`，第二因子 `(restrictEquiv).symm`)
  have hkey := explicitMap1_comp
    (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p)
    (H := Field.absoluteGaloisGroup F)
    (N := (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V)
    (φ := ((absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
      Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F))
    (f := muHom (F := F) (p := p) hζ) continuous_of_discreteTopology
    (muHom_equivariant (F := F) (p := p) hζ)
    (K := AbsoluteGaloisGroup F)
    (P := (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V)
    (ψ := ((absoluteGaloisGroupRestrictEquiv F).symm :
      AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F))
    (q := AddMonoidHom.id (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V)
    continuous_of_discreteTopology
    (fun k n => by
      have h1 : (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).ρ
          (((absoluteGaloisGroupRestrictEquiv F).symm :
            AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F) k) n = n :=
        TauCeti.trivialFp_ρ_apply_apply (p := p)
          (G := Field.absoluteGaloisGroup F) _ n
      have h2 : (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).ρ k
          (n : (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V) = n :=
        TauCeti.trivialFp_ρ_apply_apply (p := p) (G := AbsoluteGaloisGroup F) k _
      exact h1.trans h2.symm)
  have hid : (((absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F)) :
      Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F).comp
      (((absoluteGaloisGroupRestrictEquiv F).symm :
        AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F))
      = ContinuousMonoidHom.id (AbsoluteGaloisGroup F) :=
    restrictEquiv_comp_symm (F := F)
  have hcmp : (AddMonoidHom.id (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V).comp
      (muHom (F := F) (p := p) hζ) = muHomAbs (F := F) (p := p) hζ := by
    ext y; rfl
  -- `hS : explicitMap1 (id G_a) μ = (explicitMap1 (restrictEquiv).symm id).comp (explicitMap1 restrictEquiv μ)`
  have hS : explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (AbsoluteGaloisGroup F)
        (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V
        (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
        (muHomAbs (F := F) (p := p) hζ) continuous_of_discreteTopology
        (muHomAbs_equivariant (F := F) (p := p) hζ)
      = (explicitMap1 (Field.absoluteGaloisGroup F)
          (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V
          (AbsoluteGaloisGroup F) (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V
          (((absoluteGaloisGroupRestrictEquiv F).symm :
            AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F))
          (AddMonoidHom.id (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V)
          continuous_of_discreteTopology
          (fun k n => by
            have h1 : (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).ρ
                (((absoluteGaloisGroupRestrictEquiv F).symm :
                  AbsoluteGaloisGroup F →ₜ* Field.absoluteGaloisGroup F) k) n = n :=
              TauCeti.trivialFp_ρ_apply_apply (p := p)
                (G := Field.absoluteGaloisGroup F) _ n
            have h2 : (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).ρ k
                (n : (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V) = n :=
              TauCeti.trivialFp_ρ_apply_apply (p := p) (G := AbsoluteGaloisGroup F) k _
            exact h1.trans h2.symm)).comp
        (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
          (Field.absoluteGaloisGroup F)
          (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V
          (((absoluteGaloisGroupRestrictEquiv F :
              Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F)) :
            Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
          (muHom (F := F) (p := p) hζ) continuous_of_discreteTopology
          (muHom_equivariant (F := F) (p := p) hζ)) :=
    (explicitMap1_congr_of_eq (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p)
      (H := AbsoluteGaloisGroup F) (N := (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V)
      _ _ _ _ hid hcmp).symm.trans hkey
  rw [cohomFpMap_ofDiscrete]
  congr 1
  rw [hS]
  rfl

/-- ★★ **`bridgeKc` 的最终形态（`G_m`-绕行完全消掉）**：把 R1087／R1088／R1089 三次望远镜化串起来。

```
bridgeKc hζ a = coeffMap (GaloTrivialFp.iso).hom 1
                  ( OfDiscrete(trivialFp@G_a) (explicitMap1 id μ (kummerMap a)) )
```

对比战役侧 `kummerClass a = RS (OfDiscrete(ZMod p@G_a) (explicitMap1 id e_c (kummerMap a)))`
—— **两侧群变元同为 `G_a`**，残余只剩「模型比对 ＋ 系数层识别之差」。 -/
theorem bridgeKc_eq_final (hζ : IsPrimitiveRoot ζ p) (a : Fˣ) :
    bridgeKc (F := F) p hζ a
      = ContinuousCohomology.coeffMap (GaloTrivialFp.iso F p).hom 1
          ((TauCeti.trivialFp p (AbsoluteGaloisGroup F)).explicitH1AddEquivContinuousCohomologyOfDiscrete
            (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
              (AbsoluteGaloisGroup F)
              (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V
              (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
              (muHomAbs (F := F) (p := p) hζ) continuous_of_discreteTopology
              (muHomAbs_equivariant (F := F) (p := p) hζ)
              (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd)) := by
  rw [bridgeKc]
  rw [muNRepCohomologyEquivTrivialFp_one_kummerClass (F := F) (p := p) hζ a]
  rw [kummerMapToTrivialFp_eq_merged (F := F) (p := p) hζ]
  rw [cohomFpMap_symm_comp_restrict (F := F) (p := p) hζ]

end Cancel

end L20261018

#print axioms L20261018.restrictEquiv_comp_symm
#print axioms L20261018.cohomFpMap_symm_comp_restrict
#print axioms L20261018.bridgeKc_eq_final
