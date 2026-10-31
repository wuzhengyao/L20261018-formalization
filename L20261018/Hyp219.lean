import Hyp218

/-!
# R1088（**T1 第三归约：群变元抵消 —— `cohomFpMap` 的群变换被消掉**）

## 1. 库内侦察（内容式，`L46`／`L47`）

| 关键词 | 命中 | 结论 |
|---|---|---|
| `explicitH1AddEquivContinuousCohomologyOfDiscrete_map` | `CohomologyComparison.lean:491` | ★ **正是所需**：`OfDiscrete` 比较对**相容对** `(φ, F)` 的自然性 |
| `explicitH1AddEquivContinuousCohomologyOfDiscrete_apply` | 同文件 `:482` | `OfDiscrete = ofDiscreteModuleRestrictScalarsIntEquiv ∘ explicitH1AddEquivContinuousCohomology` |
| `cohomFpMap` | `TrivialFp.lean:299` | `= ContinuousCohomology.map φ (eqToHom (res_trivialFp_hom p φ)) n` |
| `trivialFpEquiv_eqToHom_res_trivialFp_hom` | `TrivialFp.lean:292` | `eqToHom` 的**取值不变性**（`rfl`）—— 给出 `hF : ∀ m, F.hom m = m` |
| `res_trivialFp_hom` | `TrivialFp.lean:284` | `TopRep.res φ (trivialFp p G) = trivialFp p H`（平凡系数的限制不变） |

## 2. 本轮结论

**(A) 合并形**：`kummerMapToTrivialFp = explicitMap1 restrictEquiv μ`（单一 `explicitMap1`）——由 `explicitMap1_comp` ＋ `μ ∘ kce = μ`。

**(B) 群变元抵消**（本轮核心）：

```
cohomFpMap ψ 1 (OfDiscrete(trivialFp@G_m) (explicitMap1 φ μ x))
  = OfDiscrete(trivialFp@G_a) (explicitMap1 ψ id (explicitMap1 φ μ x))
  = OfDiscrete(trivialFp@G_a) (explicitMap1 (ψ ∘ φ) μ x)
```

取 `φ := restrictEquiv`、`ψ := restrictEquiv.symm`（`ψ ∘ φ = id`）⟹

```
cohomFpMap (restrictEquiv).symm 1 (OfDiscrete(trivialFp@G_m) (explicitMap1 restrictEquiv μ x))
  = OfDiscrete(trivialFp@G_a) (explicitMap1 id μ x)
```

**⟹ `bridgeKc` 链的 `G_m`-绕行被完全消掉**：`bridgeKc` 只剩「`coeffMap iso` ∘ `OfDiscrete(trivialFp@G_a)` ∘ `explicitMap1 id μ`」，
而战役侧是「`RS` ∘ `OfDiscrete(ZMod p@G_a)` ∘ `explicitMap1 id e_c`」——**两侧群变元同为 `G_a`**，
⟹ T1 的残余只剩**系数层识别之差**（`e_c` 对 `trivialFpEquiv ∘ μ`，一维 ⟹ 非零标量，`Hyp206`）。

| 声明 | 内容 |
|---|---|
| **`kummerMapToTrivialFp_eq_merged`** | 合并形（单一 `explicitMap1 restrictEquiv μ`） |
| **`cohomFpMap_ofDiscrete`** | ★ `cohomFpMap φ 1 ∘ OfDiscrete = OfDiscrete ∘ explicitMap1 φ id`（**库内缺**，本轮自建） |

**下一轮（`Hyp220`）**：把 (B) 与合并形复合，再用 `explicitMap1_comp` 与
`(restrictEquiv).symm.comp restrictEquiv = id` 收成
`cohomFpMap (restrictEquiv).symm 1 ∘ OfDiscrete ∘ explicitMap1 restrictEquiv μ = OfDiscrete ∘ explicitMap1 id μ`。
（注意 `trivialFp p G` 与 `trivialFp p H` 的载体都是 `ULift.{0} (ZMod p)`（`G` 宇宙 0）⟹ 定义相等，可搬；两侧作用均平凡。）
-/

set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

/-! ### (A) 合并形 -/

section Merged

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **合并形**：`kummerMapToTrivialFp = explicitMap1 restrictEquiv μ`（单一 `explicitMap1`）。 -/
theorem kummerMapToTrivialFp_eq_merged (hζ : IsPrimitiveRoot ζ p) :
    kummerMapToTrivialFp (F := F) (p := p) hζ
      = explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
          (Field.absoluteGaloisGroup F)
          (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V
          ((absoluteGaloisGroupRestrictEquiv F :
              Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
            Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
          (muHom (F := F) (p := p) hζ) continuous_of_discreteTopology
          (muHom_equivariant (F := F) (p := p) hζ) := by
  have hkey := explicitMap1_comp
    (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p)
    (H := Field.absoluteGaloisGroup F) (N := (ClassFieldTheory.muNRep p F).V)
    (φ := ((absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
      Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F))
    (f := (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom)
    continuous_of_discreteTopology
    (fun g x => (ClassFieldTheory.kummerCoeffEquivMuNRep_smul (n := p) (F := F) g x).trans
      (TopRep.distribMulAction_smul _ g _).symm)
    (K := Field.absoluteGaloisGroup F) (P := (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V)
    (ψ := ContinuousMonoidHom.id (Field.absoluteGaloisGroup F))
    (q := muHom (F := F) (p := p) hζ) continuous_of_discreteTopology
    (muHom_equivariant (F := F) (p := p) hζ)
  have hid : (((absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
        Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)).comp
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F))
      = ((absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
        Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F) := by
    ext x; rfl
  have hcompq : ((muHom (F := F) (p := p) hζ).comp
        (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom)
      = muHom (F := F) (p := p) hζ := muHom_comp_kce (F := F) (p := p) hζ
  exact hkey.symm.trans (explicitMap1_congr_of_eq _ _ _ _ _ _ _ _ hid hcompq)

end Merged

/-! ### (B) `cohomFpMap` 的自然性（库内缺） -/

section Naturality

variable (p : ℕ) [Fact p.Prime]
variable {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (φ : H →ₜ* G)

attribute [local instance] TopRep.distribMulAction

/-- `trivialFp` 的 `G`-作用连续（库内 `TauCeti.continuousSMul_trivialFp` 未注册为实例）。 -/
instance instContinuousSMulTrivialFpGen (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ContinuousSMul G (TauCeti.trivialFp p G).V :=
  TauCeti.continuousSMul_trivialFp p G

/-- ★ **`cohomFpMap` 对 `OfDiscrete` 的自然性**（库内缺）：群变换可以搬进 `explicitMap1`。

`cohomFpMap φ = ContinuousCohomology.map φ (eqToHom (res_trivialFp_hom p φ))`，而
`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_map` 正是 `OfDiscrete` 比较对相容对的自然性；
两者用 `trivialFpEquiv_eqToHom_res_trivialFp_hom`（`eqToHom` 不改取值）接上。 -/
theorem cohomFpMap_ofDiscrete (x : H1 G (TauCeti.trivialFp p G).V) :
    (TauCeti.cohomFpMap p φ 1).hom
        ((TauCeti.trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete x)
      = (TauCeti.trivialFp p H).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 G (TauCeti.trivialFp p G).V H (TauCeti.trivialFp p H).V φ
            (AddMonoidHom.id (TauCeti.trivialFp p G).V) continuous_of_discreteTopology
            (fun h m => by
              have h1 : (TauCeti.trivialFp p G).ρ (φ h) m = m :=
                TauCeti.trivialFp_ρ_apply_apply (p := p) (G := G) (φ h) m
              have h2 : (TauCeti.trivialFp p H).ρ h m = m :=
                TauCeti.trivialFp_ρ_apply_apply (p := p) (G := H) h m
              exact h1.trans h2.symm) x) := by
  have hmap : (TauCeti.cohomFpMap p φ 1).hom
      = (_root_.ContinuousCohomology.map φ
          (CategoryTheory.eqToHom (TauCeti.res_trivialFp_hom p φ)) 1).hom := by
    rw [TauCeti.cohomFpMap_def]
  rw [hmap]
  refine TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_map
    (X := TauCeti.trivialFp p G) (Y := TauCeti.trivialFp p H) φ
    (CategoryTheory.eqToHom (TauCeti.res_trivialFp_hom p φ)) (AddMonoidHom.id (TauCeti.trivialFp p G).V)
    (fun m => ?_) (fun h m => by
      have h1 : (TauCeti.trivialFp p G).ρ (φ h) m = m :=
        TauCeti.trivialFp_ρ_apply_apply (p := p) (G := G) (φ h) m
      have h2 : (TauCeti.trivialFp p H).ρ h m = m :=
        TauCeti.trivialFp_ρ_apply_apply (p := p) (G := H) h m
      exact h1.trans h2.symm) x
  refine (TauCeti.trivialFpEquiv p H).injective ?_
  rw [TauCeti.trivialFpEquiv_eqToHom_res_trivialFp_hom]
  rfl

end Naturality

end L20261018

#print axioms L20261018.kummerMapToTrivialFp_eq_merged
#print axioms L20261018.cohomFpMap_ofDiscrete
