import L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization

/-!
# R1087（**T1 第二轮归约**：`explicitMap1` 对系数映射的标量线性性 ＋ `bridgeKc` 链的第一次望远镜化）

## 1. 库内侦察（`L46`／`L47`：**内容式**，禁按名字搜）

本轮对 `raw/TauCeti`（15,662 件；`raw/mathlib` 无 `.lean`）做内容式检索，关键词与结果：

| 关键词（内容式） | 命中 | 结论 |
|---|---|---|
| `cocyclesMap1` × `nsmul`／`smul` | 只有 `explicitCoeff1_eq_nsmul`（**自同态**版：`f : M →+[G] M`） | **一般的系数映射版不在库** ⟹ §2 自建 |
| `kummerCoeffAddEquivZMod` 全树 | 15 处（`EquivariantKummer`／`Local/Duality/FiniteModule`／`MuNRep`） | 它为 `addEquivOfAddCyclicCardEq`（**任意选基**，docstring 明言 not canonical） |
| `muNRepCohomologyEquivTrivialFp_one_apply` | `MuNRep.lean:495` | ★ **给出 `H¹` 层的显式分解**，正是望远镜化所需 |
| `muNRepEquivTrivialFp` | `MuNRep.lean` | `= kce⁻¹ ≻ zmodEquivRootsOfUnity.symm ≻ trivialFpEquiv.symm`（**ζ-典范**，与 `e_c` 的任意选基相对） |

## 2. 自建：`explicitMap1` 对系数映射的 `k`-标量线性性（库内缺，T1 的必需工具）

```
f = k • g  （逐点） ⟹ explicitMap1 φ f = k • explicitMap1 φ g
```

| 声明 | 内容 |
|---|---|
| **`explicitMap1_eq_nsmul`** | 上述工具（一般 `φ`／`f`／`g`，不限于自同态） |

## 3. 望远镜化第一步：`muNRepCohomologyEquivTrivialFp` 吃 `kummerClass` 的显式分解

`muNRepCohomologyEquivTrivialFp hζ 1` 的 `_one_apply` 里有一对
`OfDiscrete(muNRep) ≻ OfDiscrete(muNRep).symm`，与 `kummerClass` 里的 `OfDiscrete(muNRep)` **抵消**；
再对 `kce`（定义上 `= refl`）用 `explicitMap1_comp`，得

```
muNRepCohomologyEquivTrivialFp hζ 1 (kummerClass a)
  = OfDiscrete(trivialFp) ( explicitMap1 restrictEquiv (μ) (kummerMap a) )      μ := muNRepEquivTrivialFp
```

**这是 `bridgeKc` 链第一次被压成「模型比对 ∘ 一个 `H¹`-运输」**，与战役侧
`kummerClass a = h1ToVEquiv (explicitMap1 id e_c (kummerMap a))` 形状对照，
⟹ 下一步只剩两件事：①把 `cohomFpMap (restrictEquiv).symm` 与 `coeffMap iso` 也望远镜化（群变元抵消，
　 得「单一 `explicitMap1`」形态）；②`e_c` 与 `trivialFpEquiv ≻ μ` 只差非零标量（`Hyp206` ＋ §2 的工具）。

| 声明 | 内容 |
|---|---|
| **`explicitMap1_eq_nsmul`** | ★ **库内缺**的工具：`f = k • g（逐点）⟹ explicitMap1 φ f = k • explicitMap1 φ g` |
| **`muHom`** | `μ := muNRepEquivTrivialFp`（**ζ-典范**系数识别，与 `e_c` 的任意选基相对） |
| **`muHom_comp_kce`**／**`muHom_equivariant`** | `μ ∘ kce = μ`（`kce = refl`）／`μ` 的 `G_m`-等变性（两侧作用都平凡） |
| **`instContinuousSMulTrivialFp`** | `trivialFp` 的 `G_m`-作用连续（库内 `continuousSMul_trivialFp` 未注册为实例） |
| **`kummerMapToTrivialFp`** | `kummerMap` → `trivialFp` 的固定运输（复合形） |
| **`muNRepCohomologyEquivTrivialFp_one_kummerClass`** | ★ **望远镜化第一步**（见上） |

⚠ **工艺**：本轮的 `rfl`／defeq 检查会因项过大而 **timeout（5M heartbeats）**——
必须保证 `def` 与目标里的 `explicitMap1` 的**证明实参逐字一致**（Lean 4 的证明无关性使其可 defeq，
但比对代价与项大小成正比）；这也是把 `kummerMapToTrivialFp` 与 `muHom` **具名化**的动机。
-/

set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

/-! ### 2. `explicitMap1` 对系数映射的标量线性性（**库内缺**） -/

section Linear

variable {G : Type} [Monoid G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable {H : Type} [Monoid H] [TopologicalSpace H]
  {N : Type} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction H N] [ContinuousSMul H N]

/-- **`explicitMap1` 对系数映射的 `k`-标量线性性**（库内只有 `explicitCoeff1_eq_nsmul` 的**自同态**版）。

逐点 `f m = k • g m` ⟹ `explicitMap1 φ f = k • explicitMap1 φ g`。 -/
theorem explicitMap1_eq_nsmul (φ : H →ₜ* G) (f g : M →+ N) (hf : Continuous f)
    (hg : Continuous g)
    (hef : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (heg : ∀ (h : H) (m : M), g (φ h • m) = h • g m)
    {k : ℕ} (hk : ∀ m, f m = k • g m) :
    explicitMap1 G M H N φ f hf hef = k • explicitMap1 G M H N φ g hg heg := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    show (cocyclesMap1 G M H N φ f hf hef c : H1 H N)
        = k • (cocyclesMap1 G M H N φ g hg heg c : H1 H N)
    rw [← QuotientAddGroup.mk_nsmul]
    refine congrArg (fun z : Z1 H N => (z : H1 H N)) (Subtype.ext (funext fun h => ?_))
    have h1 : ((cocyclesMap1 G M H N φ f hf hef c : Z1 H N) : H → N) h
        = f ((c : G → M) (φ h)) := cocyclesMap1_apply _ _ _ _ _ _ _ _ c h
    have h2 : ((cocyclesMap1 G M H N φ g hg heg c : Z1 H N) : H → N) h
        = g ((c : G → M) (φ h)) := cocyclesMap1_apply _ _ _ _ _ _ _ _ c h
    rw [h1]
    rw [show (((k : ℕ) • (cocyclesMap1 G M H N φ g hg heg c : Z1 H N) : Z1 H N) : H → N) h
        = k • (((cocyclesMap1 G M H N φ g hg heg c : Z1 H N) : H → N) h) from rfl, h2, hk]

end Linear

/-! ### 3. 望远镜化第一步 -/

section Telescope

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `trivialFp` 的 `G_m`-作用连续（库内 `TauCeti.continuousSMul_trivialFp`，未注册为实例）。 -/
instance instContinuousSMulTrivialFp :
    ContinuousSMul (Field.absoluteGaloisGroup F)
      (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V :=
  TauCeti.continuousSMul_trivialFp p (Field.absoluteGaloisGroup F)

/-- **`μ := muNRepEquivTrivialFp`**：`muNRep` 的系数识别（**ζ-典范**）。 -/
noncomputable def muHom (hζ : IsPrimitiveRoot ζ p) :
    (ClassFieldTheory.muNRep p F).V →+
      (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V :=
  (ClassFieldTheory.muNRepEquivTrivialFp (n := p) (F := F) hζ).toAddMonoidHom

/-- **`kce = refl`**：`μ ∘ kce = μ`（`kummerCoeffEquivMuNRep` 是 `AddEquiv.refl`）。 -/
theorem muHom_comp_kce (hζ : IsPrimitiveRoot ζ p) :
    (muHom (F := F) (p := p) hζ).comp
        (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom
      = muHom (F := F) (p := p) hζ := by
  refine AddMonoidHom.ext fun x => ?_
  rfl

/-! ### 3b. `kummerMap` 到 `trivialFp` 的固定运输（`bridgeKc` 链的第一次望远镜化） -/

/-- **`μ` 的等变性**：`G_m` 两侧作用都平凡（`smul_kummerCoeff_eq_self` ＋ `trivialFp` 的平凡作用）。 -/
theorem muHom_equivariant (hζ : IsPrimitiveRoot ζ p) (k : Field.absoluteGaloisGroup F)
    (y : KummerCoeff F p) :
    muHom (F := F) (p := p) hζ
        ((absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) k • y)
      = k • muHom (F := F) (p := p) hζ y := by
  rw [show ((absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) k • y)
      = y from smul_kummerCoeff_eq_self hζ _ y]
  rfl

/-- **`kummerMap` 到 `trivialFp` 的固定运输**：先沿 `restrictEquiv` 与 `kce`（`= refl`）搬到 `muNRep`，
再沿 ζ-典范系数识别 `μ` 搬到 `trivialFp`。 -/
noncomputable def kummerMapToTrivialFp (hζ : IsPrimitiveRoot ζ p) :
    H1 (AbsoluteGaloisGroup F) (KummerCoeff F p) →+
      H1 (Field.absoluteGaloisGroup F)
        (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V :=
  (explicitMap1 (Field.absoluteGaloisGroup F) (ClassFieldTheory.muNRep p F).V
      (Field.absoluteGaloisGroup F)
      (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).V
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup F)) (muHom (F := F) (p := p) hζ)
      continuous_of_discreteTopology (muHom_equivariant (F := F) (p := p) hζ)).comp
    (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (Field.absoluteGaloisGroup F)
      (ClassFieldTheory.muNRep p F).V
      ((absoluteGaloisGroupRestrictEquiv F : Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
        Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
      (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom
      continuous_of_discreteTopology
      (fun g x => (ClassFieldTheory.kummerCoeffEquivMuNRep_smul (n := p) (F := F) g x).trans
        (TopRep.distribMulAction_smul _ g _).symm))

/-- ★ **望远镜化第一步**：`muNRepCohomologyEquivTrivialFp hζ 1` 吃 `kummerClass a` 后的显式形状 ——
一对 `OfDiscrete(muNRep) ≻ OfDiscrete(muNRep).symm` **抵消**，只剩一个固定运输作用于 `kummerMap a`。

这是 `bridgeKc` 链（`coeffMap iso ≻ cohomFpMap (restrictEquiv).symm ≻ muNRepCohomologyEquivTrivialFp`）
第一次被压成「模型比对 ∘ 一个 `H¹`-运输」。 -/
theorem muNRepCohomologyEquivTrivialFp_one_kummerClass (hζ : IsPrimitiveRoot ζ p) (a : Fˣ) :
    ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1
        (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a)
      = (TauCeti.trivialFp p (Field.absoluteGaloisGroup F)).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (kummerMapToTrivialFp (F := F) (p := p) hζ
            (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) := by
  rw [ClassFieldTheory.muNRepCohomologyEquivTrivialFp_one_apply]
  congr 1
  rw [ClassFieldTheory.kummerClass_eq_muNRepH1Equiv_kummerMap,
    ClassFieldTheory.muNRepH1Equiv_apply, AddEquiv.symm_apply_apply]
  rfl

end Telescope

end L20261018

#print axioms L20261018.explicitMap1_eq_nsmul
#print axioms L20261018.muHom_equivariant
#print axioms L20261018.muNRepCohomologyEquivTrivialFp_one_kummerClass
