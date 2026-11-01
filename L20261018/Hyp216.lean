import L20261018.Hyp215

/-!
# R1085（**T1 第一归约落地：`muNRepH1Equiv` 的因子分解 ＋ T1 化为「两个固定运输的比较」**）

`Hyp214`／`Hyp215` 把 T1 的系数层障碍具名分离为 `e'' = kce ∘ e_c⁻¹`（`eDouble`）并给出
`e'' ∘ e_c = kce`（`eDouble_comp_eq_kce`）。本文件把它**推到 `H¹` 层**：

```
muNRepH1Equiv = OfDiscrete ∘ explicitMap1(restrictEquiv, e'') ∘ explicitCoeff1(e_c)
```

而战役侧（`Hyp140`／`Hyp19`）

```
KummerBridge.kummerClass = h1ToVEquiv ∘ explicitCoeff1(e_c)
```

**两侧共享最右端因子 `explicitCoeff1(e_c)`** ⟹ T1 化为**两个固定运输的比较**

```
(Θ₂)  thetaTwo  vs  (Θ₁)  h1ToVEquiv           ，由  「∀ x, Θ₂ x = c • Θ₁ x」   ⟹  T1
```

该比较**与 Kummer 理论无关**（两侧都是 `H¹(G, ZMod p)` 上的固定线性运输），是 T1 的**最终形态**。

| 声明 | 内容 |
|---|---|
| **`instDistribMulActionAbsGaloisZMod`**／**`instContinuousSMulAbsGaloisZMod`** | `G_m` 经 `restrictEquiv` 作用于 `ZMod p`（作用平凡；库内无此实例，须显式给） |
| **`eCoeffHom`** | `e_c : KummerCoeff F p →+[G] ZMod p`（两侧作用平凡 ⟹ `map_smul'` 空洞） |
| **`eDoubleHom`** | `e'' : ZMod p →+[G_m] muNRep.V`（同上） |
| **`kummerH1Equiv_apply_eq`** | 战役侧系数层 = `explicitCoeff1 eCoeffHom` |
| **`h1ZModToMuNRep`** | `H¹(G_m, muNRep.V) ← H¹(G, ZMod p)`：沿 `restrictEquiv` 与 `e''` 的运输 |
| **`muNRepH1Equiv_apply_eq`** | ★ `muNRepH1Equiv x = OfDiscrete (h1ZModToMuNRep (explicitCoeff1 e_c x))`（**因子分解**） |
| **`thetaTwo`** | `bridgeKc` 的右侧固定运输 `H¹(G, ZMod p) → V` |
| **`bridgeKc_eq_thetaTwo`** | `bridgeKc a = Θ₂ (explicitCoeff1 e_c (kummerMap a))` |
| **`kummerClass_eq_thetaOne`** | `KummerBridge.kummerClass a = Θ₁ (explicitCoeff1 e_c (kummerMap a))` |
| **`t1_of_thetaTwo`** | ★ **(∀ x, Θ₂ x = c • Θ₁ x) ⟹ T1**（`c ≠ 0`）——T1 的最终形态 |

**四个卡点全部按 `PROMPT-S30` ④.1 的定位落实**：① `DistribMulActionHom` 先行；② `id.comp ψ` **不走 `rw`**
（依赖重写失败）而走 `explicitMap1_congr_of_eq`（证明参数是隐式的）；③ `TopRep.distribMulAction` 的
`local instance` ＋ **新发现**：`G_m` 作用于 `ZMod p` 的实例库内不存在，须自建；④ `muNRep_smul_trivial`
用 `exact`（不走 `rw`）。

⚠ **工艺记录（本轮新踩）**：`explicitMap1_congr_of_eq` 的**具名实参**（`(φ := …)`）在此环境**静默失效**
（`φ` 的 Unicode 归一化问题 ⟹ 具名实参被丢弃，`rfl` 变成第一个位置实参 `G`），须用**位置下划线**
`explicitMap1_congr_of_eq _ _ _ _ _ _ _ _ h1 h2`。
-/

set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

/-! ### 0. 缺失的实例：`G_m` 经 `restrictEquiv` 作用于 `ZMod p`（作用平凡） -/

section Instances

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p]

/-- **`G_m = Field.absoluteGaloisGroup F` 经 `absoluteGaloisGroupRestrictEquiv F` 作用于 `ZMod p`**
（作用平凡，但实例必须显式：数学库只有 `AbsoluteGaloisGroup F` 的版本）。 -/
noncomputable instance instDistribMulActionAbsGaloisZMod :
    DistribMulAction (Field.absoluteGaloisGroup F) (ZMod p) :=
  DistribMulAction.compHom (ZMod p) (absoluteGaloisGroupRestrictEquiv F).toMonoidHom

/-- 该作用连续（作用平凡 ⟹ 标量乘是投影）。 -/
instance instContinuousSMulAbsGaloisZMod :
    ContinuousSMul (Field.absoluteGaloisGroup F) (ZMod p) :=
  ⟨by
    rw [show (fun q : (Field.absoluteGaloisGroup F) × ZMod p => q.1 • q.2) = Prod.snd from
      funext fun _ => rfl]
    exact continuous_snd⟩

end Instances

/-! ### 1. 两个等变化系数映射（卡点 ①③④） -/

section Hom

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **`e_c` 作为 `G`-等变映射** `KummerCoeff F p →+[G] ZMod p`：两侧 `G`-作用都平凡
（`smul_kummerCoeff_eq_self` ＋ `ZMod p` 的平凡作用）⟹ `map_smul'` 空洞。
证明项写法与 `KummerBridge.kummerH1Equiv` 逐字一致（否则下游 `rfl` 级别的比对会失败）。 -/
noncomputable def eCoeffHom (hp : IsUnit (p : F)) :
    KummerCoeff F p →+[AbsoluteGaloisGroup F] ZMod p :=
  { (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddMonoidHom with
    map_smul' := fun g m => by
      rw [smul_kummerCoeff_eq_self (KummerBridge.primitiveRoot_spec F p) g m]; rfl }

/-- **`e''` 作为 `G_m`-等变映射** `ZMod p →+[G_m] muNRep.V`（卡点 ④：`exact` 而非 `rw`）。 -/
noncomputable def eDoubleHom (hp : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p) :
    ZMod p →+[Field.absoluteGaloisGroup F] (ClassFieldTheory.muNRep p F).V :=
  { (eDouble (F := F) p hp) with
    map_smul' := fun g x => by
      show eDouble (F := F) p hp x
        = (ClassFieldTheory.muNRep p F).ρ g (eDouble (F := F) p hp x)
      exact muNRep_smul_trivial (F := F) (p := p) hζ g _ }

/-- **战役侧系数层就是 `explicitCoeff1 e_c`**（卡点 ①。`rfl` 级别）。 -/
theorem kummerH1Equiv_apply_eq (hp : IsUnit (p : F))
    (x : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p)) :
    KummerBridge.kummerH1Equiv F p hp x
      = explicitCoeff1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (eCoeffHom (F := F) p hp)
          continuous_of_discreteTopology x := by
  rw [KummerBridge.kummerH1Equiv, explicitCoeff1Equiv_apply]
  rfl

end Hom

/-! ### 2. 因子分解（卡点 ②） -/

section Factor

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **`H¹` 上「沿 `restrictEquiv` 与 `e''`」的固定运输** `H¹(G, ZMod p) →+ H¹(G_m, muNRep.V)`。 -/
noncomputable def h1ZModToMuNRep (hp : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p) :
    H1 (AbsoluteGaloisGroup F) (ZMod p) →+
      H1 (Field.absoluteGaloisGroup F) (ClassFieldTheory.muNRep p F).V :=
  explicitMap1 (AbsoluteGaloisGroup F) (ZMod p) (Field.absoluteGaloisGroup F)
    (ClassFieldTheory.muNRep p F).V
    ((absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
      Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
    ((eDoubleHom (F := F) p hp hζ).toAddMonoidHom) continuous_of_discreteTopology
    (fun k y => (eDoubleHom (F := F) p hp hζ).map_smul k y)

/-- ★ **因子分解**：

```
muNRepH1Equiv x = OfDiscrete ( h1ZModToMuNRep (explicitCoeff1 e_c x) )
```

与战役侧 `kummerClass a = h1ToVEquiv (explicitCoeff1 e_c (kummerMap a))` **共享最右端因子**。 -/
theorem muNRepH1Equiv_apply_eq (hp : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (x : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p)) :
    ClassFieldTheory.muNRepH1Equiv p F x
      = TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete (ClassFieldTheory.muNRep p F)
          (h1ZModToMuNRep (F := F) p hp hζ
            (explicitCoeff1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (eCoeffHom (F := F) p hp)
              continuous_of_discreteTopology x)) := by
  rw [ClassFieldTheory.muNRepH1Equiv_apply]
  congr 1
  -- 卡点 ②：`id.comp ψ = ψ`（**不能 `rw`**：`φ.comp ψ` 也出现在 `hcomp` 里 ⟹ 依赖重写失败）
  have hid : (ContinuousMonoidHom.id (AbsoluteGaloisGroup F)).comp
      ((absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
        Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
      = ((absoluteGaloisGroupRestrictEquiv F :
          Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
        Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F) :=
    ContinuousMonoidHom.ext fun _ => rfl
  -- 系数层复合恒等（`Hyp215`）
  have hcompq : ((eDoubleHom (F := F) p hp hζ).toAddMonoidHom).comp
      ((eCoeffHom (F := F) p hp).toAddMonoidHom)
      = (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom := by
    simp only [eDoubleHom, eCoeffHom]
    exact eDouble_comp_eq_kce (F := F) (p := p) hp
  -- `explicitMap1_comp`：`(φ∘ψ, q∘f)` 的拉回 = 两次拉回的复合
  have hkey := explicitMap1_comp
    (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p) (H := AbsoluteGaloisGroup F) (N := ZMod p)
    (φ := ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
    (f := (eCoeffHom (F := F) p hp).toAddMonoidHom)
    continuous_of_discreteTopology
    (fun g m => (eCoeffHom (F := F) p hp).map_smul g m)
    (K := Field.absoluteGaloisGroup F) (P := (ClassFieldTheory.muNRep p F).V)
    ((absoluteGaloisGroupRestrictEquiv F :
        Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
      Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
    ((eDoubleHom (F := F) p hp hζ).toAddMonoidHom) continuous_of_discreteTopology
    (fun k y => (eDoubleHom (F := F) p hp hζ).map_smul k y)
  -- 把 `(id, e_c)` 的复合换成 `(restrictEquiv, kce)`：用 `congr_of_eq`（证明参数隐式）
  have hkeyS :
      explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (Field.absoluteGaloisGroup F)
        (ClassFieldTheory.muNRep p F).V
        ((absoluteGaloisGroupRestrictEquiv F :
            Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F) :
          Field.absoluteGaloisGroup F →ₜ* AbsoluteGaloisGroup F)
        (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom
        continuous_of_discreteTopology
        (fun g x => (ClassFieldTheory.kummerCoeffEquivMuNRep_smul (n := p) (F := F) g x).trans
          (TopRep.distribMulAction_smul _ g _).symm)
      = (h1ZModToMuNRep (F := F) p hp hζ).comp
          (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (AbsoluteGaloisGroup F) (ZMod p)
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F)) (eCoeffHom (F := F) p hp).toAddMonoidHom
            continuous_of_discreteTopology (fun g m => (eCoeffHom (F := F) p hp).map_smul g m)) :=
    (explicitMap1_congr_of_eq _ _ _ _ _ _ _ _ hid hcompq).symm.trans hkey
  exact congrArg (fun g => g x) hkeyS

end Factor

/-! ### 3. `bridgeKc` 的固定运输 `Θ₂` 与 T1 的最终形态 -/

section Theta

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **`Θ₂`：`bridgeKc` 的右侧固定运输** `H¹(G, ZMod p) → V`。

它是 `muNRepCohomologyEquivTrivialFp ∘ OfDiscrete ∘ h1ZModToMuNRep` 再沿 `cohomFpMap`／`coeffMap`
回到 `V`——与 `Kummer 类`无关，只是「把 `ZMod p` 系数搬去 `μ_p`」的固定线性映射。 -/
noncomputable def thetaTwo (hp : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (x : H1 (AbsoluteGaloisGroup F) (ZMod p)) : GaloBase.V F p :=
  ContinuousCohomology.coeffMap (GaloTrivialFp.iso F p).hom 1
    ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1).hom
      ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
        (TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete (ClassFieldTheory.muNRep p F)
          (h1ZModToMuNRep (F := F) p hp hζ x))))

/-- **`bridgeKc a = Θ₂ (explicitCoeff1 e_c (kummerMap a))`**（`bridgeKc` 的定义 ＋ 因子分解）。 -/
theorem bridgeKc_eq_thetaTwo (hζ : IsPrimitiveRoot ζ p) (a : Fˣ) :
    bridgeKc (F := F) p hζ a
      = thetaTwo (F := F) p (hζ.neZero'.out.isUnit) hζ
          (explicitCoeff1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (eCoeffHom (F := F) p (hζ.neZero'.out.isUnit)) continuous_of_discreteTopology
            (TauCeti.kummerMap F p (hζ.neZero'.out.isUnit) a).toAdd) := by
  rw [bridgeKc, ClassFieldTheory.kummerClass_eq_muNRepH1Equiv_kummerMap]
  rw [muNRepH1Equiv_apply_eq (F := F) (p := p) (hζ.neZero'.out.isUnit) hζ]
  rfl

/-- **`KummerBridge.kummerClass a = h1ToVEquiv (explicitCoeff1 e_c (kummerMap a))`**（战役侧同形）。 -/
theorem kummerClass_eq_thetaOne (hp : IsUnit (p : F)) (a : Fˣ) :
    KummerBridge.kummerClass F p hp a
      = KummerBridge.h1ToVEquiv F p
          (explicitCoeff1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (eCoeffHom (F := F) p hp)
            continuous_of_discreteTopology (TauCeti.kummerMap F p hp a).toAdd) := by
  rw [KummerBridge.kummerClass, kummerH1Equiv_apply_eq]

/-- ★ **T1 的最终形态**：两个固定运输只差非零标量 ⟹ T1。

`∀ x, Θ₂ x = c • Θ₁ x` 是**纯线性代数陈述**（两侧都是 `H¹(G, ZMod p)` 上的固定运输），
不再涉及 Kummer 理论。 -/
theorem t1_of_thetaTwo (hp : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p) (c : ZMod p)
    (hc : c ≠ 0)
    (h : ∀ x : H1 (AbsoluteGaloisGroup F) (ZMod p),
      KummerBridge.h1ToVEquiv F p x = c • thetaTwo (F := F) p (hζ.neZero'.out.isUnit) hζ x) :
    ∃ c' : ZMod p, c' ≠ 0 ∧ ∀ a : Fˣ,
      KummerBridge.kummerClass F p hp a = c' • bridgeKc (F := F) p hζ a := by
  refine ⟨c, hc, fun a => ?_⟩
  have hpp : hp = hζ.neZero'.out.isUnit := Subsingleton.elim _ _
  subst hpp
  rw [kummerClass_eq_thetaOne (F := F) (p := p) (hζ.neZero'.out.isUnit) a,
    bridgeKc_eq_thetaTwo (F := F) (p := p) hζ a, h]

end Theta

end L20261018

#print axioms L20261018.kummerH1Equiv_apply_eq
#print axioms L20261018.muNRepH1Equiv_apply_eq
#print axioms L20261018.bridgeKc_eq_thetaTwo
#print axioms L20261018.kummerClass_eq_thetaOne
#print axioms L20261018.t1_of_thetaTwo
