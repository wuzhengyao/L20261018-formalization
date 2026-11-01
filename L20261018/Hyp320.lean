import L20261018.Hyp223
import L20261018.Hyp315
import L20261018.Hyp207

/-!
# R1224（S34）：**(T1) 去掉完备性** —— `Hyp223` 的收口搬到一般 Hensel 层级

## 发现（`L47`：库内已有优先于自建）

`Hyp223.t1_closed`（R1092）**早已机检过 (T1)**：

```
∃ c ≠ 0, ∀ a, KummerBridge.kummerClass F p hp a = c • bridgeKc hζ a
```

但它的语句**继承了 `[IsNonarchimedeanLocalField F]`**（文件所在 section 的变量），
且**全仓从未被使用**。而 S33 的 `Hyp311`–`Hyp318` 从零重建了「系数识别差标量」的路线
（`hΘ`），把 `hΘ` 当成唯一开口。

**本轮判定**：`Hyp223` 的三块证明体（`explicitMap1_comp_coeff`／`bridgeKc_eq_muP`／`coeff_scalar`）
**逐条复核后均不含完备性**，`[IsNonarchimedeanLocalField F]` 只是 section 变量。
⟹ 在 `[ValuativeRel F] [TopologicalSpace F]` 下重写一遍即可（`Hyp315` 对 `Hyp221` 做过同样的事）。

## 本轮

| 声明 | 内容 |
|---|---|
| `bridgeKc_eq_muP'` | `bridgeKc = muP.OfDiscrete ∘ explicitMap1 id (down∘μ)`（**无完备性**） |
| `coeff_scalar'` | 两条系数映射只差非零标量（**无完备性**） |
| **`t1_closed_of_hζ'`** | ★ **(T1)**（**无完备性**） |
| **`t1_closed'`** | ★ **(T1)**，任意 `hp` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section T1NoComplete

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `muP` 的载体离散，故 `G`-作用连续（作用平凡）。`Hyp223` 的同名实例带完备性，此处重述。 -/
instance instContinuousSMulMuP320 : ContinuousSMul (AbsoluteGaloisGroup F) (GaloBase.muP F p).V where
  continuous_smul := continuous_snd

/-- ★ **`bridgeKc` 侧用同一模型 `muP`**（`Hyp222.bridgeKc_eq_muP` 的**无完备性**版）。 -/
theorem bridgeKc_eq_muP' (hζ : IsPrimitiveRoot ζ p) (a : Fˣ) :
    bridgeKc (F := F) p hζ a
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (AbsoluteGaloisGroup F) (GaloBase.muP F p).V
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
            ((downHom (F := F) (p := p)).toAddMonoidHom.comp
              (muHomAbs (F := F) (p := p) hζ))
            continuous_of_discreteTopology
            (fun g m => by
              show (downHom (F := F) (p := p))
                    ((muHomAbs (F := F) (p := p) hζ) (g • m))
                  = g • (downHom (F := F) (p := p))
                    ((muHomAbs (F := F) (p := p) hζ) m)
              rw [muHomAbs_equivariant (F := F) (p := p) hζ g m,
                map_smul (downHom (F := F) (p := p)) g _])
            (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) := by
  rw [bridgeKc_eq_final (F := F) (p := p) hζ a]
  rw [coeffMap_ofDiscrete (X := TauCeti.trivialFp p (AbsoluteGaloisGroup F))
    (Y := GaloBase.muP F p) (F := (GaloTrivialFp.iso F p).hom)
    (f := downHom (F := F) (p := p)) (hF := fun m => rfl)]
  congr 1

/-- `ZMod p`-标量与 `ℕ`-标量（取 `val`）一致。 -/
theorem zmod_smul_eq_val_nsmul' (c : ZMod p) (y : (GaloBase.muP F p).V) :
    c • y = c.val • y := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) c.val y, ZMod.natCast_rightInverse c]

/-- **两条系数映射只差非零标量**（一维 `KummerCoeff` ＋ 两者皆非零）—— **无完备性**版。 -/
theorem coeff_scalar' (hζ : IsPrimitiveRoot ζ p) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ x : KummerCoeff F p,
      (eCoeffHom (F := F) p hζ.neZero'.out.isUnit) x
        = c • ((downHom (F := F) (p := p)).toAddMonoidHom.comp
            (muHomAbs (F := F) (p := p) hζ)) x := by
  classical
  have hfr : Module.finrank (ZMod p) (KummerCoeff F p) = 1 :=
    TauCeti.finrank_kummerCoeff hζ.neZero'.out.isUnit
  have hfr2 : Module.finrank (ZMod p) (GaloBase.muP F p).V = 1 := Module.finrank_self (ZMod p)
  haveI : Nontrivial (KummerCoeff F p) :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hfr]; norm_num)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : KummerCoeff F p)
  set f : KummerCoeff F p →ₗ[ZMod p] (GaloBase.muP F p).V :=
    (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom.toZModLinearMap p with hf
  set g : KummerCoeff F p →ₗ[ZMod p] (GaloBase.muP F p).V :=
    ((downHom (F := F) (p := p)).toAddMonoidHom.comp
      (muHomAbs (F := F) (p := p) hζ)).toZModLinearMap p with hg
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 : f x₀ = f 0 := by rw [h0]; rfl
    have h1' : (KummerBridge.kummerCoeffLinearEquiv F p hζ.neZero'.out.isUnit) x₀
        = (KummerBridge.kummerCoeffLinearEquiv F p hζ.neZero'.out.isUnit) 0 := h1
    exact hx₀ ((KummerBridge.kummerCoeffLinearEquiv F p hζ.neZero'.out.isUnit).injective h1')
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : g x₀ = 0 := by rw [h0]; rfl
    have h2 : (TauCeti.trivialFpEquiv p (AbsoluteGaloisGroup F))
        ((ClassFieldTheory.muNRepEquivTrivialFp (n := p) (F := F) hζ) x₀) = 0 := by
      have h1' : (downHom (F := F) (p := p))
          ((muHomAbs (F := F) (p := p) hζ) x₀) = 0 := h1
      exact h1'
    have h3 : (ClassFieldTheory.muNRepEquivTrivialFp (n := p) (F := F) hζ) x₀ = 0 :=
      (TauCeti.trivialFpEquiv p (AbsoluteGaloisGroup F)).injective (by rw [h2]; rfl)
    refine hx₀ ((ClassFieldTheory.muNRepEquivTrivialFp (n := p) (F := F) hζ).injective ?_)
    rw [h3]
    exact (map_zero _).symm
  obtain ⟨c, hc, hco⟩ := exists_smul_eq_of_finrank_eq_one (K := ZMod p)
    (M := KummerCoeff F p) (N := (GaloBase.muP F p).V) hfr hfr2 hf0 hg0
  exact ⟨c, hc, fun x => hco x⟩

/-- ★ **(T1)（无完备性）**：两侧的 Kummer 类只差非零标量。 -/
theorem t1_closed_of_hζ' (hζ : IsPrimitiveRoot ζ p) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      KummerBridge.kummerClass F p hζ.neZero'.out.isUnit a = c • bridgeKc (F := F) p hζ a := by
  obtain ⟨c, hc, hco⟩ := coeff_scalar' (F := F) (p := p) hζ
  have hns : ∀ x : KummerCoeff F p,
      (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom x
        = c.val • ((downHom (F := F) (p := p)).toAddMonoidHom.comp
            (muHomAbs (F := F) (p := p) hζ)) x := by
    intro x
    rw [show (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom x
        = (eCoeffHom (F := F) p hζ.neZero'.out.isUnit) x from rfl, hco x]
    exact zmod_smul_eq_val_nsmul' (F := F) (p := p) c _
  have hpt : ∀ x : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p),
      explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (AbsoluteGaloisGroup F)
          (ZMod p) (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
          (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom
          continuous_of_discreteTopology
          (fun g m => (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).map_smul g m) x
        = c.val • explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (AbsoluteGaloisGroup F) (ZMod p)
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
            ((downHom (F := F) (p := p)).toAddMonoidHom.comp
              (muHomAbs (F := F) (p := p) hζ))
            continuous_of_discreteTopology
            (fun g m => by
              show (downHom (F := F) (p := p))
                    ((muHomAbs (F := F) (p := p) hζ) (g • m))
                  = g • (downHom (F := F) (p := p))
                    ((muHomAbs (F := F) (p := p) hζ) m)
              rw [muHomAbs_equivariant (F := F) (p := p) hζ g m,
                map_smul (downHom (F := F) (p := p)) g _]) x := by
    intro x
    exact congrArg (fun f => f x) (explicitMap1_eq_nsmul
      (φ := ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
      (f := (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom)
      (g := (downHom (F := F) (p := p)).toAddMonoidHom.comp
        (muHomAbs (F := F) (p := p) hζ))
      (hf := continuous_of_discreteTopology) (hg := continuous_of_discreteTopology)
      (hef := fun g m => (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).map_smul g m)
      (heg := fun g m => by
        show (downHom (F := F) (p := p)) ((muHomAbs (F := F) (p := p) hζ) (g • m))
            = g • (downHom (F := F) (p := p)) ((muHomAbs (F := F) (p := p) hζ) m)
        rw [muHomAbs_equivariant (F := F) (p := p) hζ g m,
          map_smul (downHom (F := F) (p := p)) g _])
      (k := c.val) (hk := hns))
  refine ⟨((c.val : ℕ) : ZMod p), ?_, fun a => ?_⟩
  · rw [show ((c.val : ℕ) : ZMod p) = c from ZMod.natCast_rightInverse c]
    exact hc
  · calc KummerBridge.kummerClass F p hζ.neZero'.out.isUnit a
        = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
            (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
              (AbsoluteGaloisGroup F) (ZMod p)
              (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
              (eCoeffHom (F := F) p hζ.neZero'.out.isUnit) continuous_of_discreteTopology
              (fun g m => (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).map_smul g m)
              (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) :=
          kummerClass_eq_muP' (F := F) (p := p) hζ.neZero'.out.isUnit a
      _ = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
            (c.val • explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
              (AbsoluteGaloisGroup F) (ZMod p)
              (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
              ((downHom (F := F) (p := p)).toAddMonoidHom.comp
                (muHomAbs (F := F) (p := p) hζ))
              continuous_of_discreteTopology
              (fun g m => by
                show (downHom (F := F) (p := p))
                      ((muHomAbs (F := F) (p := p) hζ) (g • m))
                    = g • (downHom (F := F) (p := p))
                      ((muHomAbs (F := F) (p := p) hζ) m)
                rw [muHomAbs_equivariant (F := F) (p := p) hζ g m,
                  map_smul (downHom (F := F) (p := p)) g _])
              (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) :=
          congrArg (fun y =>
            (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete y) (hpt _)
      _ = c.val • (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
            (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
              (AbsoluteGaloisGroup F) (ZMod p)
              (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
              ((downHom (F := F) (p := p)).toAddMonoidHom.comp
                (muHomAbs (F := F) (p := p) hζ))
              continuous_of_discreteTopology
              (fun g m => by
                show (downHom (F := F) (p := p))
                      ((muHomAbs (F := F) (p := p) hζ) (g • m))
                    = g • (downHom (F := F) (p := p))
                      ((muHomAbs (F := F) (p := p) hζ) m)
                rw [muHomAbs_equivariant (F := F) (p := p) hζ g m,
                  map_smul (downHom (F := F) (p := p)) g _])
              (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) :=
          map_nsmul _ _ _
      _ = c.val • bridgeKc (F := F) p hζ a := by
          rw [bridgeKc_eq_muP' (F := F) (p := p) hζ a]
          rfl
      _ = ((c.val : ℕ) : ZMod p) • bridgeKc (F := F) p hζ a :=
          (Nat.cast_smul_eq_nsmul (ZMod p) c.val (bridgeKc (F := F) p hζ a)).symm

/-- ★ **(T1)**（任意 `hp : IsUnit (p : F)`）—— **无完备性**。 -/
theorem t1_closed' (hp : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      KummerBridge.kummerClass F p hp a = c • bridgeKc (F := F) p hζ a := by
  obtain ⟨c, hc, hco⟩ := t1_closed_of_hζ' (F := F) (p := p) hζ
  have hpp : hp = hζ.neZero'.out.isUnit := Subsingleton.elim _ _
  subst hpp
  exact ⟨c, hc, hco⟩

end T1NoComplete

end L20261018

#print axioms L20261018.bridgeKc_eq_muP'
#print axioms L20261018.coeff_scalar'
#print axioms L20261018.t1_closed_of_hζ'
#print axioms L20261018.t1_closed'
