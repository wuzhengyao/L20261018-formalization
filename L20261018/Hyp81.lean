import L20261018.Hyp80
import L20261018.Hyp46
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic

/-!
# 3.2 的 `ind`：`H²(G_F, μ_p)` 到 `Br F` 的载体链（R897）

3.2(1)(2) 的 A 档要求把 `ind : GaloBase.H2 F p → ℕ` **定义出来**（现在是参数），
即把论文的 `H²(F, μ_p)`（在本战役里是 `GaloBase.H2 F p = H²(G_F, muP)`）接到
`TauCeti` 的 Brauer 群 `Br F` 上——`ind` 是「该 Brauer 类里除代数的指数」。

## 载体链（三层，全部用库里现成件）

```
GaloBase.H2 F p = H²(G^Tc, muP F p)
  ≃+ H²(G^Tc, trivialFp p G^Tc)        ← GaloTrivialFp.cohomEquiv 2（Hyp45；`trivialFp ≅ muP`）
  ≃ₗ H²(G^m, trivialFp p G^m)          ← TauCeti.cohomFpLinearEquiv（沿 absoluteGaloisGroupRestrictEquiv）
  ≃ₗ H²(G^m, muNRep p F)               ← TauCeti.muNRepCohomologyEquivTrivialFp（TauCeti 现成）
  →  Br F                              ← TauCeti.h2MuToBr
```

其中 `G^Tc = TauCeti.AbsoluteGaloisGroup F`、`G^m = Field.absoluteGaloisGroup F`。

**侦察更正（R897）**：R895/R896 的计划是「照 `Hyp45` 模板手写一个 `TopRep` 同构
`muP ≅ (KummerCoeff 上的平凡表示)`，再 `ContinuousCohomology.coeffMap`」。
**该同构库里早有**——`TauCeti.ClassFieldTheory.muNRepIsoTrivialFp`
（`muNRep n F ≅ trivialFp n G^m`）＋ 其上同调版 `muNRepCohomologyEquivTrivialFp`，
而**群载体的那一层**是 `TauCeti.cohomFpLinearEquiv`（`G ≃ₜ* H` ⟹ `cohomFp` 等价，
`TrivialFp.lean` 的 `## Main results` 里）。故 `Hyp80` 的手写线性性对本步**不再必要**
（保留无害，它是 `μ_p ≅ ℤ/p` 的独立机检件）。

## 主结果

* `H2Bridge.gE`／`mE`：三层载体等价（逐次）。
* `H2Bridge.redEquiv_cup`：**杯积相容**——三层等价把 `GaloBase.cup`（即 `muPairing` 的杯积）
  送到 `kummerCupPairing` 的杯积。三层的自然性分别由
  `Hyp46.cupFp_coeffMap_eq_cup`／`TauCeti.cupFp_map`／
  `TauCeti.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup` 提供。
* `H2Bridge.brOfH2`：`GaloBase.H2 F p →+ Br F`。
* `H2Bridge.brOfH2_cup`：杯积形式的 `Br F` 值。
* `H2Bridge.brOfH2_injective`：`p` 在 `F` 中可逆时单射（`h2MuToBr_injective` ＋ 三层等价）。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace H2Bridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}

/-! ### 第一层：`trivialFp p G^Tc ≅ muP F p`（`Hyp45`） -/

/-- `cohomEquiv` 就是沿 `iso` 的 `coeffMap`（定义相等）。 -/
theorem cohomEquiv_eq_coeffMap (d : ℕ) (x : TauCeti.cohomFp p (AbsoluteGaloisGroup K) d) :
    (GaloTrivialFp.cohomEquiv K p d) x
      = ContinuousCohomology.coeffMap (GaloTrivialFp.iso K p).hom d x :=
  rfl

/-- **第一层的手逆**：`H²(muP) ≃+ H²(trivialFp)`。 -/
noncomputable def cE :
    ↑(continuousCohomology 2 (GaloBase.muP K p)).toModuleCat ≃+
      TauCeti.cohomFp p (AbsoluteGaloisGroup K) 2 :=
  (GaloTrivialFp.cohomEquiv K p 2).symm

/-- **第一层的杯积自然性**（`Hyp46.cupFp_coeffMap_eq_cup`）：`cupFp` 沿 `coeffMap` 就是
`GaloBase.cup`。 -/
theorem cE_cup (x y : TauCeti.cohomFp p (AbsoluteGaloisGroup K) 1) :
    (GaloTrivialFp.cohomEquiv K p 2) (TauCeti.cupFp p (AbsoluteGaloisGroup K) x y)
      = GaloBase.cup (K := K) (p := p) ((GaloTrivialFp.cohomEquiv K p 1) x)
          ((GaloTrivialFp.cohomEquiv K p 1) y) :=
  GaloCupTransport.cupFp_coeffMap_eq_cup K p x y

/-! ### 第二层：沿群同构 `absoluteGaloisGroupRestrictEquiv` 的上同调等价 -/

/-- **群载体**：`TauCeti.cohomFpLinearEquiv` 的逆，把 `G^Tc` 上的上同调送到 `G^m` 上。 -/
noncomputable def gE (d : ℕ) :
    TauCeti.cohomFp p (AbsoluteGaloisGroup K) d ≃+
      TauCeti.cohomFp p (Field.absoluteGaloisGroup K) d :=
  (TauCeti.cohomFpLinearEquiv p (absoluteGaloisGroupRestrictEquiv K) d).symm.toAddEquiv

/-- `gE` 是沿 `absoluteGaloisGroupRestrictEquiv` 的 `cohomFpMap`。 -/
theorem gE_apply (d : ℕ) (x : TauCeti.cohomFp p (AbsoluteGaloisGroup K) d) :
    gE (p := p) (K := K) d x
      = TauCeti.cohomFpMap p (ContinuousMonoidHom.toContinuousMonoidHom
          (absoluteGaloisGroupRestrictEquiv K)) d x :=
  TauCeti.cohomFpLinearEquiv_symm_apply p (absoluteGaloisGroupRestrictEquiv K) d x

/-- **第二层的杯积自然性**（`TauCeti.cupFp_map`）：群同构保持杯积。 -/
theorem gE_cup (x y : TauCeti.cohomFp p (AbsoluteGaloisGroup K) 1) :
    gE (p := p) (K := K) 2 (TauCeti.cupFp p (AbsoluteGaloisGroup K) x y)
      = TauCeti.cupFp p (Field.absoluteGaloisGroup K)
          (gE (p := p) (K := K) 1 x) (gE (p := p) (K := K) 1 y) := by
  rw [gE_apply, gE_apply, gE_apply]
  exact TauCeti.cupFp_map p (AbsoluteGaloisGroup K)
    (ContinuousMonoidHom.toContinuousMonoidHom (absoluteGaloisGroupRestrictEquiv K)) x y

/-! ### 第三层：`muNRep p K ≅ trivialFp p G^m`（TauCeti 现成） -/

/-- **系数载体**：平凡 `ℤ/p` 系数与 `μ_p` 系数的上同调等价
（`TauCeti.ClassFieldTheory.muNRepCohomologyEquivTrivialFp` 的逆）。 -/
noncomputable def mE (hζ : IsPrimitiveRoot ζ p) (d : ℕ) :
    TauCeti.cohomFp p (Field.absoluteGaloisGroup K) d ≃+
      ↑(continuousCohomology d (ClassFieldTheory.muNRep p K)).toModuleCat :=
  (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ d).symm.toAddEquiv

/-- **第三层的杯积自然性**：`cupFp` 沿 `mE` 就是 `kummerCupPairing` 的杯积
（`muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup`）。 -/
theorem mE_cup (hζ : IsPrimitiveRoot ζ p)
    (a b : TauCeti.cohomFp p (Field.absoluteGaloisGroup K) 1) :
    mE (p := p) (K := K) hζ 2 (TauCeti.cupFp p (Field.absoluteGaloisGroup K) a b)
      = (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
          (mE (p := p) (K := K) hζ 1 a) (mE (p := p) (K := K) hζ 1 b) := by
  have key := ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup
    (n := p) (F := K) ζ hζ
    (x := mE (p := p) (K := K) hζ 1 a) (y := mE (p := p) (K := K) hζ 1 b)
  have h1 : (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ 1)
      (mE (p := p) (K := K) hζ 1 a) = a := by
    simp only [mE, LinearEquiv.coe_toAddEquiv]
    exact LinearEquiv.apply_symm_apply _ a
  have h2 : (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ 1)
      (mE (p := p) (K := K) hζ 1 b) = b := by
    simp only [mE, LinearEquiv.coe_toAddEquiv]
    exact LinearEquiv.apply_symm_apply _ b
  rw [h1, h2] at key
  simp only [mE, LinearEquiv.coe_toAddEquiv]
  exact (LinearEquiv.symm_apply_eq _).mpr key.symm

/-! ### 载体链与 `Br F` -/

/-- **`H²` 载体链**：`GaloBase.H2 K p →+ H²(G^m, μ_p)`。 -/
noncomputable def redEquiv (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.H2 K p ≃+
      ↑(continuousCohomology 2 (ClassFieldTheory.muNRep p K)).toModuleCat :=
  ((GaloTrivialFp.cohomEquiv K p 2).symm.trans (gE (p := p) (K := K) 2)).trans
    (mE (p := p) (K := K) hζ 2)

/-- `H¹` 上同一套载体链（杯积的两个因子住在这里）。 -/
noncomputable def redEquiv1 (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.V K p ≃+
      ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p K)).toModuleCat :=
  ((GaloTrivialFp.cohomEquiv K p 1).symm.trans (gE (p := p) (K := K) 1)).trans
    (mE (p := p) (K := K) hζ 1)

/-- **`Br F` 层**：`ind` 的定义域（`GaloBase.H2 K p →+ Br K`）。 -/
noncomputable def brOfH2 (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.H2 K p →+ ClassFieldTheory.Br K :=
  (ClassFieldTheory.h2MuToBr p K).comp (redEquiv (p := p) (K := K) hζ).toAddMonoidHom

/-- `brOfH2` 的展开式。 -/
theorem brOfH2_apply (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.H2 K p) :
    brOfH2 (p := p) (K := K) hζ x
      = ClassFieldTheory.h2MuToBr p K (redEquiv (p := p) (K := K) hζ x) :=
  rfl

/-! ### 主定理：杯积相容 -/

/-- **载体链保持杯积**：`GaloBase.cup` 沿三层等价就是 `kummerCupPairing` 的杯积。

三层的自然性分别是 `GaloCupTransport.cupFp_coeffMap_eq_cup`（`Hyp46`）、
`TauCeti.cupFp_map`（群同构）、
`TauCeti.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup`（系数同构）。 -/
theorem redEquiv_cup (hζ : IsPrimitiveRoot ζ p) (A B : GaloBase.V K p) :
    redEquiv (p := p) (K := K) hζ (GaloBase.cup (K := K) (p := p) A B)
      = (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
          (redEquiv1 (p := p) (K := K) hζ A) (redEquiv1 (p := p) (K := K) hζ B) := by
  have h1 : (GaloTrivialFp.cohomEquiv K p 2).symm (GaloBase.cup (K := K) (p := p) A B)
      = TauCeti.cupFp p (AbsoluteGaloisGroup K)
          ((GaloTrivialFp.cohomEquiv K p 1).symm A)
          ((GaloTrivialFp.cohomEquiv K p 1).symm B) := by
    have h := cE_cup (p := p) (K := K)
      ((GaloTrivialFp.cohomEquiv K p 1).symm A)
      ((GaloTrivialFp.cohomEquiv K p 1).symm B)
    have hA : (GaloTrivialFp.cohomEquiv K p 1) ((GaloTrivialFp.cohomEquiv K p 1).symm A) = A :=
      (GaloTrivialFp.cohomEquiv K p 1).apply_symm_apply A
    have hB : (GaloTrivialFp.cohomEquiv K p 1) ((GaloTrivialFp.cohomEquiv K p 1).symm B) = B :=
      (GaloTrivialFp.cohomEquiv K p 1).apply_symm_apply B
    rw [hA, hB] at h
    exact (AddEquiv.symm_apply_eq (GaloTrivialFp.cohomEquiv K p 2)).mpr h.symm
  simp only [redEquiv, redEquiv1, AddEquiv.trans_apply]
  rw [h1, gE_cup (p := p) (K := K), mE_cup (p := p) (K := K) hζ]

/-- **杯积的 `Br F` 形式**：`A ∪ B` 的 Brauer 类是 `h2MuToBr` 作用在
`kummerCupPairing` 的杯积上。 -/
theorem brOfH2_cup (hζ : IsPrimitiveRoot ζ p) (A B : GaloBase.V K p) :
    brOfH2 (p := p) (K := K) hζ (GaloBase.cup (K := K) (p := p) A B)
      = ClassFieldTheory.h2MuToBr p K
          ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
            (redEquiv1 (p := p) (K := K) hζ A)
            (redEquiv1 (p := p) (K := K) hζ B)) := by
  rw [brOfH2_apply, redEquiv_cup (p := p) (K := K) hζ A B]

/-- **单射性**：`p` 在 `K` 中可逆时 `brOfH2` 单射（`h2MuToBr_injective` ＋ 三层都是等价）。 -/
theorem brOfH2_injective (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : K)) :
    Function.Injective (brOfH2 (p := p) (K := K) hζ) := by
  intro x y hxy
  have h1 : redEquiv (p := p) (K := K) hζ x = redEquiv (p := p) (K := K) hζ y :=
    ClassFieldTheory.h2MuToBr_injective p K hp hxy
  exact (redEquiv (p := p) (K := K) hζ).injective h1

end H2Bridge

#print axioms H2Bridge.cohomEquiv_eq_coeffMap
#print axioms H2Bridge.cE_cup
#print axioms H2Bridge.gE_cup
#print axioms H2Bridge.mE_cup
#print axioms H2Bridge.redEquiv_cup
#print axioms H2Bridge.brOfH2_cup
#print axioms H2Bridge.brOfH2_injective
