import L20261018.Hyp83
import L20261018.Hyp82
/-!
# 线性性 ＋ `brauerOfH2 (c • (A ∪ B))` 的显式形式（R899）

R899 的装配需要一件事：`redEquiv`（`Hyp81`）目前只是 `AddEquiv`，而 `hind` 的目标是
`∀ x ∈ span {h}, ind x ≤ p`，即 `x = c • h` ⟹ 必须把 `c •` 推过 `redEquiv`。
三个分量（`cohomEquiv`／`cohomFpLinearEquiv`／`muNRepCohomologyEquivTrivialFp`）**本来都是线性的**，
只是 `Hyp81` 把它们打包成了 `AddEquiv`。本文件给出线性版并证明二者在函数层相同（`rfl`），
于是 `map_smul` 免费用。

## 主结果

* `cEL`／`redLin`／`redLin1`：三层链的 `ZMod p`-线性版。
* `redEquiv_map_smul`／`redEquiv1_map_smul`：**`redEquiv` 尊重纯量乘**。
* **`brOfH2_smul_cup`**：`brOfH2 (c • (A ∪ B)) = h2MuToBr (cup (c • X) Y)`——`hind` 装配的第一块。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace H2Bridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}

/-! ### 第一层的线性版（`Hyp45` 的 `cohomEquiv` 本来自 `ContinuousLinearEquiv`） -/

/-- **第一层（线性版）**：`trivialFp p G^Tc ≅ muP` 诱导的上同调线性等价。 -/
noncomputable def cEL (d : ℕ) :
    ↑(TauCeti.cohomFp p (AbsoluteGaloisGroup K) d).toModuleCat ≃ₗ[ZMod p]
      ↑(continuousCohomology d (GaloBase.muP K p)).toModuleCat :=
  ((TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod p)
    (AbsoluteGaloisGroup K) d).mapIso (GaloTrivialFp.iso K p)).toContinuousLinearEquiv.toLinearEquiv

/-- `cEL` 与 `Hyp45` 的 `AddEquiv` 版是**同一个函数**。 -/
theorem cEL_toAddEquiv (d : ℕ) :
    (cEL (p := p) (K := K) d).toAddEquiv = GaloTrivialFp.cohomEquiv K p d :=
  rfl

/-! ### `H²`／`H¹` 链的线性版 -/

/-- **`H²` 载体链（线性版）**：`GaloBase.H2 K p ≃ₗ H²(muNRep p K)`。 -/
noncomputable def redLin (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.H2 K p ≃ₗ[ZMod p]
      ↑(continuousCohomology 2 (ClassFieldTheory.muNRep p K)).toModuleCat :=
  ((cEL (p := p) (K := K) 2).symm.trans
      (TauCeti.cohomFpLinearEquiv p (absoluteGaloisGroupRestrictEquiv K) 2).symm).trans
    (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ 2).symm

/-- **`H¹` 载体链（线性版）**。 -/
noncomputable def redLin1 (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.V K p ≃ₗ[ZMod p]
      ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p K)).toModuleCat :=
  ((cEL (p := p) (K := K) 1).symm.trans
      (TauCeti.cohomFpLinearEquiv p (absoluteGaloisGroupRestrictEquiv K) 1).symm).trans
    (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ 1).symm

/-- `redLin` 在函数层等于 `Hyp81.redEquiv`。 -/
theorem redLin_eq (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.H2 K p) :
    redLin (p := p) (K := K) hζ x = redEquiv (p := p) (K := K) hζ x :=
  rfl

/-- `redLin1` 在函数层等于 `Hyp81.redEquiv1`。 -/
theorem redLin1_eq (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.V K p) :
    redLin1 (p := p) (K := K) hζ x = redEquiv1 (p := p) (K := K) hζ x :=
  rfl

/-- **`redEquiv` 尊重纯量乘**（线性性；`hind` 把 `c •` 推过载体链时用）。 -/
theorem redEquiv_map_smul (hζ : IsPrimitiveRoot ζ p) (c : ZMod p) (x : GaloBase.H2 K p) :
    redEquiv (p := p) (K := K) hζ (c • x) = c • redEquiv (p := p) (K := K) hζ x := by
  rw [← redLin_eq (p := p) (K := K) hζ, ← redLin_eq (p := p) (K := K) hζ]
  exact (redLin (p := p) (K := K) hζ).map_smul c x

/-- **`redEquiv1` 尊重纯量乘**。 -/
theorem redEquiv1_map_smul (hζ : IsPrimitiveRoot ζ p) (c : ZMod p) (x : GaloBase.V K p) :
    redEquiv1 (p := p) (K := K) hζ (c • x) = c • redEquiv1 (p := p) (K := K) hζ x := by
  rw [← redLin1_eq (p := p) (K := K) hζ, ← redLin1_eq (p := p) (K := K) hζ]
  exact (redLin1 (p := p) (K := K) hζ).map_smul c x

/-! ### 主结果：`brOfH2 (c • (A ∪ B))` 的显式形式 -/

/-- **`hind` 装配的第一块**：`c • (A ∪ B)` 的 `Br` 类 = `h2MuToBr` 作用在
`kummerCupPairing` 的杯积 `(c • X) ∪ Y` 上（`X = redEquiv1 A`、`Y = redEquiv1 B`）。

`c •` 进第一槽用的是 `kummerCupPairing` 的杯积对第一槽的线性（`LinearMap.map_smul`）。 -/
theorem brOfH2_smul_cup (hζ : IsPrimitiveRoot ζ p) (c : ZMod p) (A B : GaloBase.V K p) :
    brOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) A B)
      = ClassFieldTheory.h2MuToBr p K
          ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
            (c • redEquiv1 (p := p) (K := K) hζ A) (redEquiv1 (p := p) (K := K) hζ B)) := by
  rw [brOfH2_apply, redEquiv_map_smul, redEquiv_cup (p := p) (K := K) hζ A B]
  congr 1
  show c • (((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (redEquiv1 (p := p) (K := K) hζ A)) (redEquiv1 (p := p) (K := K) hζ B)
      = ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (c • redEquiv1 (p := p) (K := K) hζ A) (redEquiv1 (p := p) (K := K) hζ B)
  rw [LinearMap.map_smul, LinearMap.smul_apply]

/-- **`Br` 层的版本**：`brauerOfH2 (c • (A ∪ B))` 的 `Br` 类同样是 `(c • X) ∪ Y` 的像。 -/
theorem brauerOfH2_smul_cup (hζ : IsPrimitiveRoot ζ p) (c : ZMod p)
    (A B : GaloBase.V K p) :
    ClassFieldTheory.brauerGroupEquivBr K
        (Additive.ofMul (brauerOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) A B)))
      = ClassFieldTheory.h2MuToBr p K
          ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
            (c • redEquiv1 (p := p) (K := K) hζ A) (redEquiv1 (p := p) (K := K) hζ B)) := by
  show ClassFieldTheory.brauerGroupEquivBr K
      ((ClassFieldTheory.brauerGroupEquivBr K).symm
        (brOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) A B))) = _
  rw [AddEquiv.apply_symm_apply]
  exact brOfH2_smul_cup (p := p) (K := K) hζ c A B

end H2Bridge

#print axioms H2Bridge.cEL_toAddEquiv
#print axioms H2Bridge.redEquiv_map_smul
#print axioms H2Bridge.redEquiv1_map_smul
#print axioms H2Bridge.brOfH2_smul_cup
#print axioms H2Bridge.brauerOfH2_smul_cup
