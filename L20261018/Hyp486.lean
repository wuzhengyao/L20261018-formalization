import Hyp485

/-!
# S40 R28：动作 A4b 第一步 —— **`GaloBase.H2` 到 `H²(ℤ, μ_p)` 的一条 `AddEquiv`**

把 R18 的四段桥（`Hyp478`）打包：

```
GaloBase.H2 F p = H²(GaloBase.muP)
  ≅ H²(muPReal)                          -- Hyp388.muH2Equiv（反向）
  ≅ H²(muKummerCoeff)                    -- Hyp478.kummerCoeffMuRealCohomologyIso（反向）
  ≅ H²(ofDiscreteModule ℤ G (KummerCoeff F p))   -- TauCeti.restrictScalarsIntEquiv（反向）
```

⟹ `kummerH2Bridge : GaloBase.H2 F p ≃+ H²(ℤ, KummerCoeff F p)`。
这是 A4b 的**第一段**（把 `d` 的定义域运到 `knrResidueMapInt` 的定义域）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`kummerH2Bridge`** | ★★★★★ **`GaloBase.H2 F p ≃+ H²(ℤ, KummerCoeff F p)`** |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **`GaloBase.H2 F p ≃+ H²(G, μ_p)`**（`ℤ`-系数；R18 四段桥的打包）。

方向：`GaloBase.H2 → H²(GaloBase.muP) → H²(muPReal) → H²(muKummerCoeff) → H²(ℤ, KummerCoeff)`。 -/
noncomputable def kummerH2Bridge (hp : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.H2 F p ≃+
      ↑(continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat :=
  (muH2Equiv F hζ).toContinuousLinearEquiv.toAddEquiv.symm.trans
    ((kummerCoeffMuRealCohomologyIso F p hp hζ 2).toContinuousLinearEquiv.toAddEquiv.symm.trans
      (ContCohomology.restrictScalarsIntEquiv (muKummerCoeff F p) 2).symm)

end L20261018

#print axioms L20261018.kummerH2Bridge
