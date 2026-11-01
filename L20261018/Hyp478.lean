import L20261018.Hyp477

/-!
# S40 R18：★ **桥链闭合** —— `KummerCoeff F p ≅ μ_p(F)` 系数同构 ＋ `H^i` 层同构

## 本轮补的那条（`RECON-R3` §95.2 的唯一剩余缺口）

`muPReal` 用 `Additive (rootsOfUnity p F)`（**`F` 内**的根）；`kummerResidueMap` 用
`KummerCoeff F p = Additive (rootsOfUnity p (SepCl F))`（**`F^s` 内**的）。
按 R17 的新纪律先做了内容式 grep（本仓无现成件），**但两条现成件的复合即得**：

```
KummerCoeff F p  ≃ₗ[ZMod p]  ZMod p  ≃ₗ[ZMod p]  Additive (rootsOfUnity p F)
   [Hyp19.KummerBridge.kummerCoeffLinearEquiv]   [Hyp382.muLinearEquiv]
```

⟹ 不需要任何 `rootsOfUnity` 层的双射。

## 桥链的最终形状（全部件都在库）

```
H^i(ℤ, KummerCoeff F p)
  ≅ H^i(ZMod p, KummerCoeff F p)          -- TauCeti.restrictScalarsIntEquiv
  ≅ H^i(ZMod p, Additive (rootsOfUnity p F)) = H^i(muPReal)   -- 本件 ★
  ≅ H^i(ZMod p, ZMod p) = H^i(GaloBase.muP)                   -- Hyp382.muCohomologyIso
```

## 机检件

| 声明 | 内容 |
|---|---|
| **`kummerCoeffMuRealEquiv`** | ★★★★ `KummerCoeff F p ≃ₗ[ZMod p] Additive (rootsOfUnity p F)` |
| **`muKummerCoeff`** | `ofDiscreteModule (ZMod p) G (KummerCoeff F p)` |
| **`kummerCoeffMuRealIso`** | ★★★★★ **`muKummerCoeff ≅ muPReal p F`**（`TopRep` 同构） |
| **`kummerCoeffMuRealCohomologyIso`** | ★★★★★ **`H^i(muKummerCoeff) ≅ H^i(muPReal)`** |
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

/-- ★★★★ **系数同构 `KummerCoeff F p ≅ μ_p(F)`**：两条现成件的复合。 -/
noncomputable def kummerCoeffMuRealEquiv (hp : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    KummerCoeff F p ≃ₗ[ZMod p] Additive (rootsOfUnity p F) :=
  (KummerBridge.kummerCoeffLinearEquiv F p hp).trans (muLinearEquiv p F hζ)

/-- `μ_p(F^s)`（`ZMod p` 层）作为系数对象。 -/
noncomputable def muKummerCoeff : TopRep (ZMod p) (TauCeti.AbsoluteGaloisGroup F) :=
  letI := kummerCoeffMort (K := F) p
  TauCeti.ofDiscreteModule (ZMod p) (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p)

/-- ★★★★★ **`μ_p(F^s) ≅ μ_p(F)`**（`TopRep` 层）。 -/
noncomputable def kummerCoeffMuRealIso (hp : IsUnit (p : F)) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) :
    muKummerCoeff F p ≅ muPReal p F :=
  letI := kummerCoeffMort (K := F) p
  TauCeti.ofDiscreteModuleIso (kummerCoeffMuRealEquiv F p hp hζ) (fun g m => by
    rw [kummerCoeff_smul_trivial (F := F) (p := p) hζ g m]
    rfl)

/-- ★★★★★ **`H^i` 层**：`H^i(G, μ_p(F^s)) ≅ H^i(G, μ_p(F))`。 -/
noncomputable def kummerCoeffMuRealCohomologyIso (hp : IsUnit (p : F)) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (i : ℕ) :
    continuousCohomology i (muKummerCoeff F p) ≅ continuousCohomology i (muPReal p F) :=
  CategoryTheory.Functor.mapIso
    (TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod p)
      (TauCeti.AbsoluteGaloisGroup F) i) (kummerCoeffMuRealIso F p hp hζ)

end L20261018

#print axioms L20261018.kummerCoeffMuRealEquiv
#print axioms L20261018.kummerCoeffMuRealIso
#print axioms L20261018.kummerCoeffMuRealCohomologyIso
