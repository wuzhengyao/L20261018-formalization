import Hyp480
import Hyp379

/-!
# S40 R21：**动作 A 的前两步** —— `∂₂` 的 `H²(G,ℤ)` 形式（`knrResidueMapInt`）

## 本轮做什么（`S40-REMAINING-PLAN.md` 的动作 A，第一段）

造 `d : H²(G,μ_p) → VKG ⊆ H¹(G,ℤ/p)` 的路线是

```
H²(G,μ_p) --kummerResidueMap--> H¹(G,ℚ/ℤ) --ratOverZDimShift⁻¹--> H²(G,ℤ)
          --(integralBockstein 的逆，限于 p-挠)--> H¹(G,ℤ/p) ⊇ VKG
```

本轮把**前两段**机检成一条定义：

```lean
knrResidueMapInt : H²(G, KummerCoeff F p) → H²(G, ULift ℤ)
```

`H²(G,ℤ)` 形式的 `∂₂`。

## 侦察结论（本轮）

* `TauCeti.integralBocksteinShortExact (n) : 0 → ℤ --n--> ℤ → ZMod n → 0` ✓（`Integral.lean:73`）
* **`TauCeti.integralBockstein (n) (i) : H^i(G,ZMod n) ⟶ H^{i+1}(G,ULift ℤ)`** ✓（`Integral.lean:142`）
* **`TauCeti.integralBockstein_one_injective (n) : Function.Injective (integralBockstein G n 1)`** ✓（`:153`）
* **⚠ 但库内 __没有__ `integralBockstein_one_range`（像 = `n`-挠）** —— 第三段因此**还缺一条 range 引理**
  （`Integral.lean:203` 只用到单射性）。

⟹ **动作 A 的第三段 = 自建 `integralBockstein` 的 range 引理**（估 1 轮）。
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

variable (F : Type) [Field F]

/-- ★★★★★ **`∂₂` 的 `H²(G,ℤ)` 形式**：
`H²(G, μ_p) --kummerResidueMap--> H¹(G,ℚ/ℤ) ≅ H²(G,ℤ)`。

这是动作 A 的**前两段**（`S40-REMAINING-PLAN.md` §3 A）。 -/
noncomputable def knrResidueMapInt (p : ℕ) [NeZero p] :
    continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
        (KummerCoeff F p)) →
      continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
        (ULift.{0} ℤ)) :=
  (intH2AddEquivH1RatOverZ (F := F)).symm.toFun ∘ kummerResidueMap (K := F) p 0

/-- `knrResidueMapInt` 的定义式（供下游展开核查）。 -/
theorem knrResidueMapInt_apply (p : ℕ) [NeZero p]
    (x : continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ
      (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))) :
    knrResidueMapInt F p x =
      (intH2AddEquivH1RatOverZ (F := F)).symm (kummerResidueMap (K := F) p 0 x) := rfl

end L20261018

#print axioms L20261018.knrResidueMapInt
#print axioms L20261018.knrResidueMapInt_apply
