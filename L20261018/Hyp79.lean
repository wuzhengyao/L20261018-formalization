import L20261018.Hyp78
/-!
# 3.2 的系数载体第一半：`μ_p ≅ ℤ/p`（模载体 ＋ 平凡作用）

`(3)(ii)` 在 `Br` 里已闭合（`Hyp77`）。要把 3.2(1)(2) 的 `ind : GaloBase.H2 K p → ℕ`
真正定义出来，需要把 `GaloBase.H2 K p = H²(G_K, muP)`（系数 `ZMod p`，平凡作用）
与 `h2MuToBr` 的定义域 `H²(G_K, muNRep p K)`（系数 `KummerCoeff K p`）接起来。
`Hyp78` 已解决**群载体**（`absoluteGaloisGroupRestrictEquiv` 无条件）；
本文件解决**系数载体**这一半：

* `KummerCoeff K p = Additive (rootsOfUnity p (Kˢ))`，而 `IsPrimitiveRoot.zmodEquivRootsOfUnity`
  给出 `ZMod p ≃+ Additive (rootsOfUnity p Kˢ)`——**这就是 `μ_p ≅ ℤ/p`**；
* 该同构下 `G`-作用是**平凡**的（`ζ_p ∈ K` 时，`TauCeti.smul_kummerCoeff_eq_self`）。

于是 `muP K p`（`ZMod p` 上的平凡表示）与 `muNRep p K`（`KummerCoeff` 上的表示，
`ζ_p ∈ K` 时平凡）**作为 `ZMod p`-模是同一个**，差一个载体同构。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace SymbolCupBridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}

section

variable [NeZero p]
  (hζ : IsPrimitiveRoot ζ p)

include hζ

/-- **系数载体：`μ_p ≅ ℤ/p`**（作为加法群）。

`KummerCoeff K p = Additive (rootsOfUnity p (Kˢ))`，而 `ζ` 在 `Kˢ` 中的像（本原 `p` 次单位根）
经 `IsPrimitiveRoot.zmodEquivRootsOfUnity` 给出 `ZMod p ≃+ Additive (rootsOfUnity p Kˢ)`；
取逆即得。这正是 `μ_p ≅ ℤ/p` 的机检形式。 -/
noncomputable def kummerCoeffEquivZMod :
    KummerCoeff K p ≃+ ZMod p :=
  ((hζ.map_of_injective (algebraMap K (SeparableClosure K)).injective).isUnit_unit
    (NeZero.ne p)).zmodEquivRootsOfUnity.symm

/-- **`ζ_p ∈ K` 时 `μ_p` 上的 `G_K`-作用是平凡的**（`TauCeti.smul_kummerCoeff_eq_self`）。 -/
theorem kummerCoeff_smul_eq_self (g : AbsoluteGaloisGroup K) (x : KummerCoeff K p) :
    g • x = x :=
  TauCeti.smul_kummerCoeff_eq_self (n := p) hζ g x

end

end SymbolCupBridge

#print axioms SymbolCupBridge.kummerCoeffEquivZMod
#print axioms SymbolCupBridge.kummerCoeff_smul_eq_self
