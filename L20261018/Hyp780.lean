import L20261018.Hyp779

/-!
# S74 R6：**`∂¹(π)` 是 `H¹(I,ℤ/p)` 的生成元** —— GS `∂¹((−π)) = 1` 的战役形态

## 位置（路线 A，即 GS 6.8.4 的复位路线）

GS `prop-specialization-section` 的证明只有两步：
1. 投影公式 `∂^{p+q}(a ∪ Inf b) = ∂^p(a) ∪ b`（`lemma-residue-cup-product`，印版 6.8.4）；
2. **`∂¹((−π)) = 1`** —— 原文一句：*"because `∂_v^1` becomes the mod `m` valuation map via the
   Kummer isomorphism and `−π` has valuation 1"*。

**本件 = 第 2 步在战役里的形态**：`H¹(I,ℤ/p)` 是一维 `ℤ/p`-空间（`Hyp759.natCard_h1Inertia_eq`），
故"`∂¹((π))` 非零"（`Hyp775.res1V_kummerClass_ne_zero_of_uniformizer`）就直接推出
**它是生成元**（`Hyp761.zmultiples_eq_top_of_natCard_prime`）。

⟹ 于是**没有任何"归一化常数"要算**：`e_{x₀}`（`x₀ := ∂¹((π))`）就是"`x₀ ↦ 1`"那个
`H¹(I,ℤ/p) ≅ ℤ/p`，而 GS 的 `∂¹((−π)) = 1` 只是把 `x₀` 换成 `−x₀`（`e_{−x₀}(x₀) = −1`，
`Hyp775.h1InertiaAddEquiv_neg_self`）。

## 交付

| 声明 | 内容 |
|---|---|
| **`res1V_kummerClass_zmultiples_eq_top`** | ★★★★★ **`∂¹((π))` 生成 `H¹(I,ℤ/p)`** |
| **`res1V_kummerClass_spec`** | ★★★★★ **`∂¹((π))` 完整刻画**：共轭不变**且**生成 `H¹(I,ℤ/p)` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★★★ **`∂¹((π))` 生成 `H¹(I,ℤ/p)`**（`π` 一致化元）。

`H¹(I,ℤ/p)` 的基数是素数 `p`（`Hyp759.natCard_h1Inertia_eq`），故任一非零元即生成元
（`Hyp761.zmultiples_eq_top_of_natCard_prime`）；非零性由 `Hyp775` 给出（`p ∤ v(π) = 1`）。 -/
theorem res1V_kummerClass_zmultiples_eq_top (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) :
    AddSubgroup.zmultiples (res1V (F := F) (p := p)
      (KummerBridge.kummerClass F p hp π)) = ⊤ :=
  zmultiples_eq_top_of_natCard_prime p _
    (res1V_kummerClass_ne_zero_of_uniformizer (F := F) (p := p) hp hpq' hπ)
    (natCard_h1Inertia_eq (F := F) (p := p) (q := q) hpq ζ hζ hgen)

/-! ## 2 `∂¹((π))` 的两个性质打包（GS `∂¹` 落点的完整刻画） -/

/-- ★★★★★ **`∂¹((π))` 完整刻画**：它**共轭不变**（即落在 `H⁰(Γ⧸I, H¹(I,ℤ/p))`）**且生成**
`H¹(I,ℤ/p)`。这两条合起来就是 GS `prop-specialization-section` 里 `∂¹((−π)) = 1` 的全部内容
（"成为 mod `p` 赋值映射"＝共轭不变；"`(−π)` 赋值 `1`"＝生成）。 -/
theorem res1V_kummerClass_spec (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) :
    res1V (F := F) (p := p) (KummerBridge.kummerClass F p hp π)
        ∈ H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
      ∧ AddSubgroup.zmultiples (res1V (F := F) (p := p)
          (KummerBridge.kummerClass F p hp π)) = ⊤ :=
  ⟨res1V_mem_H1ConjInvariants (F := F) (p := p) _,
    res1V_kummerClass_zmultiples_eq_top (F := F) (p := p) (q := q) hpq ζ hζ hgen hp hpq' hπ⟩

end L20261018

#print axioms L20261018.res1V_kummerClass_zmultiples_eq_top
#print axioms L20261018.res1V_kummerClass_spec
