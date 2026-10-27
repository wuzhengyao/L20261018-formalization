import L20261018.Hyp37
import TauCeti.Algebra.CrossedProduct.BrauerClass
import TauCeti.Algebra.BrauerGroup.Group

/-!
# 缺口 1 的第四层：退化扩张上的交叉积类是**平凡类**

`Hyp34` 在 `H²(Gal(L/K), Lˣ)` 层证了「第一槽是 `p` 次幂 ⟹ 循环代数类消失」，
`Hyp37` 在域论层证了「`a ∈ (K^×)^p` ⟹ `K(a^{1/p}) = K`」。本文件补上 **Brauer 群层**：

> 若 `Aut_K(L)` 平凡（等价地 `L = K`），则**任意** `2`-余环 `c : TwoCocycle K L` 的交叉积
> 都是平凡 Brauer 类，`crossedProductClass c = 1`。

## 为什么这条**不需要 carry 余环的构造**

这是本文件最要紧的一点。符号代数按 GS 的循环代数定义是
`(a,b)_K = (K(a^{1/p})/K, σ, b)`，其中载着 `b` 的是一个**具体的 carry 余环**。
但「第一槽是 `p` 次幂 ⟹ 分裂」这条特例**对余环毫无要求**：

`a ∈ (K^×)^p` 时 `K(a^{1/p}) = K`（`Hyp37`），而**任何** `2`-余环在平凡扩张上的交叉积都
是 `K` 自己（`finrank = [L:K]² = 1`，且 `algebraMap` 双射），故类平凡。

⟹ `(f)` 所依赖的那一半**不需要**构造 carry 余环；缺口 1 的残余因此只剩
「呈现定义 `F⟨x,y⟩/(x^p−a, y^p−b, yx−ζ_p xy)` 与循环交叉积的认同」
（GS2017 `cor-cyclic-special-presentations`），那是**记号翻译**，不是新的数学。

## 主结果

* `CrossedProductDeg.crossedProductClass_eq_one_of_subsingleton_aut`：`Aut_K(L)` 平凡 ⟹ 类为 1。
* `CrossedProductDeg.crossedProductClass_eq_one_of_eq_bot`：`L = ⊥` ⟹ 类为 1。
* `CrossedProductDeg.crossedProductClass_rootSet_eq_one`：**`a ∈ (K^×)^p` ⟹
  `K(a^{1/p})` 上的任意交叉积类是 1**。
-/

open TauCeti

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CrossedProductDeg

universe u

variable {K : Type u} [Field K]

/-- **`Aut_K(L)` 平凡 ⟹ 交叉积类是平凡类。** 此时 `[L:K] = 1`，故
`finrank K (CrossedProduct c) = [L:K] · |Aut| = 1`；秩 `1` 的 `K`-代数由 `algebraMap` 的张成，
其双射性给出 `CrossedProduct c ≃ₐ[K] K`，于是 `mk` 相同而 `mk K = 1`。 -/
theorem crossedProductClass_eq_one_of_subsingleton_aut
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton (L ≃ₐ[K] L)] (c : TwoCocycle K L) :
    BrauerGroup.crossedProductClass c = 1 := by
  -- `Aut_K(L)` 单点，故 `[L : K] = 1`
  haveI : Unique (L ≃ₐ[K] L) :=
    { default := AlgEquiv.refl
      uniq := fun e => Subsingleton.elim e AlgEquiv.refl }
  have hcard : Nat.card (L ≃ₐ[K] L) = 1 := Nat.card_unique
  have hL : Module.finrank K L = 1 := by
    rw [← IsGalois.card_aut_eq_finrank, hcard]
  -- 故交叉积的维数是 `1`
  have hA : Module.finrank K (CrossedProduct c) = 1 := by
    rw [CrossedProduct.finrank_eq_finrank_mul_card, hL, hcard, mul_one]
  -- 秩 `1` ⟹ `algebraMap` 双射 ⟹ 与 `K` 同构
  have hbij : Function.Bijective (algebraMap K (CrossedProduct c)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hA
  have e : CrossedProduct c ≃ₐ[K] K :=
    (AlgEquiv.ofBijective (Algebra.ofId K (CrossedProduct c)) hbij).symm
  rw [BrauerGroup.crossedProductClass_def, ← BrauerGroup.mk_base]
  exact BrauerGroup.mk_eq_mk_of_algEquiv e

/-- `Aut_K(⊥)` 平凡：`⊥ ≅ K` 作为 `K`-代数，其自同构必为恒等。 -/
instance subsingleton_algEquiv_bot :
    Subsingleton (↥(⊥ : IntermediateField K (SeparableClosure K)) ≃ₐ[K]
      ↥(⊥ : IntermediateField K (SeparableClosure K))) where
  allEq e f := by
    refine AlgEquiv.ext (fun x => ?_)
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp x.2
    have hx : x = algebraMap K ↥(⊥ : IntermediateField K (SeparableClosure K)) k :=
      Subtype.ext (by simpa using hk.symm)
    rw [hx]
    simp

/-- **`L = ⊥`（即 `L = K`）⟹ 交叉积类是平凡类。** -/
theorem crossedProductClass_eq_one_of_eq_bot
    (L : IntermediateField K (SeparableClosure K)) (hL : L = ⊥)
    [FiniteDimensional K ↥L] [IsGalois K ↥L]
    (c : TwoCocycle K ↥L) :
    BrauerGroup.crossedProductClass c = 1 := by
  subst hL
  exact crossedProductClass_eq_one_of_subsingleton_aut c

/-- **缺口 1 的分裂性那一半，完全一般地成立**：若 `a ∈ (K^×)^p`，则 `K(a^{1/p})` 上的
**任意** `2`-余环的交叉积都是平凡 Brauer 类。

不需要 carry 余环的具体构造——退化扩张上的一切余环都给出平凡类。 -/
theorem crossedProductClass_rootSet_eq_one {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    [HasEnoughRootsOfUnity K p] {a : Kˣ} (ha : ∃ α : Kˣ, α ^ p = a)
    [FiniteDimensional K ↥(IntermediateField.adjoin K
      {x : SeparableClosure K | x ^ p = algebraMap K (SeparableClosure K) (a : K)})]
    [IsGalois K ↥(IntermediateField.adjoin K
      {x : SeparableClosure K | x ^ p = algebraMap K (SeparableClosure K) (a : K)})]
    (c : TwoCocycle K ↥(IntermediateField.adjoin K
      {x : SeparableClosure K | x ^ p = algebraMap K (SeparableClosure K) (a : K)})) :
    BrauerGroup.crossedProductClass c = 1 :=
  crossedProductClass_eq_one_of_eq_bot _
    (SymbolAlg.adjoin_rootSet_eq_bot_of_isPow (K := K) (p := p) ha) c

end CrossedProductDeg
