import L20261018.Hyp471

/-!
# S40 R11：Kummer 系数 `μ_p ≅ KummerCoeff K p` **打到 `K_nr^×`** 的系数映射

## 这一件在关键路径上的位置

目标 ③ 要 `residueSpan ⊆ ker r_v`，其中 `r_v = knrResidueMap'` 定义在
`H²(G, K_nr^×)`（`Hyp470`）上，而 `residueSpan` 由 **Kummer 类** `(u)∪(w)` 生成（`u,w` 单位）。
故需要一条**系数映射**

```
KummerCoeff K p = Additive (rootsOfUnity p (SepCl K))  ──→  KnrUnits' K = Additive (↥K_nr)ˣ
```

**与 `TauCeti.kummerCoeffToUnits` 的区别（关键）**：那一件的目标是 `UnitsCoeff K = (SepCl K)^×`
（**整个** `SepCl K` 的单位），**不落在 `K_nr` 里**；本件证明 Kummer 系数的像**落在 `K_nr` 里**
（因 `p` 次单位根是 `K` 上代数的 ⟹ 落在某个有限 `K'` 里 ⟹ 落在 `K'((π))` 的常系数部分）。

⟹ 这是把 Kummer 桥**降到正确载体 `K_nr` 上**的一步（`Hyp470` 的同一范畴内，无范畴桥接风险）。

## 本件不声称什么

* 不声称 `μ_p ≅ 平凡 Z/p`（W4，需 `μ_p ⊂ K` 才成立）；
* 不声称系数映射的 `G`-等变性（下一轮，用 `Hyp468.knrMap` 的系数作用）；
* 不声称 cup 积相容（W8）。

## 机检件

| 声明 | 内容 |
|---|---|
| `kummerSeries_mem_Knr` | ★★★★ `single 0 ζ ∈ K_nr`（`ζ` 为 `p` 次单位根） |
| `kummerUnitOn` | ★★★★ `ζ` 作为 `K_nr^×` 的单位 |
| **`kummerCoeffToKnrUnits`** | ★★★★★ **`KummerCoeff K p →+ KnrUnits' K`** |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-- `p` 次单位根在 `K` 上整（`ζ^p = 1`）。 -/
theorem rootsOfUnity_isIntegral (p : ℕ) [NeZero p] (ζ : rootsOfUnity p (SeparableClosure K)) :
    IsIntegral K ((((ζ : (SeparableClosure K)ˣ)) : SeparableClosure K)) := by
  have hζ : (((ζ : (SeparableClosure K)ˣ)) : SeparableClosure K) ^ p = 1 := by
    have := (mem_rootsOfUnity p (ζ : (SeparableClosure K)ˣ)).mp ζ.2
    simpa using congrArg (fun u : (SeparableClosure K)ˣ => ((u : SeparableClosure K)))
      this
  refine ⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C (1 : K) (NeZero.ne p), ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one, hζ, sub_self]

/-- ★★★★ **`p` 次单位根（作为常系数级数）落在 `K_nr` 里**。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8152 quote="maximal unramified extension of $K$, i.e. the composite of all finite unramified"
theorem kummerSeries_mem_Knr (p : ℕ) [NeZero p] (ζ : rootsOfUnity p (SeparableClosure K)) :
    (HahnSeries.single 0 (((ζ : (SeparableClosure K)ˣ)) : SeparableClosure K) :
      LaurentSeries (SeparableClosure K)) ∈ KnrSubfield K := by
  set ζ' : SeparableClosure K := (((ζ : (SeparableClosure K)ˣ)) : SeparableClosure K) with hζ'
  have hint : IsIntegral K ζ' := rootsOfUnity_isIntegral p ζ
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K {ζ'}) :=
    IntermediateField.adjoin.finiteDimensional hint
  rw [mem_KnrSubfield]
  refine ⟨⟨IntermediateField.adjoin K {ζ'}, inferInstance⟩, ⟨
    (HahnSeries.single 0 (⟨ζ', IntermediateField.subset_adjoin K {ζ'} (Set.mem_singleton ζ')⟩ :
      ↥(IntermediateField.adjoin K {ζ'})) : LaurentSeries ↥(IntermediateField.adjoin K {ζ'})),
    ?_⟩⟩
  show HahnSeries.map (HahnSeries.single 0 (⟨ζ', _⟩ : ↥(IntermediateField.adjoin K {ζ'})))
      (algebraMap ↥(IntermediateField.adjoin K {ζ'}) (SeparableClosure K))
    = HahnSeries.single 0 ζ'
  ext n
  rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  rcases eq_or_ne n 0 with h | h
  · subst h; simp
  · simp [h]

/-- ★★★★ **`p` 次单位根作为 `K_nr^×` 的单位**。 -/
noncomputable def kummerUnitOn (p : ℕ) [NeZero p] (ζ : rootsOfUnity p (SeparableClosure K)) :
    (↥(KnrSubfield K))ˣ :=
  Units.mk0 ⟨HahnSeries.single 0 (((ζ : (SeparableClosure K)ˣ)) : SeparableClosure K),
    kummerSeries_mem_Knr p ζ⟩ (by
    intro h
    have h' : (HahnSeries.single 0 (((ζ : (SeparableClosure K)ˣ)) : SeparableClosure K) :
      LaurentSeries (SeparableClosure K)) = 0 := congrArg Subtype.val h
    have hc := congrArg (fun x : LaurentSeries (SeparableClosure K) => x.coeff 0) h'
    rw [HahnSeries.coeff_single, if_pos rfl] at hc
    exact Units.ne_zero (ζ : (SeparableClosure K)ˣ) hc)

theorem kummerUnitOn_coe (p : ℕ) [NeZero p] (ζ : rootsOfUnity p (SeparableClosure K)) :
    ((kummerUnitOn (K := K) p ζ : (↥(KnrSubfield K))ˣ) : ↥(KnrSubfield K)) =
      ⟨HahnSeries.single 0 (((ζ : (SeparableClosure K)ˣ)) : SeparableClosure K),
        kummerSeries_mem_Knr p ζ⟩ := rfl

/-- ★★★★★ **Kummer 系数打到 `K_nr^×`**：`KummerCoeff K p →+ K_nr^×`（加性形态）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8160 quote="Denoting by $U_{nr}$ the multiplicative group of units in $K_{nr}$, we get an"
noncomputable def kummerCoeffToKnrUnits (p : ℕ) [NeZero p] :
    KummerCoeff K p →+ KnrUnits' K where
  toFun x := Additive.ofMul (kummerUnitOn (K := K) p (Additive.toMul x))
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    show (HahnSeries.single 0 ((↑((1 : rootsOfUnity p (SeparableClosure K)) :
      (SeparableClosure K)ˣ) : SeparableClosure K)) : LaurentSeries (SeparableClosure K))
      = (HahnSeries.single 0 ((1 : (SeparableClosure K)ˣ) : SeparableClosure K) :
        LaurentSeries (SeparableClosure K))
    congr 1
  map_add' x y := by
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    show (HahnSeries.single 0 ((↑(Additive.toMul (x + y)) : (SeparableClosure K)ˣ) :
        SeparableClosure K) : LaurentSeries (SeparableClosure K))
      = (HahnSeries.single 0 ((↑(Additive.toMul x) : (SeparableClosure K)ˣ) :
          SeparableClosure K) : LaurentSeries (SeparableClosure K))
        * (HahnSeries.single 0 ((↑(Additive.toMul y) : (SeparableClosure K)ˣ) :
          SeparableClosure K) : LaurentSeries (SeparableClosure K))
    rw [HahnSeries.single_mul_single]
    congr 2

end L20261018

#print axioms L20261018.kummerUnitOn
#print axioms L20261018.kummerCoeffToKnrUnits
