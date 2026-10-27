import L20261018.Hyp52
import TauCeti.FieldTheory.GaloisCohomology.Kummer

/-!
# `(f)` 的 A 档（Kummer 形式）：余限制的像 ＝ 约化范数的 Kummer 类

`(f)` = `lem:basic-inclusions`(1)：`N ⊆ S`，其中
`N = cor_{E/F}H¹(E,μ_p)`、`S = Nrd(D^×)F^{×p}/F^{×p}`（在 Kummer 同构
`F^×/F^{×p} ≅ H¹(F,μ_p)` 下）。

本文件把两半拼起来：

1. **`cor` 的翻译**（TauCeti `kummerCor_kummerMap`）：
   `cor_{E/F}(kummer_E y) = kummer_F(N_{E/F} y)`；
2. **`hNrd`**（`Hyp52`，由 `Hyp51` 的交叉积呈现 ＋ `Hyp33` 得到）：
   `N_{E/F}(y)` 是 `D` 中某单位的约化范数。

⟹ **(f) 的内容**：余限制像里的每个元素都是「某个约化范数的 Kummer 类」。

**仍缺的接口（已精确定界）**：论文的 `S` 是 `F^×` 里的子集，而本战役的 `nrd`/`nrdOfIso`
按定义是 **`E`-值**的（`LinearMap.det (mulRight c a)`，见 `Hyp21`）。`nrdOfIso` 的取值落在
`algebraMap F E` 的像里（即「约化范数其实是 `F`-值的」）这一事实**尚无引理**——它才是把上句
的 Kummer 形式改写为 `S` 的集合包含所缺的唯一一块。`Hyp33.nrd_inc` 只覆盖
`x = inc(y)` 这一支。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolKummer

universe u

variable {F : Type u} [Field F] {E : Type u} [Field E] [Algebra F E]
  [FiniteDimensional F E] {p : ℕ} (hn : IsUnit (p : E))
  (σ : E →ₐ[F] SeparableClosure F)

open TauCeti

/-- **`(f)` 的 `cor` 翻译**：`cor_{E/F}(kummer_E y) = kummer_F(N_{E/F}(y))`
（TauCeti `kummerCor_kummerMap`，本战役写法）。 -/
theorem kummerCor_kummerMap_eq (y : Eˣ) :
    kummerCor F p E σ (kummerMap E p hn y)
      = kummerMap F p (isUnit_natCast_of_isUnit_natCast (algebraMap F E) hn)
          (Algebra.normUnits F y) :=
  TauCeti.kummerCor_kummerMap F p E σ hn y

/-- **`(f)` 的 A 档（Kummer 形式）**：对 `Eˣ` 的每个 `y`，余限制 `cor_{E/F}` 的像
`cor(kummer_E y)` 是 `F` 的一个单位 `z` 的 Kummer 类，而 `z`（经 `algebraMap F E`）正是
`D` 中某单位的约化范数。

即：**`N` 的每个元素都是某个约化范数的 Kummer 类** —— `(f)` 的数学内容。 -/
theorem exists_kummerCor_eq_kummerMap_of_nrd
    (c : TwoCocycle F E) {D : Type u} [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D]
    (φ : D ≃ₐ[F] CrossedProduct c)
    (hNrd : ∀ y : Eˣ, ∃ v : Dˣ,
      CrossedProductNrd.nrdOfIso c φ (v : D)
        = algebraMap F E (Algebra.norm F (y : E)))
    (y : Eˣ) :
    ∃ z : Fˣ,
      kummerCor F p E σ (kummerMap E p hn y)
          = kummerMap F p (isUnit_natCast_of_isUnit_natCast (algebraMap F E) hn) z
        ∧ ∃ v : Dˣ, CrossedProductNrd.nrdOfIso c φ (v : D) = algebraMap F E (z : F) := by
  refine ⟨Algebra.normUnits F y, kummerCor_kummerMap_eq (p := p) hn σ y, ?_⟩
  obtain ⟨v, hv⟩ := hNrd y
  exact ⟨v, hv⟩

/-- **`(f)` 的 A 档（集合形式）**：`Hyp52` 的 `hNrd` 给出「域范数 ⊆ 约化范数」，
再经 `cor` 翻译即得「余限制像 ⊆ 约化范数的 Kummer 类」。 -/
theorem range_kummerCor_subset_of_mk_eq
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (c : TwoCocycle F L)
    {D : Type u} [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D]
    (hmk : BrauerGroup.mk (CSA.of F D) = BrauerGroup.crossedProductClass c)
    (hdeg : Module.finrank F D = Module.finrank F L ^ 2) :
    ∃ φ : D ≃ₐ[F] CrossedProduct c,
      (Set.range fun y : Lˣ => algebraMap F L (Algebra.norm F (y : L)))
        ⊆ (Set.range fun v : Dˣ => CrossedProductNrd.nrdOfIso c φ (v : D)) :=
  SymbolHNrd.norm_range_subset_nrd_range_of_mk_eq (K := F) c hmk hdeg

/-! ### `(f)` 的论文形式：`N ⊆ S` -/

/-- **`(f)` 的 A 档（论文形式）**：`N ⊆ S`。

* `N = cor_{E/F} H¹(E,μ_p)`（余限制的像）；
* `S` = 那些 `Fˣ` 元素 `z` 的 Kummer 类，其中 `algebraMap F E z` 是 `D` 中某单位的约化范数
  （即论文的 `S = Nrd(D^×)F^{×p}/F^{×p}`，在工作模型下的形态）。

证明：任取 `w = cor u`；由 `kummerMap` 满射 `u = kummer_E y`；`cor(kummer_E y) = kummer_F(N_{E/F}y)`
（`kummerCor_kummerMap`），而 `N_{E/F}(y)` 是某单位的约化范数（`hNrd`）。 -/
theorem range_kummerCor_subset_of_nrd
    (c : TwoCocycle F E) {D : Type u} [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D]
    (φ : D ≃ₐ[F] CrossedProduct c)
    (hNrd : ∀ y : Eˣ, ∃ v : Dˣ,
      CrossedProductNrd.nrdOfIso c φ (v : D)
        = algebraMap F E (Algebra.norm F (y : E))) :
    ∀ w ∈ Set.range (fun w : Multiplicative
        (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup E) (KummerCoeff E p)) =>
        kummerCor F p E σ w),
      ∃ z : Fˣ, w = kummerMap F p (isUnit_natCast_of_isUnit_natCast (algebraMap F E) hn) z
        ∧ ∃ v : Dˣ, CrossedProductNrd.nrdOfIso c φ (v : D) = algebraMap F E (z : F) := by
  rintro w ⟨u, rfl⟩
  obtain ⟨y, rfl⟩ := kummerMap_surjective (K := E) (n := p) hn u
  refine ⟨Algebra.normUnits F y, kummerCor_kummerMap_eq (p := p) hn σ y, ?_⟩
  obtain ⟨v, hv⟩ := hNrd y
  exact ⟨v, hv⟩

/-- **`(f)` 的 A 档收口**：由论文自己的假设（`D` 与某交叉积同 Brauer 类 ＋ 同次数）直接得到
`N ⊆ S`。

这是 `(f)`（`lem:basic-inclusions`(1)）在**交叉积工作模型**下的完整形式：
上游的「`E` 分裂 `D`」由 `Hyp48`／`Hyp49` 提供，TauCeti 把它变成类相等；本定理把类相等
升成同构（`Hyp51`）并给出 `hNrd`（`Hyp52`），再经 `cor` 的 Kummer 翻译（TauCeti）得到包含。 -/
-- @source file=raw/L20261018.tex locator=label:lem:basic-inclusions quote="复合范数像满足 $N\subseteq S$；"
theorem lemma_3_3_1_galo [IsGalois F E]
    (c : TwoCocycle F E) {D : Type u} [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D]
    (hmk : BrauerGroup.mk (CSA.of F D) = BrauerGroup.crossedProductClass c)
    (hdeg : Module.finrank F D = Module.finrank F E ^ 2) :
    ∃ φ : D ≃ₐ[F] CrossedProduct c,
      ∀ w ∈ Set.range (fun w : Multiplicative
          (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup E) (KummerCoeff E p)) =>
          kummerCor F p E σ w),
        ∃ z : Fˣ, w = kummerMap F p (isUnit_natCast_of_isUnit_natCast (algebraMap F E) hn) z
          ∧ ∃ v : Dˣ, CrossedProductNrd.nrdOfIso c φ (v : D) = algebraMap F E (z : F) := by
  obtain ⟨φ, hsub⟩ := range_kummerCor_subset_of_mk_eq (F := F) (L := E) c hmk hdeg
  refine ⟨φ, range_kummerCor_subset_of_nrd (p := p) hn σ c φ (fun y => ?_)⟩
  obtain ⟨v, hv⟩ := hsub ⟨y, rfl⟩
  exact ⟨v, hv⟩

end SymbolKummer
