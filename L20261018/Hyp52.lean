import L20261018.Hyp51
import L20261018.Hyp33
/-!
# `(f)` 的 `hNrd`（A 档合成）：除代数的约化范数包含极大子域的域范数

本文件把三块已机检的件拼起来，得到论文 `(f)`（`lem:basic-inclusions`(1)）所依赖的
`hNrd`：`N_{L/K}(L^×) ⊆ Nrd_D(D^×)`。

拼装方式：

1. **`Hyp51.nonempty_algEquiv_of_mk_eq_crossedProductClass`**：由「`D` 与 `L/K` 上某交叉积
   同 Brauer 类 ＋ 同次数」给出**代数同构** `φ : D ≃ₐ CrossedProduct c`；
2. **`Hyp33.exists_nrdOfIso_eq_norm`**：沿 `φ` 搬运后，`L^×` 的每个域范数都是 `D` 中某个单位的
   约化范数（Gille–Szamuely Prop. 2.6.3 的机检形态）；
3. 组合即得 `hNrd`。

上游供给（R861 侦察）：`E` 分裂 `D` ⟹ 类相等（TauCeti
`exists_crossedProductClass_eq_of_isSplittingField`）；`E` 分裂 `D` 本身由 `Hyp49` 从
`(1a)`（`Hyp48`）得到。⟹ `(f)` 的 `hNrd` 在**纸面链条上已闭合**，只差把它接到
`A.lemma_3_3_1` 的具体对象（`cor` ＝ 余限制、`S` ＝ Suslin 子空间）上。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolHNrd

universe u

variable {K : Type u} [Field K]

open TauCeti

/-- **`(f)` 的 `hNrd`（逐元素版）**：若中心除代数 `D` 与 `L/K` 上某交叉积同 Brauer 类、
且 `finrank D = [L:K]²`，则 `L` 的每个单位 `y` 的域范数 `N_{L/K}(y)` 都是 `D` 中某个单位的
约化范数（`nrdOfIso` 是沿所取同构搬运的约化范数，`Hyp33` 证其与呈现选取无关）。 -/
theorem exists_nrdOfIso_eq_norm_of_mk_eq
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (c : TwoCocycle K L)
    {D : Type u} [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    (hmk : BrauerGroup.mk (CSA.of K D) = BrauerGroup.crossedProductClass c)
    (hdeg : Module.finrank K D = Module.finrank K L ^ 2) (y : Lˣ) :
    ∃ (φ : D ≃ₐ[K] CrossedProduct c) (v : Dˣ),
      CrossedProductNrd.nrdOfIso c φ (v : D)
        = algebraMap K L (Algebra.norm K (y : L)) := by
  obtain ⟨φ⟩ := SymbolWedderburn.nonempty_algEquiv_of_mk_eq_crossedProductClass (K := K) c hmk hdeg
  obtain ⟨v, hv⟩ := CrossedProductNrd.exists_nrdOfIso_eq_norm (K := K) c φ y
  exact ⟨φ, v, hv⟩

/-- **`(f)` 的 `hNrd`（集合版）**：`N_{L/K}(L^×)` 含于某个呈现下 `D` 的约化范数像。 -/
theorem norm_range_subset_nrd_range_of_mk_eq
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (c : TwoCocycle K L)
    {D : Type u} [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    (hmk : BrauerGroup.mk (CSA.of K D) = BrauerGroup.crossedProductClass c)
    (hdeg : Module.finrank K D = Module.finrank K L ^ 2) :
    ∃ φ : D ≃ₐ[K] CrossedProduct c,
      (Set.range fun y : Lˣ => algebraMap K L (Algebra.norm K (y : L)))
        ⊆ (Set.range fun v : Dˣ => CrossedProductNrd.nrdOfIso c φ (v : D)) := by
  obtain ⟨φ⟩ := SymbolWedderburn.nonempty_algEquiv_of_mk_eq_crossedProductClass (K := K) c hmk hdeg
  exact ⟨φ, CrossedProductNrd.norm_image_le_nrdOfIso_image (K := K) c φ⟩

end SymbolHNrd
