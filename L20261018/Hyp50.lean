import L20261018.Hyp49
import TauCeti.Algebra.CrossedProduct.Splitting.Class

/-!
# Brauer 层的两个接口（`(2)` 的剩余基建，第一段）

## 侦察更正（本轮最重要的发现）

`STATUS.md`／`HANDOFF.md`／`wiki/hyp-symbol-cup.md` 此前把
「`E` 分裂 `D` ⟹ `D` 有交叉积呈现（GS2017 Prop 4.5.8 ＋ Wedderburn）」记在**具名假设**里。
**这是错的**：TauCeti 早已机检了它的**类层面**版本——

```lean
TauCeti.BrauerGroup.exists_crossedProductClass_eq_of_isSplittingField
    (h : TauCeti.Algebra.IsSplittingField K A L) (L/K 有限 Galois) :
    ∃ c : TwoCocycle K L, crossedProductClass c = mk (CSA.of K A)
```

（`TauCeti/Algebra/CrossedProduct/Splitting/Class.lean`；配套 `crossedProductClass_cocycleOfSplitting`。）
所以「分裂 ⟹ 某个交叉积的类」**不是外部输入**；真正还缺的是**代数层面的同构**
`D ≃ₐ CrossedProduct c`（类相等 ＋ 同次数 ⟹ 同构，需要 Wedderburn 的唯一性，
TauCeti 的 `BrauerGroup/Division.lean` 只给了**除代数之间**的版本）。

## 本文件给的两块接口

1. **CSA 结构沿 `K`-代数同构搬运**（`isCentral_of_algEquiv`、`isSimpleRing_of_algEquiv`）：
   `IsCentral` 用中心子代数、`IsSimpleRing` 用 mathlib 的
   `RingEquiv.mapTwoSidedIdeal : TwoSidedIdeal R ≃o TwoSidedIdeal S`。这是任何「对商代数
   （如 `SymbolAlg`）谈 Brauer 类」的必备胶水。
2. **`mk_matrix_eq_one`**：全矩阵代数的 Brauer 类是 `1`（TauCeti `mk_matrix` ＋ `mk_base`）。
   与 `Hyp49.IsSplit` 合起来即「分裂 ⟹ 类平凡」在**代数确实同构于矩阵代数**时的形态。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolBrauer

universe u

variable {K : Type u} [Field K]

/-! ### CSA 结构沿代数同构的搬运 -/

/-- **中心性沿 `K`-代数同构搬运**（`⊥` 是 `algebraMap` 的像，见 `Algebra.mem_bot`）。 -/
theorem isCentral_of_algEquiv {A B : Type u} [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [Algebra.IsCentral K A] (e : A ≃ₐ[K] B) : Algebra.IsCentral K B := by
  refine ⟨fun b hb => ?_⟩
  rw [Subalgebra.mem_center_iff] at hb
  have hmem : e.symm b ∈ Subalgebra.center K A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    calc a * e.symm b = e.symm (e a) * e.symm b := by rw [e.symm_apply_apply]
      _ = e.symm (e a * b) := (map_mul _ _ _).symm
      _ = e.symm (b * e a) := by rw [hb (e a)]
      _ = e.symm b * e.symm (e a) := map_mul _ _ _
      _ = e.symm b * a := by rw [e.symm_apply_apply]
  have hbot : e.symm b ∈ (⊥ : Subalgebra K A) := Algebra.IsCentral.out hmem
  rw [Algebra.mem_bot] at hbot
  obtain ⟨r, hr⟩ := hbot
  rw [Algebra.mem_bot]
  exact ⟨r, by rw [← e.apply_symm_apply b, ← hr, AlgEquiv.commutes]⟩

/-- **单性沿 `K`-代数同构搬运**（`RingEquiv.mapTwoSidedIdeal` 是**序同构**，
`OrderIso.isSimpleOrder` 沿它搬运 `IsSimpleOrder`）。 -/
theorem isSimpleRing_of_algEquiv {A B : Type u} [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [IsSimpleRing A] (e : A ≃ₐ[K] B) : IsSimpleRing B :=
  IsSimpleRing.mk (OrderIso.isSimpleOrder (RingEquiv.mapTwoSidedIdeal e.toRingEquiv).symm)

/-! ### 全矩阵代数的 Brauer 类是 `1` -/

/-- **`M_n(K)` 的 Brauer 类是 `1`**（TauCeti `mk_matrix` ＋ `mk_base`）。 -/
theorem mk_matrix_eq_one (n : ℕ) [NeZero n] :
    TauCeti.BrauerGroup.mk (TauCeti.CSA.of K (Matrix (Fin n) (Fin n) K)) = 1 := by
  have h : TauCeti.BrauerGroup.mk (TauCeti.CSA.of K (Matrix (Fin n) (Fin n) K))
      = TauCeti.BrauerGroup.mk (TauCeti.CSA.matrix (TauCeti.CSA.base K) n) := rfl
  rw [h, TauCeti.BrauerGroup.mk_matrix, TauCeti.BrauerGroup.mk_base]

end SymbolBrauer
