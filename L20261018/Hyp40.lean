import L20261018.Hyp10
import L20261018.Hyp29
/-!
# 3.3(2) 收口：`cor H¹(E, μ_p) ⊆ U^⊥`，在显式模型上**无条件**

论文 `lem:basic-inclusions` (2) 的证明是**投影公式 ＋ `res_E((a_i)) = 0`** 两行：

```
cor(α) ∪ (a_i) = cor(α ∪ res(a_i)) = cor(α ∪ 0) = 0
```

两块在此之前从未拼在一起，且各自都已机检：

* **投影公式**：`Hyp10.explicitCup_projection_res_right`
  （`explicitCor2 (cup_U w (res v)) = cup_G (cor w) v`）；
* **`res(a_i) = 0`**：`Hyp29.res_explicitH1_kummerMap_eq_zero_iff`（`a_i ∈ Δ` 时成立），
  经 `Hyp9.res_explicitH1`（`res (explicitH1 x) = explicitH1 (explicitRes1 x)`）
  与 `explicitH1` 是加法等价，落到**显式模型** `explicitRes1` 上。

本文件在同一个显式模型（`explicitCup11` / `explicitCor1` / `explicitCor2` / `explicitRes1`）里
把两者拼起来，得到 `A.lemma_3_3_2` 的结论 —— **`cor` 的像落在 `U^⊥` 里** —— 且**无额外假设**：
`hproj` 与 `resE a_i = 0` 都不再是参数。

### 与 `A.lemma_3_3_2` 的关系

`A.lemma_3_3_2` 是这条论证的**抽象版**（`hproj`、`resE a_i = 0` 作参数）。本文件给出**实例**，
两个参数在实例上被 `Hyp10` 与 `Hyp29` 消掉。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace GaloCup

universe u

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `ZMod p` 上的乘法配对，作为加法群双同态。 -/
def zmodMulPairing (p : ℕ) : ZMod p →+ ZMod p →+ ZMod p where
  toFun x :=
    { toFun := fun y => x * y
      map_zero' := mul_zero x
      map_add' := fun a b => by rw [mul_add] }
  map_zero' := by
    ext y
    simp
  map_add' := by
    intro a b
    ext y
    simp [add_mul]

/-- **`(a)` 的显式模型类**：`a ↦ (a)` 落在 `H¹(G_F, ZMod p)` 的显式模型里，即
`kummerH1Equiv (kummerMap a)`。 -/
noncomputable def kummerExplicit (hp : IsUnit (p : F)) (a : Fˣ) :
    H1 (AbsoluteGaloisGroup F) (ZMod p) :=
  (KummerBridge.kummerH1Equiv F p hp) (kummerMap F p hp a).toAdd

/-- **`a ∈ Δ` ⟹ 显式限制杀死 `(a)`。** 由 `Hyp29`（连续模型上的消失性判据）
经 `Hyp9`（限制与显式比较交换）落到显式模型。 -/
theorem explicitRes1_kummerExplicit_eq_zero (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    {a : Fˣ} (ha : a ∈ Δ) :
    explicitRes1 (AbsoluteGaloisGroup F) (ZMod p)
      ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup)
      (kummerExplicit (F := F) (p := p) hp a) = 0 := by
  have h29 := (BKummer.res_explicitH1_kummerMap_eq_zero_iff
    (F := F) (p := p) hp Δ hroots a).mpr (Subgroup.mem_sup_right ha)
  rw [res_explicitH1 (G := AbsoluteGaloisGroup F) (M := ZMod p)
    (IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup] at h29
  refine (explicitH1AddEquivContinuousCohomology
    (G := ↥((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup))
    (M := ZMod p)).injective ?_
  simp only [kummerExplicit, map_zero]
  exact h29

/-- **3.3(2)：`cor` 的像与 `(a_i)` 的杯积为零** —— 即 `cor H¹(E, μ_p) ⊆ U^⊥`。

`a_i ∈ Δ = ker(res_{E/F})`（由 `Hyp29`，见 `explicitRes1_kummerExplicit_eq_zero`），
故 `cor(α) ∪ (a_i) = cor(α ∪ res(a_i)) = cor(α ∪ 0) = 0`（投影公式，`Hyp10`）。 -/
-- @source file=raw/L20261018.tex locator=label:lem:basic-inclusions quote="复合范数像满足 $N\subseteq U^\perp$；"
theorem lemma_3_3_2_explicit (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup).FiniteIndex]
    (w : H1 ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup)
      (ZMod p)) :
    explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        (zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl)
        (explicitCor1 (AbsoluteGaloisGroup F) (ZMod p) _ hU w)
        (kummerExplicit (F := F) (p := p) hp a1) = 0 ∧
      explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        (zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl)
        (explicitCor1 (AbsoluteGaloisGroup F) (ZMod p) _ hU w)
        (kummerExplicit (F := F) (p := p) hp a2) = 0 := by
  have hres1 := explicitRes1_kummerExplicit_eq_zero (F := F) (p := p) hp Δ hroots ha1
  have hres2 := explicitRes1_kummerExplicit_eq_zero (F := F) (p := p) hp Δ hroots ha2
  constructor
  · rw [← explicitCup_projection_res_right (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
      _ hU (zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) w
      (kummerExplicit (F := F) (p := p) hp a1)]
    rw [hres1, map_zero, map_zero]
  · rw [← explicitCup_projection_res_right (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
      _ hU (zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) w
      (kummerExplicit (F := F) (p := p) hp a2)]
    rw [hres2, map_zero, map_zero]

end GaloCup
