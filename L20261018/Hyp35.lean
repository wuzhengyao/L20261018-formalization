import L20261018.Hyp29
import L20261018.Hyp19
import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars

/-!
# `(a)` at the paper's own `V`: the restriction kernel on `GaloBase.V F p`

`Hyp27` proves the kernel criterion for the explicit restriction map and `Hyp29` for the canonical
cohomology with coefficients `ZMod p`, but both live on `ofDiscreteModule ℤ G (ZMod p)` — the model
obtained from `GaloBase.muP F p` by forgetting scalars. The paper's `V`, and hence `A.lean`'s
`BiKummerData.V` (via `galoBiKummer`), is

`GaloBase.V F p = continuousCohomology 1 (GaloBase.muP F p)`

carrying the `ZMod p`-module structure that `GaloBase.cup` is bilinear over. `A.lemma_3_1_2`'s
hypothesis `LinearMap.ker res = B.U` is stated for a `res` on that space, so `Hyp29` had never been
attached to it.

The obstruction recorded in earlier rounds was that `res` and the scalar-restriction comparison do not
meet at the level of the two `ModuleCat` projections. That is not the case: TauCeti's

`TauCeti.ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom`

is precisely the naturality of `restrictScalarsIntIso` with respect to a simultaneous change of group
and coefficients, and `ContinuousCohomology.res` is such a change
(`res_def : res S X n = map (subgroupSubtype S) (id _) n`). Instantiating it gives the commuting
square `res_restrictScalarsIntEquiv_comm` below, and with it the transport of `Hyp29` to `GaloBase.V`.

## Main results

* `KummerV.res_restrictScalarsIntEquiv_comm`: restriction commutes with the scalar-restriction
  comparison at the level of elements.
* `KummerV.res_kummerClass_eq_zero_iff`: **`(a)` on `GaloBase.V F p`** — restriction to
  `E.fixingSubgroup` kills the Kummer class of `a` exactly when `a ∈ (Fˣ)^p ⊔ Δ`. This is the same
  statement as `Hyp29`, now on the carrier that `A.lean` uses, so it is available to
  `A.lemma_3_1_2`.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace KummerV

universe u

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Restriction commutes with the scalar-restriction comparison.** For `y` a class in the
`ℤ`-model of `X` (the underlying additive representation of `X`), restricting to `S ⊆ G` and then
re-inserting the scalars is the same as re-inserting them and then restricting.

The proof is TauCeti's `map_comp_restrictScalarsIntIso_hom_of_hom` at the group map
`subgroupSubtype S` and the identity coefficient map, read at the element `y`. -/
theorem res_restrictScalarsIntEquiv_comm (S : Subgroup G) (X : TopRep.{u} k G) (n : ℕ)
    (y : ↑(continuousCohomology n (TopRep.restrictScalarsInt.obj X)).toModuleCat) :
    restrictScalarsIntEquiv (TopRep.res S.subtype X) n
        ((ContinuousCohomology.res S (TopRep.restrictScalarsInt.obj X) n).hom y)
      = (ContinuousCohomology.res S X n).hom (restrictScalarsIntEquiv X n y) := by
  have h := TauCeti.ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom
    (ContinuousMonoidHom.subgroupSubtype S)
    (CategoryTheory.CategoryStruct.id (TopRep.res S.subtype X)) n
  have h2 := congrArg (fun (m : continuousCohomology n (TopRep.restrictScalarsInt.obj X) ⟶
      TopModuleCat.restrictScalarsInt.obj (continuousCohomology n (TopRep.res S.subtype X)))
      => m.hom y) h
  simp only [ContinuousCohomology.res_def] at h2 ⊢
  exact h2

/-! ### 把 `Hyp29` 搬到 `GaloBase.V`：第五层 -/

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`(a)` 在论文自己的 `V` 上。** 限制到 `E.fixingSubgroup` 杀死 `a` 的 Kummer 类
（在 `GaloBase.V F p = H¹(G_F, ZMod p)` 里）当且仅当 `a ∈ (Fˣ)^p ⊔ Δ`。

`KummerBridge.kummerClass` 按定义就是「`restrictScalarsIntEquiv` 作用在 ℤ-模型的类上」
（`KummerBridge.h1ToVEquiv`），故 `res_restrictScalarsIntEquiv_comm` 把限制搬到 ℤ-模型一侧，
再由 `Hyp29` 给出消失性判据。

**上一轮记为「不可 defeq ⟹ 无路」的那一步，其实只是 `rw` 的 motive 问题**：
`ContinuousCohomology.res S (TopRep.restrictScalarsInt.obj (GaloBase.muP F p)) n` 与
`ContinuousCohomology.res S (ofDiscreteModule ℤ G (ZMod p)) n` **按 `rfl` 相等**，
但 `rw` 对一个余定义域依赖该对象的项造不出 motive。改用 `exact`（defeq 检查）即通。 -/
theorem res_kummerClass_eq_zero_iff (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (a : Fˣ) :
    (ContinuousCohomology.res
        (IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
        (GaloBase.muP F p) 1).hom (KummerBridge.kummerClass F p hp a) = 0
      ↔ a ∈ (powMonoidHom p : Fˣ →* Fˣ).range ⊔ Δ := by
  set S : Subgroup (AbsoluteGaloisGroup F) :=
    (IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup with hS
  have hk : KummerBridge.kummerClass F p hp a
      = restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 1
          (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)
            ((KummerBridge.kummerH1Equiv F p hp) (kummerMap F p hp a).toAdd)) := (rfl)
  rw [hk]
  have hnat := (res_restrictScalarsIntEquiv_comm (k := ZMod p) S (GaloBase.muP F p) 1
    (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)
      ((KummerBridge.kummerH1Equiv F p hp) (kummerMap F p hp a).toAdd))).symm
  rw [hnat]
  exact (AddEquivClass.map_eq_zero_iff).trans
    (BKummer.res_explicitH1_kummerMap_eq_zero_iff hp Δ hroots a)

end KummerV
