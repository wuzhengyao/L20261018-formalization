import L20261018.Infra.Cohomology.ResidueLES.Step004_i_star_delta_zero_bar

/-!
# S45 R5：★★★★★ **(d) 完成** —— `∂₂ ∘ Inf = 0`（`Inf₂ ≫ deltaTwo_minimal = 0`）

## 数学内容

GS `prop-residue-map-long-exact` 的长正合列在 `H^{i}(G,A)` 处正合 ⟺ **`∂^{i} ∘ Inf = 0`**。
`∂₂ = deltaTwo_minimal`（`Hyp539`），`Inf₂ = (HInfRes A S 2).f`。展开：

```
∂₂ = Inf₂ ≫ δ_A⁻¹ ≫ Inf_{C,1}⁻¹ ≫ deltaZeroBar_*
```

其中 `δ_A = (coindBot_dimensionShift_two A).hom`（GS (6.15) 的边界映射）、
`Inf_{C,1} = (HInfRes (dimensionShiftUp A) S 1).f`。于是

```
δ_{Y'} ≫ (∂₂ ∘ Inf₂)
  = (δ_{Y'} ≫ Inf₂) ≫ δ_A⁻¹ ≫ Inf_{C,1}⁻¹ ≫ M
  = (i_* ≫ Inf_{C,1} ≫ δ_A) ≫ δ_A⁻¹ ≫ Inf_{C,1}⁻¹ ≫ M     -- (F1)，Hyp543
  = i_* ≫ M                                                 -- Iso 消去
  = map (id) (iTame ≫ deltaZeroBar) 1 = 0                    -- (F2)，Hyp544
⟹ ∂₂ ∘ Inf₂ = 0                                             -- Mono δ_{Y'}，Hyp544
```

## 机检内容

| 声明 | 内容 |
|---|---|
| `deltaTwo_firstHalf'_hom_eq` | 展开式（`Iso.trans`／`Iso.symm` 的 `.hom`） |
| `inflationIso_hom_eq` | `inflationIso = HInfRes C S 1` 的 `.f`（`asIso` 的 `.hom`） |
| `map_iTame_comp_map_deltaZeroBar` | ★★★ `i_* ≫ M = 0`（`map_comp` ＋ `Hyp544.iTame_comp_deltaZeroBar`） |
| **`deltaTwo_minimal_comp_inflation`** | ★★★★★ **(d)**：`Inf₂ ≫ deltaTwo_minimal = 0` |

## 诚实边界

* 本件只给 (d)。**(C) `tame_uu`（`kills`）仍缺**：还需 `TopPairing.cup_infl` 把 (d) 接到杯积上。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- `∂₂` 前半的展开式：`(deltaTwo_firstHalf'_of_h2 A h2).hom = δ_A⁻¹ ≫ Inf_{C,1}⁻¹`。 -/
theorem deltaTwo_firstHalf'_hom_eq
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    (deltaTwo_firstHalf'_of_h2 A h2).hom
      = (coindBot_dimensionShift_two A).inv
        ≫ (inflationIso_dimensionShiftUp_zero A h2).inv := (rfl)

/-- `inflationIso` 的 `.hom` 就是 `Inf_{C,1}`（`asIso` 的定义）。 -/
theorem inflationIso_hom_eq
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    (inflationIso_dimensionShiftUp_zero A h2).hom
      = (groupCohomology.HInfRes (Rep.dimensionShiftUp A) S 1).f := (rfl)

/-- ★★★ **`δ_{Y'}` 是满的**：`H²(G⧸S, (Coind A)^S) = 0` ⟹ `δ` 满。

（收口用的是 `Epi` 而非 `Mono`：`δ ≫ X = 0` 要能推出 `X = 0` 必须 `δ` 满。） -/
theorem epi_δ_cokerSES :
    Epi (groupCohomology.δ (cokerSES_shortExact A S) 1 2 rfl) :=
  groupCohomology.epi_δ_of_isZero (cokerSES_shortExact A S) 1
    (TauCeti.groupCohomology.isZero_quotientToInvariants_coindBot_succ S A.V 1)

/-- `Hyp543` 的 (F1) 重述成 `HInfRes A S 2`（原件的 `A.dimensionShiftUpSES.X₁` 与之 `rfl`）。 -/
theorem delta_coind_comp_infl' :
    groupCohomology.δ (cokerSES_shortExact A S) 1 2 rfl ≫ (groupCohomology.HInfRes A S 2).f
      = groupCohomology.map (MonoidHom.id (G ⧸ S)) (iTame A S) 1
        ≫ (groupCohomology.HInfRes (Rep.dimensionShiftUp A) S 1).f
        ≫ (coindBot_dimensionShift_two A).hom :=
  delta_coind_comp_infl A S

/-- ★★★ **`i_* ≫ M = 0`**：把 `iTame ≫ deltaZeroBar = 0`（`Hyp544`）过 `map (id) · 1`。

用 `map_comp`（`f = g = id`）＋ `(resFunctor id).map iTame = iTame` ＋ `map _ 0 = 0`。 -/
theorem map_iTame_comp_map_deltaZeroBar :
    groupCohomology.map (MonoidHom.id (G ⧸ S)) (iTame A S) 1
      ≫ groupCohomology.map (MonoidHom.id (G ⧸ S))
          (deltaZeroBar A S (innerConjTrivialIn_one A S)) 1 = 0 := by
  rw [← groupCohomology.map_comp (f := MonoidHom.id (G ⧸ S)) (g := MonoidHom.id (G ⧸ S))
    (A := tameImage A S) (B := (qSES A S).X₃)
    (C := h1RepQuot A S 1 (innerConjTrivialIn_one A S))
    (φ := iTame A S) (ψ := deltaZeroBar A S (innerConjTrivialIn_one A S)) 1]
  have hzero : (Rep.resFunctor (MonoidHom.id (G ⧸ S))).map (iTame A S)
      ≫ deltaZeroBar A S (innerConjTrivialIn_one A S) = 0 :=
    iTame_comp_deltaZeroBar A S
  rw [hzero]
  show HomologicalComplex.homologyMap _ 1 = 0
  rw [groupCohomology.cochainsMap_zero]
  exact HomologicalComplex.homologyMap_zero _ _ 1

/-- ★★★★★ **(d)**：`∂₂ ∘ Inf = 0` —— `Inf₂ ≫ deltaTwo_minimal = 0`。

GS `prop-residue-map-long-exact` 的长正合列在 `H^i(G,A)` 处正合；GS 原文（`:9542`）
「The fact that the maps `H^i(G/H,A^H) → H^i(G,A)` are indeed the usual inflation maps …」。 -/
theorem deltaTwo_minimal_comp_inflation
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    (groupCohomology.HInfRes A S 2).f ≫ deltaTwo_minimal A S h2 = 0 := by
  have hsuff : groupCohomology.δ (cokerSES_shortExact A S) 1 2 rfl
      ≫ ((groupCohomology.HInfRes A S 2).f ≫ deltaTwo_minimal A S h2) = 0 := by
    rw [← Category.assoc, delta_coind_comp_infl']
    rw [deltaTwo_minimal_eq A S h2, deltaTwo_firstHalf'_hom_eq A S h2]
    rw [← inflationIso_hom_eq A S h2]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact map_iTame_comp_map_deltaZeroBar A S
  haveI := epi_δ_cokerSES A S
  exact (cancel_epi (groupCohomology.δ (cokerSES_shortExact A S) 1 2 rfl)).mp
    (hsuff.trans (comp_zero (f := groupCohomology.δ (cokerSES_shortExact A S) 1 2 rfl)).symm)

end L20261018

#print axioms L20261018.deltaTwo_firstHalf'_hom_eq
#print axioms L20261018.inflationIso_hom_eq
#print axioms L20261018.epi_δ_cokerSES
#print axioms L20261018.map_iTame_comp_map_deltaZeroBar
#print axioms L20261018.deltaTwo_minimal_comp_inflation
