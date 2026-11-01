import Hyp542

/-!
# S45 R3：★★★★★ **(F1) 的方块** —— `δ_{Y'} ≫ Inf₂ = i_* ≫ Inf_{C,1} ≫ δ_A`（**无条件**）

## 这一步在 GS 的哪一句

GS `prop-residue-map-long-exact` 证明末句（`raw/GilleSzamuely2017.tex:9540–9542`，逐字）：

> The fact that the maps `H^{i}(G/H,A^{H})\to H^{i}(G,A)` are indeed the usual inflation maps
> follows from an easy compatibility between inflations and boundary maps in long exact
> sequences, which readers may check for themselves.

该「easy compatibility」的**机检形态**就是下面 `delta_coind_comp_infl`：

```
δ_{Y'} ≫ Inf₂  =  i_* ≫ Inf_{C,1} ≫ δ_A
```

（`Y' = 0 → A^S → (Coind A)^S → T → 0`，`δ_{Y'} : H¹(G⧸S,T) → H²(G⧸S,A^S) = δ_T^{-1}`；
`i_* = map (id) iTame 1`；`δ_A = (coindBot_dimensionShift_two A).hom`。）

## 工具（**全部库内，零自建数学**）

| 用 | 件 | 位置 |
|---|---|---|
| **跨群** `δ` 自然性 | **`TauCeti.groupCohomology.δ_naturality`** | `scratch/tauceti-port/TauCeti/.../GroupCohomology/LongExactSequence.lean:113` |
| `map` 的复合律（**方向已实测**：`map f φ ≫ map g ψ`） | **`groupCohomology.map_comp`** | mathlib `GroupCohomology/Functoriality.lean:161` |
| `(id).comp f = f` | `MonoidHom.id_comp` | 库内 |
| `Φ` 的 `τ₁/τ₂/τ₃` 形状 | 照抄 `TauCeti` 的 `mono_HInfRes_f_and_exact` | `port/.../InflationRestriction.lean:105–110` |

## 机检内容

| 声明 | 内容 |
|---|---|
| `f1Sq` | ★★★ `Φ' : Y'.map (res (mk' S)) ⟶ XG`（三个分量 ＋ 两个交换性） |
| `delta_dimShiftUpSES_eq` | `δ_{XG} = (coindBot_dimensionShift_two A).hom`（`rfl`） |
| `f1Sq_τ₁_eq` | `map (mk' S) τ₁ 2 = Inf₂`（`rfl`，即 `HInfRes` 的定义） |
| `f1Sq_τ₃_eq` | ★★ `map (mk' S) τ₃ 1 = i_* ≫ Inf_{C,1}`（`map_comp`，GS 的「次序」在此定死） |
| **`delta_coind_comp_infl`** | ★★★★★ **(F1)**：`δ_{Y'} ≫ Inf₂ = i_* ≫ Inf_{C,1} ≫ δ_A` |

## 诚实边界

* 本件**不**含 `(d)`（`∂₂ ∘ Inf = 0`）：还差两件 —— `iTame ≫ deltaZeroBar = 0`（把 `Hyp541` 的
  `ModuleCat` 层等式抬到 `Rep` 层）与 `Mono δ_{Y'}`。
* 本件**不**用 `h2`（`H²(S,A) = 0`）：(F1) 是**无条件**的（与 GS 一致）。
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

/-- ★★★ **(F1) 的方块**：`Φ' : Y'.map (res (mk' S)) ⟶ XG`，`XG = 0 → A → Coind A → C → 0`。

三个分量就是 `C^S ↪ C` 那一族 `quotientToInvariants_lift`；`τ₃` 多一层 `resMap iTame`
（`iTame : T = coker(A^S ↪ (Coind A)^S) ⟶ C^S`，`Hyp542`）。 -/
noncomputable def f1Sq :
    (cokerSES A S).map (Rep.resFunctor (QuotientGroup.mk' S)) ⟶
      A.dimensionShiftUpSES where
  τ₁ := Rep.ofHom ((A.dimensionShiftUpSES.X₁).ρ.quotientToInvariants_lift S)
  τ₂ := Rep.ofHom ((A.dimensionShiftUpSES.X₂).ρ.quotientToInvariants_lift S)
  τ₃ := (Rep.resFunctor (QuotientGroup.mk' S)).map (iTame A S)
    ≫ Rep.ofHom ((A.dimensionShiftUpSES.X₃).ρ.quotientToInvariants_lift S)
  comm₁₂ := by ext; rfl
  comm₂₃ := by
    have hπ : (Rep.resFunctor (QuotientGroup.mk' S)).map (cokernel.π (qSES A S).f)
        ≫ (Rep.resFunctor (QuotientGroup.mk' S)).map (iTame A S)
        = (Rep.resFunctor (QuotientGroup.mk' S)).map (qSES A S).g := by
      rw [← Functor.map_comp, cokernelπ_comp_iTame]
    rw [ShortComplex.map_g, ← Category.assoc, hπ]
    ext z
    rfl

/-- `δ_{XG}` 就是 GS (6.15) 的 `H¹(G,C) ≅ H²(G,A)` 那个同构的 `.hom`。 -/
theorem delta_dimShiftUpSES_eq :
    groupCohomology.δ (Rep.dimensionShiftUpSES_shortExact A) 1 2 rfl
      = (coindBot_dimensionShift_two A).hom := (rfl)

/-- `map (mk' S) τ₁ 2` **就是** `Inf₂`（`HInfRes` 的定义）。 -/
theorem f1Sq_τ₁_eq :
    groupCohomology.map (QuotientGroup.mk' S) (f1Sq A S).τ₁ 2
      = (groupCohomology.HInfRes A.dimensionShiftUpSES.X₁ S 2).f := (rfl)

/-- ★★ `map (mk' S) τ₃ 1 = i_* ≫ Inf_{C,1}` —— GS「inflation 与 boundary 相容」的**次序定死**处。

由 `map_comp`（`f := id (G⧸S)`、`g := mk' S`、`φ := iTame`、`ψ := C^S ↪ C`）即得。 -/
theorem f1Sq_τ₃_eq :
    groupCohomology.map (QuotientGroup.mk' S) (f1Sq A S).τ₃ 1
      = groupCohomology.map (MonoidHom.id (G ⧸ S)) (iTame A S) 1
        ≫ (groupCohomology.HInfRes A.dimensionShiftUpSES.X₃ S 1).f := by
  have hcomp := groupCohomology.map_comp (f := MonoidHom.id (G ⧸ S))
    (g := QuotientGroup.mk' S) (A := tameImage A S)
    (B := (qSES A S).X₃) (C := A.dimensionShiftUpSES.X₃)
    (φ := iTame A S)
    (ψ := Rep.ofHom ((A.dimensionShiftUpSES.X₃).ρ.quotientToInvariants_lift S)) 1
  have hmap : groupCohomology.map
        ((MonoidHom.id (G ⧸ S)).comp (QuotientGroup.mk' S)) (f1Sq A S).τ₃ 1
      = groupCohomology.map (QuotientGroup.mk' S) (f1Sq A S).τ₃ 1 :=
    groupCohomology.map_congr
      (f := (MonoidHom.id (G ⧸ S)).comp (QuotientGroup.mk' S))
      (g := QuotientGroup.mk' S) (A := tameImage A S) (B := A.dimensionShiftUpSES.X₃)
      (φ := (f1Sq A S).τ₃) (ψ := (f1Sq A S).τ₃)
      (MonoidHom.id_comp (QuotientGroup.mk' S)) rfl 1
  rw [← hmap]
  exact hcomp

/-- ★★★★★ **(F1)**：`δ_{Y'} ≫ Inf₂ = i_* ≫ Inf_{C,1} ≫ δ_A`（**无条件**，不用 `H²(S,A) = 0`）；
证明 = `δ_naturality (mk' S) hY' hXG Φ' 1 2 rfl` ＋ `map_comp`（见 `f1Sq_τ₃_eq`）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:prop-residue-map-long-exact quote="follows from an easy compatibility between inflations and boundary maps in long exact"
theorem delta_coind_comp_infl :
    groupCohomology.δ (cokerSES_shortExact A S) 1 2 rfl
      ≫ (groupCohomology.HInfRes A.dimensionShiftUpSES.X₁ S 2).f
      = groupCohomology.map (MonoidHom.id (G ⧸ S)) (iTame A S) 1
        ≫ (groupCohomology.HInfRes A.dimensionShiftUpSES.X₃ S 1).f
        ≫ (coindBot_dimensionShift_two A).hom := by
  have h := TauCeti.groupCohomology.δ_naturality (QuotientGroup.mk' S)
    (cokerSES_shortExact A S) (Rep.dimensionShiftUpSES_shortExact A) (f1Sq A S) 1 2 rfl
  rw [f1Sq_τ₃_eq A S] at h
  rw [f1Sq_τ₁_eq A S] at h
  rw [delta_dimShiftUpSES_eq A] at h
  rw [Category.assoc] at h
  exact h

end L20261018

#print axioms L20261018.delta_dimShiftUpSES_eq
#print axioms L20261018.f1Sq_τ₁_eq
#print axioms L20261018.f1Sq_τ₃_eq
#print axioms L20261018.delta_coind_comp_infl
