import L20261018.Infra.Cohomology.Conjugation.Step002_m_carrier_bridge_beta
import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

/-!
# S47 R4：★★★★★ **`M` 本体完成** —— `Cᴵ → H¹(I, μ_p)` 的 `Γ`-等变映射

`∂₂ := δ_Γ⁻¹ ≫ Inf_C⁻¹ ≫ M`（路线 A）的第三因子 `M` 在 GS 6.8.1 里是
`H^{i-1}(G/H, C^H) → H^{i-1}(G/H, H¹(H,A))` 的**系数层映射**，须是 `G/H`-模态射。
S47 R2/R3 把它的难点拆成三座载体桥；本件把**最后一座（α）**补上并**把 `M` 装出来**：

| 桥 | 件 | 状态 |
|---|---|---|
| 骨架（`δ` 的共轭等变） | `Hyp574.contDeltaZeroBar_conjNormal` | ✅ R2 |
| β（比较同构 `H1 ↔ continuousCohomology 1` 的共轭等变） | `Hyp575.contH1_iso_conjNormal` | ✅ R3 |
| **α（`Cᴵ ↔ H⁰(I,C)` 的共轭等变）** | `explicitH0Iso_conjNormalMap_zero` | ✅ **本件** |

```
contM : Cᴵ → H¹(I, μ_p)（显式离散载体 H1 ↥I (ZMod p)）
contM := H¹比较⁻¹ ∘ contDeltaZeroBar I ∘ H⁰比较
contM_smul : contM (g • x) = g • contM x            -- g : Γ（共轭作用）
```

**为什么 α 原来被当成难点**：`conjNormalMap V M g 0` 是 `map (conj) (pair) 0`，其在 `H⁰` 上的
作用没有现成引理。本件的解法 = 库内 `DegreeZero.lean:285 map_degreeZeroClass`
（`map` 在次数 0 对 `degreeZeroClass` 的作用）＋ 一个"`degreeZeroClass` 只依赖向量"的小引理
（其证明项依赖向量，故 `rw` 会因 dependent motive 失败）。

**⟹ `M` 的 `Γ`-等变性已机检**。余下（R5）：把两端的 `Γ`-作用下降到 `Γ⧸I`（γ），
即 `FixedPoints.addSubgroup` 的 `DistribMulAction (Γ⧸I)`（已有）与 `H1` 上的
`QuotientGroup.lift`（用 `Conjugation/Basic.lean:332 smul_eq_self_of_mem`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

/-! ## 一般形态：α 桥 -/

section General

variable {R : Type} [Ring R] [TopologicalSpace R]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : TopRep R G}

/-- `degreeZeroClass` 只依赖向量（不变性证明无关）：用来绕开 `rw` 的 dependent motive 失败。 -/
theorem degreeZeroClass_congr {u v : X.V} (h : u = v)
    (hu : ∀ g : G, (X.ρ g) u = u) (hv : ∀ g : G, (X.ρ g) v = v) :
    ContinuousCohomology.degreeZeroClass X u hu =
      ContinuousCohomology.degreeZeroClass X v hv := by
  subst h
  exact congrArg (ContinuousCohomology.zeroIso X).inv (Subtype.ext rfl)

variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
  (V : Subgroup G) [V.Normal]

/-- ★★★ **α（元素层）**：`conjNormalMap` 在 `H⁰` 上就是系数作用 `g • ·`。

`conjNormalMap V M g 0 = map (conj by g) (pair) 0`；用库内 `map_degreeZeroClass`
把它算成 `degreeZeroClass (g • u)`（`conjNormalPair_hom_apply` 给 `pair.hom = g • ·`）。 -/
theorem conjNormalMap_degreeZeroClass (g : G) (u : M)
    (hu : ∀ v : ↥V, ((ofDiscreteModule ℤ ↥V M).ρ v) u = u) :
    ContinuousCohomology.conjNormalMap V M g 0
        (ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ ↥V M) u hu) =
      ContinuousCohomology.degreeZeroClass (ofDiscreteModule ℤ ↥V M) (g • u)
        (fun v => by
          show (v : G) • (g • u) = g • u
          rw [smul_smul]
          have hv : (v : G) * g = g * (g⁻¹ * (v : G) * g) := by group
          rw [hv, ← smul_smul]
          congr 1
          have hmem : g⁻¹ * (v : G) * g ∈ V := by
            simpa using (inferInstance : V.Normal).conj_mem (v : G) v.2 g⁻¹
          simpa [Subgroup.smul_def] using hu ⟨g⁻¹ * (v : G) * g, hmem⟩) := by
  rw [ContinuousCohomology.conjNormalMap_def, ContinuousCohomology.map_degreeZeroClass]
  exact degreeZeroClass_congr (ContinuousCohomology.conjNormalPair_hom_apply V M g u) _ _

/-- ★★★★ **α**：`H⁰ ≅ 不变点` 的比较同构把 `H⁰` 上的共轭作用送到不变点上的自然作用。 -/
theorem explicitH0Iso_conjNormalMap_zero (g : G) (x : H0 ↥V M) :
    ContinuousCohomology.conjNormalMap V M g 0
        ((explicitH0IsoContinuousCohomology ↥V M).hom x) =
      (explicitH0IsoContinuousCohomology ↥V M).hom (g • x) := by
  rw [explicitH0IsoContinuousCohomology_hom_eq_degreeZeroClass,
    conjNormalMap_degreeZeroClass, explicitH0IsoContinuousCohomology_hom_eq_degreeZeroClass]
  exact degreeZeroClass_congr (coe_smul_fixedPoints_addSubgroup g x).symm _ _

end General

/-! ## 战役形态：`M` 及其共轭等变性 -/

section Campaign

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [CompactSpace ↥I]

/-- ★★★★★ **`M`**：`Cᴵ → H¹(I, μ_p)`（显式离散载体 `H1 ↥I (ZMod p)`）。

`= H¹比较⁻¹ ∘ contDeltaZeroBar I ∘ H⁰比较`：先把 `Cᴵ` 送到 `H⁰(I, C)`（α 桥），
再用 GS (6.17) 的连结映射 `δ₀` 送到 `H¹(I, μ_p)`，最后落在显式模型上
（它带 `DiscreteTopology`，能喂 `H¹(Γ⧸I, ·)`）。 -/
noncomputable def contM (x : contInvC (F := F) p I) : H1 ↥I (ZMod p) :=
  (explicitH1AddEquivContinuousCohomology ↥I (ZMod p)).symm
    ((contDeltaZeroBar (F := F) p I)
      ((explicitH0IsoContinuousCohomology ↥I (contC (F := F) p)).hom x))

/-- `M` 展开到 `continuousCohomology 1` 层的形态（下游比较用）。 -/
theorem contM_eq (x : contInvC (F := F) p I) :
    (explicitH1AddEquivContinuousCohomology ↥I (ZMod p)) (contM (F := F) p I x) =
      (contDeltaZeroBar (F := F) p I)
        ((explicitH0IsoContinuousCohomology ↥I (contC (F := F) p)).hom x) :=
  AddEquiv.apply_symm_apply _ _

/-- ★★★★★ **`M` 的共轭等变性**：`contM (g • x) = g • contM x`（`g : Γ`）。

三块桥依次开火：α（`H0iso_conjNormalMap_zero`）、`Hyp574`（`δ` 的共轭等变）、
`Hyp575`（比较同构的共轭等变）。 -/
theorem contM_smul (g : AbsoluteGaloisGroup F) (x : contInvC (F := F) p I) :
    contM (F := F) p I (g • x) = g • contM (F := F) p I x := by
  unfold contM
  rw [(explicitH0Iso_conjNormalMap_zero (M := contC (F := F) p) I g x).symm,
    ← contDeltaZeroBar_conjNormal_apply (F := F) p I g
      ((explicitH0IsoContinuousCohomology ↥I (contC (F := F) p)).hom x),
    contH1_iso_symm_conjNormal]
  rw [AddEquiv.symm_apply_apply]

end Campaign

end L20261018

#print axioms L20261018.degreeZeroClass_congr
#print axioms L20261018.conjNormalMap_degreeZeroClass
#print axioms L20261018.explicitH0Iso_conjNormalMap_zero
#print axioms L20261018.contM
#print axioms L20261018.contM_smul
