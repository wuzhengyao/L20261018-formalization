import L20261018.Infra.Cohomology.Conjugation.Step001_m_conj_equivariant
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.ConnectingMap

/-!
# S47 R3：★★★★ **`M` 的载体桥 β —— 比较同构的共轭等变性**

S47 R2 把 `M` 的难点拆成三座载体桥（`S47-DIGEST.md` §9）：α（`Cᴵ ↔ H⁰`）、
**β（比较同构 `H1 ↔ continuousCohomology 1` 的等变性）**、γ（`Γ⧸I`-作用）。
本件攻下 **β**：

```
explicitH1AddEquivContinuousCohomology ↥N M
  : H1 ↥N M ≃+ continuousCohomology 1 (ofDiscreteModule ℤ ↥N M)
```

要它把**显式模型**上的共轭 `explicitConj1 N g`（`Conjugation/Basic.lean:176`，
即 `g • ·`，`@[defeq]` 见 `explicitConj1_apply_eq_smul`）送到**标准模型**上的共轭
`conjNormalMap N M g 1`（`map` of the compatible pair，`Corestriction/Conjugation.lean:259`）。

**先前判为"库内无桥接引理"（R2）；R3 实测：桥接引理不必新造，只需三块拼装。**

1. `conjNormal_coe_eq_inverseConjugationHom`：`conjNormalMap` 用的自动同构
   `↑(ContinuousAut.conjNormal g⁻¹)` 与 `explicitConj1` 用的
   `N.inverseConjugationHom g`（`Topology/.../ContinuousMonoidHom/Basic.lean:292`）**是同一个连续同态**
   （两者的逐点公式都是 `n ↦ g⁻¹ * ↑n * g`）。
2. `conjNormal_hequiv`：`(n ↦ g⁻¹ n g, g ·)` 是**相容对**
   （`gf(φ n · m) = n · (g m)`，即共轭与作用相配）。
3. `conjNormalMap_comp_explicitH1`：由库内
   `explicitH1AddEquivContinuousCohomology_map`（`CohomologyComparison.lean:162`，
   **比较同构对相容对的自然性**）＋ `map_congr_of_hom_apply`（把 (1) 换掉 `snd` 的 φ）组装。

**故 GS (6.17) 之后 `H^{i-1}(G/H, C^H) → H^{i-1}(G/H, H¹(H,A))` 的系数层映射，在
`H¹(I,μ_p)` 一侧已可用显式离散模型（`H1`，带 `DiscreteTopology`）陈述**——这正是 `M`
要喂给 `H¹(Γ⧸I, ·)` 的载体。
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

/-! ## 一般形态（对任意 profinite 群的闭正规子群成立） -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SeparatelyContinuousMul G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]

/-- ★★★ **`conjNormalMap` 的自动同构就是 `inverseConjugationHom`**：两者逐点都是 `n ↦ g⁻¹ * n * g`。 -/
theorem conjNormal_coe_eq_inverseConjugationHom (g : G) :
    (↑(ContinuousAut.conjNormal (N := N) g⁻¹) : ↥N →ₜ* ↥N) = N.inverseConjugationHom g := by
  refine ContinuousMonoidHom.ext fun n => Subtype.ext ?_
  rw [Subgroup.inverseConjugationHom_apply]
  simp

/-- ★★★ **相容对**：`(n ↦ g⁻¹ n g, g ·)` 满足 `gf (φ n · m) = n · (gf m)`。 -/
theorem conjNormal_hequiv (g : G) :
    ∀ (n : ↥N) (m : M),
      (DistribSMul.toAddMonoidHom M g) ((N.inverseConjugationHom g) n • m) =
        n • ((DistribSMul.toAddMonoidHom M g) m) := by
  intro n m
  have hv : ((N.inverseConjugationHom g) n : G) = g⁻¹ * (n : G) * g := by
    rw [Subgroup.inverseConjugationHom_apply]
  simp only [DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def, hv, smul_smul]
  group

/-- ★★★★ **β**：比较同构把显式共轭（`= g • ·`）送到标准共轭 `conjNormalMap`。 -/
theorem conjNormalMap_comp_explicitH1 (g : G) (x : H1 ↥N M) :
    ContinuousCohomology.conjNormalMap N M g 1
        (explicitH1AddEquivContinuousCohomology ↥N M x) =
      explicitH1AddEquivContinuousCohomology ↥N M (g • x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [ContinuousCohomology.conjNormalMap_def]
    set pair₂ : TopRep.res (↑(N.inverseConjugationHom g) : ↥N →* ↥N)
        (ofDiscreteModule ℤ ↥N M) ⟶ ofDiscreteModule ℤ ↥N M :=
      ofDiscreteModulePair _ (DistribSMul.toAddMonoidHom M g).toIntLinearMap
        (conjNormal_hequiv (M := M) N g) with hpair₂
    rw [ContinuousCohomology.map_congr_of_hom_apply
      (conjNormal_coe_eq_inverseConjugationHom N g)
      (ContinuousCohomology.conjNormalPair N M g) pair₂ (fun m => ?_)]
    · rw [explicitH1AddEquivContinuousCohomology_map ↥N M ↥N M
        (N.inverseConjugationHom g) (DistribSMul.toAddMonoidHom M g)
        (conjNormal_hequiv (M := M) N g)]
      congr 1
    · rw [ContinuousCohomology.conjNormalPair_hom_apply, ofDiscreteModulePair_hom_apply]
      rfl

/-! ## 战役形态：`N = I ≤ Γ = Gal(F̄/F)`，`M = μ_p` -/

section Campaign

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [CompactSpace ↥I]

/-- ★★★★★ **β（战役形态）**：`H¹(I, μ_p)` 的显式离散载体上，共轭作用与标准模型一致。

下游用法：`M : Cᴵ → H1 ↥I (ZMod p)` 的等变性一旦在显式模型上陈述，就能经此件转回
`continuousCohomology 1`（`M` 的 `contDeltaZeroBar` 形态，见 `Hyp574`）。 -/
theorem contH1_iso_conjNormal (g : AbsoluteGaloisGroup F) (x : H1 ↥I (ZMod p)) :
    ContinuousCohomology.conjNormalMap I (ZMod p) g 1
        (explicitH1AddEquivContinuousCohomology ↥I (ZMod p) x) =
      explicitH1AddEquivContinuousCohomology ↥I (ZMod p) (g • x) :=
  conjNormalMap_comp_explicitH1 (M := ZMod p) I g x

/-- 同一件事的**逆方向**（下游 `M` 的靶在显式模型时用这一条）。 -/
theorem contH1_iso_symm_conjNormal (g : AbsoluteGaloisGroup F)
    (y : continuousCohomology 1 (ofDiscreteModule ℤ ↥I (ZMod p))) :
    ContinuousCohomology.conjNormalMap I (ZMod p) g 1 y =
      (explicitH1AddEquivContinuousCohomology ↥I (ZMod p))
        (g • (explicitH1AddEquivContinuousCohomology ↥I (ZMod p)).symm y) := by
  conv_lhs => rw [← AddEquiv.apply_symm_apply (explicitH1AddEquivContinuousCohomology ↥I (ZMod p)) y]
  exact contH1_iso_conjNormal (F := F) p I g _

end Campaign

end L20261018

#print axioms L20261018.conjNormal_coe_eq_inverseConjugationHom
#print axioms L20261018.conjNormal_hequiv
#print axioms L20261018.conjNormalMap_comp_explicitH1
#print axioms L20261018.contH1_iso_conjNormal
#print axioms L20261018.contH1_iso_symm_conjNormal
