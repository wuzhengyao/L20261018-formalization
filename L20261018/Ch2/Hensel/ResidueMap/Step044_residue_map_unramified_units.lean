import L20261018.Ch2.Hensel.Inertia.Step010_knr_continuous_smul
import L20261018.Infra.Cohomology.Step006_rv_complex_assembly

/-!
# S40 R9：装 `S : DiscreteShortExact G U_nr (Additive K_nr^×) (ULift ℤ)` 并喂 `Hyp386.residueMap`

## 本轮做什么（纯装配）

前八轮已把 G2 的全部数学吃干（都在**正确的**载体 `KnrSubfield K = ⋃_{K'} K'((π))` 上）：

| 部件 | 件 |
|---|---|
| `v_{K_nr} : K_nr^× →* Multiplicative ℤ`，`v π = 1` | `Hyp467.knrValOn`／`knrValOn_pi` |
| GS (6.1) 正合 ／ 满射 ／ 分裂 | `Hyp467.knrProjOn_exact`／`_surjective`／`_split` |
| `G` 保 `K_nr` ＋ 作用 ＋ `v`-不变性 | `Hyp468.knrMap_mem_Knr`／`knrMulActionOn`／`knrUnitsMulActionOn`／`knrValOn_smul` |
| **`ContinuousSMul G ↥K_nr`** | **`Hyp469.knrContinuousSMulOn`** |

⟹ 本轮只把 `DiscreteShortExact` 的七个字段摆好，再喂 `Hyp386.residueMap` 得 `r_v^{n+2}`。

## 本轮机检

| 声明 | 内容 |
|---|---|
| `continuous_smul_of_stabilizer_isOpen` | ★★★★ 通用引理：`M` 离散 ＋ 每点稳定子开 ⟹ 作用连续 |
| `knrUnitsSmul_eq_self` | `σ ∈ fixingSubgroup K'` ⟹ `σ • x = x`（`x ∈ K'((π))`） |
| `isOpen_stabilizer'` | ★★★★★ `IsOpen (Stab x)`（`x : Additive (K_nr^×)`） |
| `knrContinuousSMul'` | ★★★★★ **`ContinuousSMul G (Additive (K_nr^×))`** |
| `knrKerContinuousSMul'` | ★★★★ `ContinuousSMul G U_nr` |
| **`knrShortExact'`** | ★★★★★ **`DiscreteShortExact G U_nr (Additive (K_nr^×)) (ULift ℤ)`** |
| **`knrResidueMap'`** | ★★★★★ **`r_v^{n+2}`**（＝ `Hyp386.residueMap` 喂进本轮装好的 `S`） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

/-! ## 1. 通用引理：离散模 ＋ 每点稳定子开 ⟹ 作用连续 -/

/-- ★★★★ **离散模上的作用连续 ⟺ 每点稳定子开**（用「每点常值邻域」）。 -/
theorem continuous_smul_of_stabilizer_isOpen {G M : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [MulAction G M] [TopologicalSpace M] [DiscreteTopology M]
    (h : ∀ m : M, IsOpen ((MulAction.stabilizer G m : Subgroup G) : Set G)) :
    Continuous (fun p : G × M => p.1 • p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g, y⟩
  have hopen1 : IsOpen ({g' : G | g' • y = g • y}) := by
    have heq : {g' : G | g' • y = g • y}
        = (fun z : G => g * z) '' ((MulAction.stabilizer G y : Subgroup G) : Set G) := by
      ext g'
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hh
        refine ⟨g⁻¹ * g', ?_, by group⟩
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, hh, inv_smul_smul]
      · rintro ⟨z, hz, rfl⟩
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hz
        rw [mul_smul, hz]
    rw [heq]
    exact (Homeomorph.isOpen_image (Homeomorph.mulLeft g)).mpr (h y)
  have hU : ({g' : G | g' • y = g • y} ×ˢ ({y} : Set M)) ∈ nhds (g, y) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hopen1.mem_nhds (by simp))
      ((isOpen_discrete ({y} : Set M)).mem_nhds rfl)
  have hev : (fun p : G × M => p.1 • p.2) =ᶠ[nhds (g, y)] (fun _ => g • y) :=
    Filter.eventually_of_mem hU (fun p hp => by
      obtain ⟨hg', hy'⟩ := hp
      simp only [Set.mem_singleton_iff] at hy'
      subst hy'
      exact hg')
  exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

variable {K : Type} [Field K]

/-! ## 2. 拓扑（离散） -/

noncomputable instance knrUUnitsTopology : TopologicalSpace (KnrUnits' K) := ⊥

instance knrUUnitsDiscrete : DiscreteTopology (KnrUnits' K) := ⟨rfl⟩

noncomputable instance knrUKerTopology : TopologicalSpace (Additive ↥(knrValOn K).ker) := ⊥

instance knrUKerDiscrete : DiscreteTopology (Additive ↥(knrValOn K).ker) := ⟨rfl⟩

/-! ## 3. `Additive (K_nr^×)` 上的 `DistribMulAction` -/

/-- ★★★★ **`G` 在 `Additive (K_nr^×)` 上的 `DistribMulAction`**。 -/
noncomputable instance knrUDistribMulAction :
    DistribMulAction (TauCeti.AbsoluteGaloisGroup K) (KnrUnits' K) where
  smul σ x := Additive.ofMul (σ • Additive.toMul x)
  one_smul x := by
    apply Additive.toMul.injective
    show Units.map (knrMapOn (K := K) 1).toMonoidHom (Additive.toMul x) = Additive.toMul x
    rw [knrMapOn_id]
    rfl
  mul_smul σ τ x := by
    apply Additive.toMul.injective
    show Units.map (knrMapOn (K := K) (σ * τ)).toMonoidHom (Additive.toMul x)
      = Units.map (knrMapOn (K := K) σ).toMonoidHom
        (Units.map (knrMapOn (K := K) τ).toMonoidHom (Additive.toMul x))
    rw [knrMapOn_mul]
    rfl
  smul_zero σ := by
    apply Additive.toMul.injective
    show Units.map (knrMapOn (K := K) σ).toMonoidHom (1 : (↥(KnrSubfield K))ˣ) = 1
    exact map_one _
  smul_add σ a b := by
    apply Additive.toMul.injective
    show Units.map (knrMapOn (K := K) σ).toMonoidHom (Additive.toMul a * Additive.toMul b)
      = Units.map (knrMapOn (K := K) σ).toMonoidHom (Additive.toMul a)
        * Units.map (knrMapOn (K := K) σ).toMonoidHom (Additive.toMul b)
    rw [map_mul]

instance knrUSMulCommClass :
    SMulCommClass (TauCeti.AbsoluteGaloisGroup K) ℤ (KnrUnits' K) where
  smul_comm σ z x := by
    apply Additive.toMul.injective
    show Units.map (knrMapOn (K := K) σ).toMonoidHom ((Additive.toMul x) ^ z)
      = (Units.map (knrMapOn (K := K) σ).toMonoidHom (Additive.toMul x)) ^ z
    exact map_zpow _ _ _

instance knrUContinuousSMulInt : ContinuousSMul ℤ (KnrUnits' K) where
  continuous_smul := continuous_def.mpr (fun s _ => isOpen_discrete _)

/-! ## 4. 每点稳定子开（单位层）与 `ContinuousSMul` -/

theorem isOpen_stabilizer' (x : KnrUnits' K) :
    IsOpen ((MulAction.stabilizer (TauCeti.AbsoluteGaloisGroup K) x :
      Subgroup (TauCeti.AbsoluteGaloisGroup K)) : Set (TauCeti.AbsoluteGaloisGroup K)) := by
  set y : ↥(KnrSubfield K) :=
    ((Additive.toMul x : (↥(KnrSubfield K))ˣ) : ↥(KnrSubfield K)) with hy
  obtain ⟨K', hK'⟩ := mem_KnrSubfield.mp y.2
  haveI : FiniteDimensional K ↥K'.1 := K'.2
  have h1 : IsOpen ((MulAction.stabilizer (TauCeti.AbsoluteGaloisGroup K) y :
      Subgroup (TauCeti.AbsoluteGaloisGroup K)) : Set (TauCeti.AbsoluteGaloisGroup K)) :=
    Subgroup.isOpen_mono (fixingSubgroup_le_stabilizer K' y hK')
      (IntermediateField.fixingSubgroup_isOpen K'.1)
  refine Subgroup.isOpen_mono ?_ h1
  intro σ hσ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hσ ⊢
  apply Additive.toMul.injective
  show Units.map (knrMapOn (K := K) σ).toMonoidHom (Additive.toMul x) = Additive.toMul x
  apply Units.ext
  show (knrMapOn (K := K) σ) ((Additive.toMul x : (↥(KnrSubfield K))ˣ) :
    ↥(KnrSubfield K)) = _
  exact hσ

/-- ★★★★★ **`ContinuousSMul G (Additive (K_nr^×))`**。 -/
instance knrUContinuousSMul' :
    ContinuousSMul (TauCeti.AbsoluteGaloisGroup K) (KnrUnits' K) where
  continuous_smul := continuous_smul_of_stabilizer_isOpen (isOpen_stabilizer' (K := K))

/-! ## 5. `U_nr = ker v` 上的作用与 `ContinuousSMul` -/

noncomputable def knrUKerSmul (σ : TauCeti.AbsoluteGaloisGroup K)
    (y : Additive ↥(knrValOn K).ker) : Additive ↥(knrValOn K).ker :=
  Additive.ofMul ⟨σ • ((Additive.toMul y : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ), by
    show knrValOn K (σ • ((Additive.toMul y : ↥(knrValOn K).ker) :
      (↥(KnrSubfield K))ˣ)) = 1
    rw [knrValOn_smul]
    exact (Additive.toMul y).2⟩

noncomputable instance knrUKerDistribMulAction :
    DistribMulAction (TauCeti.AbsoluteGaloisGroup K) (Additive ↥(knrValOn K).ker) where
  smul := knrUKerSmul (K := K)
  one_smul x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show Units.map (knrMapOn (K := K) 1).toMonoidHom
      (((Additive.toMul x : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ))
      = ((Additive.toMul x : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ)
    rw [knrMapOn_id]
    rfl
  mul_smul σ τ x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show Units.map (knrMapOn (K := K) (σ * τ)).toMonoidHom
      (((Additive.toMul x : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ))
      = Units.map (knrMapOn (K := K) σ).toMonoidHom (Units.map (knrMapOn (K := K) τ).toMonoidHom
        (((Additive.toMul x : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ)))
    rw [knrMapOn_mul]
    rfl
  smul_zero σ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show Units.map (knrMapOn (K := K) σ).toMonoidHom (1 : (↥(KnrSubfield K))ˣ) = 1
    exact map_one _
  smul_add σ a b := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show Units.map (knrMapOn (K := K) σ).toMonoidHom
        (((Additive.toMul a : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ)
          * ((Additive.toMul b : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ))
      = Units.map (knrMapOn (K := K) σ).toMonoidHom
          ((Additive.toMul a : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ)
        * Units.map (knrMapOn (K := K) σ).toMonoidHom
          ((Additive.toMul b : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ)
    rw [map_mul]

instance knrUKerSMulCommClass :
    SMulCommClass (TauCeti.AbsoluteGaloisGroup K) ℤ (Additive ↥(knrValOn K).ker) where
  smul_comm σ z x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    show Units.map (knrMapOn (K := K) σ).toMonoidHom
        ((((Additive.toMul x : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ)) ^ z)
      = (Units.map (knrMapOn (K := K) σ).toMonoidHom
          (((Additive.toMul x : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ))) ^ z
    exact map_zpow _ _ _

instance knrUKerContinuousSMulInt : ContinuousSMul ℤ (Additive ↥(knrValOn K).ker) where
  continuous_smul := continuous_def.mpr (fun s _ => isOpen_discrete _)

theorem isOpen_stabilizerKer (x : Additive ↥(knrValOn K).ker) :
    IsOpen ((MulAction.stabilizer (TauCeti.AbsoluteGaloisGroup K) x :
      Subgroup (TauCeti.AbsoluteGaloisGroup K)) : Set (TauCeti.AbsoluteGaloisGroup K)) := by
  set u : (↥(KnrSubfield K))ˣ :=
    ((Additive.toMul x : ↥(knrValOn K).ker) : (↥(KnrSubfield K))ˣ) with hu
  obtain ⟨K', hK'⟩ := mem_KnrSubfield.mp ((u : ↥(KnrSubfield K))).2
  haveI : FiniteDimensional K ↥K'.1 := K'.2
  refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen K'.1)
  intro σ hσ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hσ ⊢
  apply Additive.toMul.injective
  apply Subtype.ext
  show (σ • u : (↥(KnrSubfield K))ˣ) = u
  apply Units.ext
  show (knrMapOn (K := K) σ) (u : ↥(KnrSubfield K)) = (u : ↥(KnrSubfield K))
  apply Subtype.ext
  show ((knrMapOn (K := K) σ) (u : ↥(KnrSubfield K)) : LaurentSeries (SeparableClosure K))
    = ((u : ↥(KnrSubfield K)) : LaurentSeries (SeparableClosure K))
  rw [knrMapOn_coe]
  exact knrMap_eq_self_of_mem_fixing σ hσ hK'

instance knrUKerContinuousSMul' :
    ContinuousSMul (TauCeti.AbsoluteGaloisGroup K) (Additive ↥(knrValOn K).ker) where
  continuous_smul := continuous_smul_of_stabilizer_isOpen (isOpen_stabilizerKer (K := K))

/-! ## 6. ★ GS (6.1) 装成 `DiscreteShortExact`（正确的载板上） -/

-- @source file=raw/GilleSzamuely2017.tex locator=line:8160 quote="Denoting by $U_{nr}$ the multiplicative group of units in $K_{nr}$, we get an"
theorem knrInclOn_equivariant (σ : TauCeti.AbsoluteGaloisGroup K)
    (y : Additive ↥(knrValOn K).ker) :
    knrInclOn K ((knrUKerDistribMulAction (K := K)).smul σ y) = σ • knrInclOn K y := by
  apply Additive.toMul.injective
  rfl

-- @source file=raw/GilleSzamuely2017.tex locator=line:8163 quote="which is split by the map $\mathbf{Z}\to K_{nr}^{\times}$ sending $1$ to a local"
theorem knrProjOn_equivariant (σ : TauCeti.AbsoluteGaloisGroup K) (b : KnrUnits' K) :
    knrProjOn K (σ • b) = σ • knrProjOn K b := by
  show (ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul (σ • b)))) : ULift ℤ)
    = σ • (ULift.up (Multiplicative.toAdd (knrValOn K (Additive.toMul b))) : ULift ℤ)
  have h : knrValOn K (Additive.toMul (σ • b)) = knrValOn K (Additive.toMul b) :=
    knrValOn_smul (K := K) σ (Additive.toMul b)
  rw [h]
  rfl

/-- ★★★★★ **GS (6.1)**（`raw/GilleSzamuely2017.tex:8162`）在**正确的** `K_nr` 上装成
`DiscreteShortExact`：`1 → U_nr → K_nr^× →^v ℤ → 0`，`G`-等变，且被 `1 ↦ π` 分裂。 -/
noncomputable def knrShortExact' (K : Type) [Field K] :
    DiscreteShortExact (TauCeti.AbsoluteGaloisGroup K)
      (Additive ↥(knrValOn K).ker) (KnrUnits' K) (ULift ℤ) where
  incl := knrInclOn K
  proj := knrProjOn K
  incl_equivariant := knrInclOn_equivariant (K := K)
  proj_equivariant := knrProjOn_equivariant (K := K)
  incl_injective := knrInclOn_injective K
  proj_surjective := knrProjOn_surjective K
  exact := knrProjOn_exact K

/-- ★★★★★ **GS 6.8.1 的剩余映射** `r_v^{n+2} : H^{n+2}(G, K_nr^×) → H^{n+1}(G, ℚ/ℤ)`。 -/
noncomputable def knrResidueMap' (n : ℕ) :
    continuousCohomology (n + 2)
        (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup K) (KnrUnits' K)) →
      continuousCohomology (n + 1)
        (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup K) QoverZdisc) :=
  residueMap (F := K) (U := Additive ↥(knrValOn K).ker) (M := KnrUnits' K) (knrShortExact' K) n


end L20261018

#print axioms L20261018.knrUContinuousSMul'
#print axioms L20261018.knrUKerContinuousSMul'
#print axioms L20261018.knrInclOn_equivariant
#print axioms L20261018.knrProjOn_equivariant
#print axioms L20261018.knrShortExact'
#print axioms L20261018.knrResidueMap'
