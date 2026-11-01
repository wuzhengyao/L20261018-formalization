import L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr

/-!
# S40 R8：`ContinuousSMul G ↥K_nr`（`RECON-R3` §85.4 第 4 步）

## 为什么这一步是入场券

`Hyp386.residueMap` 要 `[ContinuousSMul G M]`。`G` 在**离散**模 `M` 上的作用连续
⟺ 每个 `m` 的稳定子 `Stab m` 在 `G` 中**开**。

R4（`RECON-R3` §82.2）已证：
* `K_s((π))^×` 上**不成立**（`Σ a_n π^n` 的稳定子是开子群的无限交）；
* `K_nr^×`（`= ⋃ K'((π))`）上**成立**：`x ∈ K'((π))` ⟹ `Stab x ⊇ fixingSubgroup K'` 开。

本轮把这个论证形式化。

## 本轮机检

| 声明 | 内容 |
|---|---|
| `knrMap_eq_self_of_mem_fixing` | `σ ∈ fixingSubgroup K'` 且 `x ∈ K'((π))` ⟹ `knrMap σ x = x` |
| **`fixingSubgroup_le_stabilizer`** | ★★★★ `fixingSubgroup K' ≤ Stab x`（`x ∈ K'((π))`） |
| **`isOpen_stabilizer`** | ★★★★★ **`IsOpen (Stab x)`**（`x : ↥K_nr`） |
| **`knrContinuousSMulOn`** | ★★★★★ **`ContinuousSMul G ↥K_nr`**（离散拓扑下由「每点常值邻域」） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-! ## 1. `fixingSubgroup K'` 固定 `K'((π))` 的每个元素 -/

/-- `σ` 固定 `K'` 逐点 ⟹ `knrMap σ` 固定 `K'((π))` 逐点。 -/
theorem knrMap_eq_self_of_mem_fixing (σ : TauCeti.AbsoluteGaloisGroup K)
    {K' : IntermediateField K (SeparableClosure K)}
    (hσ : σ ∈ K'.fixingSubgroup) {x : LaurentSeries (SeparableClosure K)}
    (hx : x ∈ (coeffIncl (K := K) K').fieldRange) : knrMap σ x = x := by
  obtain ⟨y, rfl⟩ := hx
  ext n
  rw [knrMap_coeff, coeffIncl_coeff, IntermediateField.algebraMap_apply]
  exact congrArg Subtype.val
    ((IntermediateField.mem_fixingSubgroup_iff K' σ).mp hσ _ (y.coeff n).2)

/-! ## 2. 稳定子包含 `fixingSubgroup K'` -/

/-- ★★★★ **`fixingSubgroup K' ≤ Stab x`**。 -/
theorem fixingSubgroup_le_stabilizer (K' : FinInt K) (x : ↥(KnrSubfield K))
    (hx : (x : LaurentSeries (SeparableClosure K)) ∈ (coeffIncl (K := K) K'.1).fieldRange) :
    K'.1.fixingSubgroup ≤ MulAction.stabilizer (TauCeti.AbsoluteGaloisGroup K) x := by
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  show knrMap σ (x : LaurentSeries (SeparableClosure K)) = (x : LaurentSeries (SeparableClosure K))
  exact knrMap_eq_self_of_mem_fixing σ hσ hx

/-- ★★★★★ **每点稳定子开**。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8160 quote="Denoting by $U_{nr}$ the multiplicative group of units in $K_{nr}$, we get an"
theorem isOpen_stabilizer (x : ↥(KnrSubfield K)) :
    IsOpen ((MulAction.stabilizer (TauCeti.AbsoluteGaloisGroup K) x :
      Subgroup (TauCeti.AbsoluteGaloisGroup K)) : Set (TauCeti.AbsoluteGaloisGroup K)) := by
  obtain ⟨K', hx⟩ := mem_KnrSubfield.mp x.2
  haveI : FiniteDimensional K ↥K'.1 := K'.2
  exact Subgroup.isOpen_mono (fixingSubgroup_le_stabilizer K' x hx)
    (IntermediateField.fixingSubgroup_isOpen K'.1)

/-! ## 3. 离散拓扑与 `ContinuousSMul` -/

noncomputable instance knrSubfieldTopologicalSpace : TopologicalSpace ↥(KnrSubfield K) := ⊥

instance knrSubfieldDiscreteTopology : DiscreteTopology ↥(KnrSubfield K) := ⟨rfl⟩

/-- ★★★★★ **`ContinuousSMul G ↥K_nr`**：`↥K_nr` 取**离散**拓扑，由「每点有常值邻域」给出。

对 `(g, y)`，取 `y ∈ K'((π))`，则 `(g * fixingSubgroup K') × {y}` 是 `(g,y)` 的邻域且
其上 `(g', y') ↦ g' • y' = g • y` 为常值（因 `fixingSubgroup K'` 固定 `K'((π))` 逐点）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:8162 quote="1\to U_{nr}\to K_{nr}^{\times}\xrightarrow{v}\mathbf{Z}\to0"
instance knrContinuousSMulOn : ContinuousSMul (TauCeti.AbsoluteGaloisGroup K)
    ↥(KnrSubfield K) where
  continuous_smul := by
    rw [continuous_iff_continuousAt]
    rintro ⟨g, y⟩
    obtain ⟨K', hy⟩ := mem_KnrSubfield.mp y.2
    haveI : FiniteDimensional K ↥K'.1 := K'.2
    -- `{g' | g' • y = g • y}` 是开的
    have hopen1 : IsOpen ({g' : TauCeti.AbsoluteGaloisGroup K | g' • y = g • y}) := by
      have heq : {g' : TauCeti.AbsoluteGaloisGroup K | g' • y = g • y}
          = (fun z : TauCeti.AbsoluteGaloisGroup K => g * z) ''
            ((MulAction.stabilizer (TauCeti.AbsoluteGaloisGroup K) y :
              Subgroup (TauCeti.AbsoluteGaloisGroup K)) : Set (TauCeti.AbsoluteGaloisGroup K)) := by
        ext g'
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro h
          refine ⟨g⁻¹ * g', ?_, by group⟩
          rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul, h, inv_smul_smul]
        · rintro ⟨z, hz, rfl⟩
          rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hz
          rw [mul_smul, hz]
      rw [heq]
      exact (Homeomorph.isOpen_image (Homeomorph.mulLeft g)).mpr (isOpen_stabilizer y)
    -- 邻域
    have hU : ({g' : TauCeti.AbsoluteGaloisGroup K | g' • y = g • y} ×ˢ
        ({y} : Set ↥(KnrSubfield K))) ∈ nhds (g, y) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (hopen1.mem_nhds (by simp))
        ((isOpen_discrete ({y} : Set ↥(KnrSubfield K))).mem_nhds rfl)
    -- 在邻域上常值
    have hev : (fun p : TauCeti.AbsoluteGaloisGroup K × ↥(KnrSubfield K) => p.1 • p.2)
        =ᶠ[nhds (g, y)] (fun _ => g • y) :=
      Filter.eventually_of_mem hU (fun p hp => by
        obtain ⟨hg', hy'⟩ := hp
        simp only [Set.mem_singleton_iff] at hy'
        subst hy'
        exact hg')
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

end L20261018

#print axioms L20261018.isOpen_stabilizer
#print axioms L20261018.knrContinuousSMulOn
