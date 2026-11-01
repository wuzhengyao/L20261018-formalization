import L20261018.Hyp515

/-!
# S43 R21（**S4**）：`I_K` 的 ℓ-Sylow ≅ `ℤ_ℓ` —— **（★）对 `I_K` 本身闭合**

## 本件在（★）的哪一格

```
（★）
 ├─ S1  载体对齐                  ✅ Hyp511
 ├─ S3c 模型 ℓ-部分 ≅ ℤ_ℓ 且无限  ✅ Hyp513 ＋ Hyp514
 ├─ S2  化到 I/P_K ＋ 交平凡        ✅ Hyp515
 └─ S4  搬回 ＋ 组装              ← **本件**
```

## 数学（三步，全部是「把已有的 `≃ₜ*` 拼起来」）

设 `q = char κ`、`ℓ ≠ q`，`M := ℤ̂^{(p')}(1)`，`f : ↥I_K ↠ ↥(tameInertia K)`（`Hyp515`）。

1. **唯一性**：`tameInertia` 交换（`tameInertia_isMulCommutative`）⟹ 其 ℓ-Sylow **唯一**
   （`IsProPSylow.eq_of_normal`）。取 `P` ＝ `↥I_K` 的 ℓ-Sylow（`exists_isProPSylow`），
   则 `P.map f` 与 `Q_M.map e`（`e : M ≃ₜ* tameInertia`）都等于那**唯一**的 ℓ-Sylow。
2. **交平凡 ⟹ `P → P.map f` 是双射**（`Hyp515` 的 `inf_wildInertia_eq_bot` ＋
   `ker f = P_K`），于是（紧 → T2 的连续双射）`↥P ≃ₜ* ↥(P.map f)`。
3. **拼装**：`↥P ≃ₜ* ↥(P.map f) ＝ ↥Q_t ≃ₜ* ↥Q_M ≃ₜ* Multiplicative ℤ_[ℓ]`
   （`ContinuousMulEquiv.subgroupMap` 供应中间那段）。

## 新增的通用工具

**`continuousMulEquivOfBijective`**：紧群到 Hausdorff 群的连续**双射**同态是拓扑同构。
（`Continuous.isClosedMap` ＋ 闭映射的补像刻画开性；mathlib 无现成件。）

## 机检内容

| 声明 | 内容 |
|---|---|
| **`continuousMulEquivOfBijective`** | ★★★★ 紧 → T2 的连续双射同态 ⟹ `≃ₜ*` |
| **`tameModelEquivTameInertia`** | ★★★★ `M ≃ₜ* ↥(tameInertia K)`（`tameInertiaHom` 的核心像） |
| **`ker_toTameInertia`** | `ker f = P_K` |
| **`isProPSylow_map_eq`** | ★★★★ ℓ-Sylow 的像 ＝ 模型 ℓ-部分的像（唯一性） |
| **`inertiaProPSylowData_inertia`** | ★★★★★ **（★）对 `I_K` 闭合**：`InertiaProPSylowData ↥I_K ℓ` |
| **`cdLE_inertia`** | ★★★★★ `cd_ℓ(I_K) ≤ 1`（**无条件**，只需 ℓ ≠ char κ） |

## 诚实边界

* 本件给的是 `I_K = inertiaSubgroup K`（TauCeti 载体）。搬到**战役载体** `inertiaLoc F`
  需 `Hyp511`（`inertiaLoc_eq_map_inertiaSubgroup`）沿 `≃ₜ*` 运输 —— 下一轮。
* **`C2`（Hensel → 完备）与 `B1` 支线仍未做**；`Ch4TameSymbolHyp`（一般 `K`）仍 `∅-open`。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

/-! ### 通用工具：紧 → T2 的连续双射同态是拓扑同构 -/

/-- ★★★★ **紧群到 Hausdorff 群的连续双射同态是拓扑同构**。

`MulEquiv.toContinuousMulEquiv` 要求 `∀ s, IsOpen (e ⁻¹' s) ↔ IsOpen s`。正向是连续性；
反向用 `Continuous.isClosedMap`（紧 → T2）：若 `e ⁻¹' s` 开，则 `sᶜ = e '' (e ⁻¹' s)ᶜ` 是闭集的像，
故闭，故 `s` 开。 -/
noncomputable def continuousMulEquivOfBijective {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [CompactSpace G] [T2Space H] (f : G →* H) (hf : Continuous f)
    (hbij : Function.Bijective f) : G ≃ₜ* H := by
  refine MulEquiv.toContinuousMulEquiv (MulEquiv.ofBijective f hbij) fun s => ⟨?_, ?_⟩
  · -- 原像开 ⟹ 开（闭映射 ＋ 双射）
    intro hs
    have hclosed : IsClosed ((f ⁻¹' s)ᶜ : Set G) := hs.isClosed_compl
    have himg : f '' ((f ⁻¹' s)ᶜ : Set G) = sᶜ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        obtain ⟨x, rfl⟩ := hbij.surjective y
        exact ⟨x, by simpa using hy, rfl⟩
    have hcs : IsClosed (sᶜ : Set H) := himg ▸ hf.isClosedMap _ hclosed
    simpa using hcs.isOpen_compl
  · -- 开 ⟹ 原像开（连续）
    intro hs
    exact hs.preimage hf

/-! ### `M ≃ₜ* ↥(tameInertia K)` -/

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- `I_K` 作为紧群的紧性（闭子群 of 紧群）。**实例形式**：`InertiaProPSylowData` 的**陈述**需要它。 -/
instance inertiaSubgroup_compactSpace : CompactSpace ↥(inertiaSubgroup K) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaSubgroup K).isCompact

/-- 驯惯性（`I_K/P_K`）的紧性。 -/
instance tameInertia_compactSpace : CompactSpace ↥(tameInertia K) :=
  isCompact_iff_compactSpace.mp (isClosed_tameInertia K).isCompact

/-- ★★★★ **模型 `ℤ̂^{(p')}(1)` 与驯惯性的拓扑同构**（`tameInertiaHom` 单射 ＋ 像 ＝ `tameInertia`）。 -/
noncomputable def tameModelEquivTameInertia : TameModel K ≃ₜ* ↥(tameInertia K) := by
  have hmem : ∀ x : TameModel K, (tameInertiaHom K) x ∈ tameInertia K := by
    intro x
    rw [← range_tameInertiaHom]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  refine continuousMulEquivOfBijective
    ((tameInertiaHom K).toMonoidHom.codRestrict (tameInertia K) hmem)
    (Continuous.subtype_mk (tameInertiaHom K).continuous hmem) ⟨?_, ?_⟩
  · intro a b h
    exact tameInertiaHom_injective K (congrArg Subtype.val h)
  · intro y
    have hy : (y : tameQuotient K) ∈ (tameInertiaHom K).range := by
      rw [range_tameInertiaHom]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

/-- **`f := toTameInertia` 的核是 `P_K`**（`ker(toTameQuotient) = P_K`）。 -/
theorem ker_toTameInertia :
    (toTameInertia (K := K)).toMonoidHom.ker
      = (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h3 : ((toTameInertia (K := K) x : ↥(tameInertia K)) : tameQuotient K)
        = ((1 : ↥(tameInertia K)) : tameQuotient K) := congrArg Subtype.val h
    have h4 : ((1 : ↥(tameInertia K)) : tameQuotient K) = 1 := rfl
    rw [h4] at h3
    exact Subgroup.mem_subgroupOf.mpr (toTameQuotient_eq_one_iff.mp h3)
  · intro h
    have hx : (x : Field.absoluteGaloisGroup K) ∈ wildInertiaSubgroup K :=
      Subgroup.mem_subgroupOf.mp h
    exact Subtype.ext (toTameQuotient_eq_one_iff.mpr hx)


/-! ### S4 主体：（★）对 `I_K` 闭合 -/

/-- **`f := toTameInertia` 在 `P` 上的限制是单射**（核为 `P_K`，与 `P` 交平凡）。 -/
theorem toTameInertia_subgroupMap_injective (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (P : Subgroup ↥(inertiaSubgroup K)) (hP : IsProPSylow ℓ P) :
    Function.Injective (MonoidHom.subgroupMap (toTameInertia (K := K)).toMonoidHom P) := by
  intro a b hab
  have hfk : (a : ↥(inertiaSubgroup K)) * (b : ↥(inertiaSubgroup K))⁻¹
      ∈ (toTameInertia (K := K)).toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Subtype.ext_iff] at *
    -- `hab` 给出两边的像是 `tameQuotient` 中相等
    have h : ((toTameInertia (K := K) a : ↥(tameInertia K)) : tameQuotient K)
        = ((toTameInertia (K := K) b : ↥(tameInertia K)) : tameQuotient K) :=
      congrArg Subtype.val hab
    show ((toTameInertia (K := K) a : ↥(tameInertia K)) : tameQuotient K)
        * (((toTameInertia (K := K) b : ↥(tameInertia K)) : tameQuotient K))⁻¹ = 1
    rw [h, mul_inv_cancel]
  have hPk : (a : ↥(inertiaSubgroup K)) * (b : ↥(inertiaSubgroup K))⁻¹ ∈ P :=
    P.mul_mem a.2 (P.inv_mem b.2)
  have hbot := inf_wildInertia_eq_bot q ℓ hℓq P hP
  have hmem : (a : ↥(inertiaSubgroup K)) * (b : ↥(inertiaSubgroup K))⁻¹
      ∈ P ⊓ (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) :=
    ⟨hPk, ker_toTameInertia (K := K) ▸ hfk⟩
  rw [hbot] at hmem
  simp only [Subgroup.mem_bot] at hmem
  refine Subtype.ext ?_
  have h2 : ((a : ↥P) : ↥(inertiaSubgroup K)) * (((b : ↥P) : ↥(inertiaSubgroup K)))⁻¹ = 1 := hmem
  exact mul_inv_eq_one.mp h2

/-- ★★★★★ **（★）对 `I_K` 闭合**：惯性群 `I_K` 的 ℓ-Sylow 与 `ℤ_ℓ` 拓扑同构（ℓ ≠ char κ）。

证明：取 `P` ＝ `↥I_K` 的 ℓ-Sylow。`toTameInertia` 把它送到 `tameInertia` 的 ℓ-Sylow；
后者交换故 ℓ-Sylow **唯一**，于是 `P.map f = Q_M.map e`（模型 Sylow 的像）。
`P ⊓ P_K = ⊥` 使 `P → P.map f` 成为紧群到 Hausdorff 群的连续双射 ⟹ `↥P ≃ₜ* ↥(P.map f)`，
再拼上 `↥Q_M ≃ₜ* Multiplicative ℤ_[ℓ]`（`Hyp514`）。 -/
noncomputable def inertiaProPSylowData_inertia (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q) :
    InertiaProPSylowData ↥(inertiaSubgroup K) ℓ := by
  -- `residueChar K = q`，于是一切下游条件可搬
  have hres : residueChar K = q := ringChar.eq _ q
  have hℓ' : ℓ.Coprime (residueChar K) := hres ▸ hℓ
  have hℓq : ℓ ≠ q := by
    have hnd : ¬ ℓ ∣ q := (Fact.out : ℓ.Prime).coprime_iff_not_dvd.1 hℓ
    exact fun h => hnd (h ▸ dvd_rfl)
  -- 模型的 ℓ-Sylow（`Hyp514`）
  let ζ : TameModel K := Classical.choose (exists_generator_primeToPTateModule K)
  have hζc : (Subgroup.closure ({ζ} : Set (TameModel K))).topologicalClosure = ⊤ :=
    Classical.choose_spec (exists_generator_primeToPTateModule K)
  have hζ : closedZpowers ζ = ⊤ := by
    rw [closedZpowers_def, Subgroup.zpowers_eq_closure]
    exact hζc
  let D : InertiaProPSylowData (TameModel K) ℓ :=
    inertiaProPSylowData_tameModel (K := K) ℓ hℓ' ζ hζ
  -- `e : M ≃ₜ* ↥tameInertia`，模型的 ℓ-Sylow 搬到驯惯性
  let eM : TameModel K ≃ₜ* ↥(tameInertia K) := tameModelEquivTameInertia (K := K)
  let QM : Subgroup (TameModel K) := D.P
  have hQM : IsProPSylow ℓ QM := D.isProPSylow
  let Qt : Subgroup ↥(tameInertia K) := Subgroup.map (↑eM : TameModel K →* ↥(tameInertia K)) QM
  have hQt : IsProPSylow ℓ Qt := hQM.map_continuousMulEquiv eM
  -- `I_K` 的 ℓ-Sylow
  let P : Subgroup ↥(inertiaSubgroup K) :=
    Classical.choose (exists_isProPSylow (p := ℓ) ↥(inertiaSubgroup K))
  have hP : IsProPSylow ℓ P :=
    Classical.choose_spec (exists_isProPSylow (p := ℓ) ↥(inertiaSubgroup K))
  have hPmap : IsProPSylow ℓ (Subgroup.map (toTameInertia (K := K)).toMonoidHom P) :=
    isProPSylow_map_toTameInertia ℓ P hP
  -- 唯一性（驯惯性交换）
  have hPeq : Subgroup.map (toTameInertia (K := K)).toMonoidHom P = Qt :=
    IsProPSylow.eq_of_normal ℓ ↥(tameInertia K) _ _ hPmap hQt
      (Subgroup.normal_of_isMulCommutative _)
  -- `P → P.map f` 的双射 ⟹ 拓扑同构
  have hinj := toTameInertia_subgroupMap_injective q ℓ hℓq P hP
  have hsurj : Function.Surjective
      (MonoidHom.subgroupMap (toTameInertia (K := K)).toMonoidHom P) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hcont : Continuous
      (MonoidHom.subgroupMap (toTameInertia (K := K)).toMonoidHom P) :=
    Continuous.subtype_mk
      ((toTameInertia (K := K)).continuous.comp continuous_subtype_val) _
  haveI : CompactSpace ↥P := isCompact_iff_compactSpace.mp hP.isClosed.isCompact
  have eP : ↥P ≃ₜ* ↥(Subgroup.map (toTameInertia (K := K)).toMonoidHom P) :=
    continuousMulEquivOfBijective _ hcont ⟨hinj, hsurj⟩
  -- 拼装：`↥P ≃ₜ* ↥Qt ≃ₜ* ↥QM ≃ₜ* ℤ_[ℓ]`
  have eQt : ↥QM ≃ₜ* ↥Qt := ContinuousMulEquiv.subgroupMap eM QM
  have hbig : ↥P ≃ₜ* Multiplicative ℤ_[ℓ] :=
    (hPeq ▸ eP).trans (eQt.symm.trans D.padicEquiv.some)
  exact { P := P, isProPSylow := hP, padicEquiv := ⟨hbig⟩ }

/-- ★★★★★ **`cd_ℓ(I_K) ≤ 1`**，无条件（只需 ℓ ≠ char κ）。 -/
theorem cdLE_inertia (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q) :
    CohomologicalDimensionLE.{0, 0} ℓ ↥(inertiaSubgroup K) 1 :=
  (inertiaProPSylowData_inertia (K := K) q ℓ hℓ).cdLE

end L20261018

#print axioms L20261018.continuousMulEquivOfBijective
#print axioms L20261018.tameModelEquivTameInertia
#print axioms L20261018.ker_toTameInertia
#print axioms L20261018.toTameInertia_subgroupMap_injective
#print axioms L20261018.inertiaProPSylowData_inertia
#print axioms L20261018.cdLE_inertia
