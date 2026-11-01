import Hyp297
import TauCeti.RingTheory.Henselian.Basic

/-!
# S50 R1：`prop:prelim-kummer-valuation`(1) 的**抽象 Hensel 版**

## 为什么这一件是 S50 的第一步

论文 `raw/L20261018.tex:978` 明写：

> 完备离散赋值域是 Hensel 的，逆命题不作假设；本节不以完备性替代 Hensel 性。

而 `prop:prelim-kummer-valuation`(1)（`raw/L20261018.tex:1014–1016`）是

> 单位约化诱导同构
> $\mathcal O_F^\times/\mathcal O_F^{\times p} \simeq K^\times/K^{\times p}$；

这个同构正是「`ker \bar v` = 单位类」的唯一通道，也是 S50 主目标
（`H¹(Γ⧸I, H¹(I,μ_p)) → ker v̄`）落地时**最后一步**要用的载体识别
（`ker v̄ = 𝒪^×/𝒪^{×p} ≅ 𝓀^×/𝓀^{×p}`）。

**此前只有完备版**：`Hyp114.unitPow_iff_residuePow` 走 TauCeti 的
`unitsMap_subtype_mem_range_powMonoidHom_iff`，而那条的 `variable` 带
`[IsNonarchimedeanLocalField F]`（见 `Hyp114` 文件头的「范围决策」硬登记）。
本件把它**降到论文实际假设**：`R` 局部环 ＋ `HenselianRing R 𝔪`，无完备性、无拓扑、无赋值。

## 本件交付

| 声明 | 内容 |
|---|---|
| `residue_unitsMap_eq_one_iff` | 单位约化的核 = `1+𝔪`（逐点） |
| `principalUnit_mem_pow_range` | `1+𝔪 ⊆ (·)^n` 的像（Hensel，**抽象环**，来自 `Hyp297`） |
| **`residue_mem_pow_range_iff`** | ★★★★★ `ρ u ∈ (𝓀^×)^n ⟺ u ∈ (𝒪^×)^n`（逐点，抽象 Hensel） |
| **`unitQuotPowEquiv`** | ★★★★★ `𝒪^×/(𝒪^×)^n ≃* 𝓀^×/(𝓀^×)^n`（**论文 (1) 的抽象 Hensel 版**） |

## 与库内已有件的**增量登记**（L47 ④ / §5.5：「弱于已有件」的不得报成成果）

| 已有件 | 它给了什么 | 本件多了什么 |
|---|---|---|
| `Hyp114.unitPow_iff_residuePow` | **完备情形**的逐点 iff（走 TauCeti `unitsMap_subtype_mem_range_powMonoidHom_iff`） | 换成**抽象 Hensel**（无 `[IsNonarchimedeanLocalField]`） |
| `Hyp163.unit_pow_of_residue_pow_of_hensel` | 抽象 Hensel 的 **⇐ 方向**，结论在 **`Fˣ`** 侧（`∃ y : Fˣ, y^p = u`） | 结论**收在 `𝒪^×` 内**（`∃ z : 𝒪^×, z^p = u`）＋ **⇒ 方向** ＋ **群同构** `unitQuotPowEquiv` |

⟹ **本件的净增量 = ①`⇒` 方向；②根落在 `𝒪^×` 内；③商群同构本身。**
`Hyp163` 的 `⇐` 方向（`Fˣ` 侧）在本件里由 `unit_mem_pow_range_of_residue_mem_ofF` 以更强的 `𝒪^×` 侧形式重述，
**不重复计算**（证明走 `Hyp296`／`Hyp297` 的抽象环路线，与 `Hyp163` 的实现不同）。

## 诚实边界

* 本件**不**涉及上同调：`ker v̄ ≅ 𝒪^×/𝒪^{×n}` 这一步（把 `ker(valLinOf)` 认成
  单位类）需要用 `prop:prelim-kummer-valuation`(2) 的 `ker v̄ = range(infl)`，
  **尚未**机检（S50 后续轮）。
* 本件对 `n` 只要求 `n ≠ 0` 与 `IsUnit (n : R)`（后者由 `char 𝓀 ≠ p` 供给）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section AbstractHensel

variable (R : Type*) [CommRing R] [IsLocalRing R]
  [HenselianRing R (IsLocalRing.maximalIdeal R)]

/-- 单位约化 `𝒪^× → 𝓀^×`（本件的 `ρ`）。 -/
noncomputable abbrev residueUnits : Rˣ →* (IsLocalRing.ResidueField R)ˣ :=
  Units.map (IsLocalRing.residue R)

/-- ★★★★ **单位约化的核 = 主单位群**：`ρ u = 1 ⟺ u - 1 ∈ 𝔪`（逐点）。 -/
theorem residue_units_eq_one_iff (u : Rˣ) :
    residueUnits R u = 1 ↔ ((u : R) - 1) ∈ IsLocalRing.maximalIdeal R := by
  rw [Units.ext_iff]
  constructor
  · intro h
    have h1 : IsLocalRing.residue R ((u : R)) = 1 := by
      simpa [residueUnits] using h
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    rw [map_sub, map_one, h1, sub_self]
  · intro h
    have h0 : IsLocalRing.residue R ((u : R) - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr h
    rw [map_sub, map_one, sub_eq_zero] at h0
    simpa [residueUnits] using h0

/-- ★★★★ **主单位群在 `n` 次幂像中**（抽象 Hensel，`Hyp297` 的 `p` 版）。 -/
theorem exists_pow_eq_of_residue_eq_one (n : ℕ) (hn0 : n ≠ 0)
    (hn : IsUnit (n : R)) {u : Rˣ} (hu : residueUnits R u = 1) :
    ∃ z : Rˣ, z ^ n = u := by
  rw [residue_units_eq_one_iff] at hu
  obtain ⟨z, hz, -⟩ := one_add_subset_pow R n hn0 hn hu
  exact ⟨z, by ext; simpa using hz⟩

/-- 上条的 `MonoidHom.mem_range` 形态。 -/
theorem principalUnit_mem_pow_range_of_eq_one (n : ℕ) (hn0 : n ≠ 0)
    (hn : IsUnit (n : R)) {u : Rˣ} (hu : residueUnits R u = 1) :
    u ∈ (powMonoidHom n : Rˣ →* Rˣ).range := by
  obtain ⟨z, hz⟩ := exists_pow_eq_of_residue_eq_one R n hn0 hn hu
  exact ⟨z, by simpa [powMonoidHom] using hz⟩

/-- ★★★★★ **`prop:prelim-kummer-valuation`(1)（逐点判据，抽象 Hensel）**：

`u ∈ (𝒪^×)^n ⟺ ρ u ∈ (𝓀^×)^n`。

⇐ 是论文 `:1622` 的那一步（「`\bar w ∈ K^{×p}` ⟹ `w = (yz)^p`」）的一般形式：
取 `W` 提升 `w`，则 `u · W^{-n} ∈ 1+𝔪`，由 Hensel 在 `1+𝔪` 上开 `n` 次方。 -/
theorem residue_mem_pow_range_iff (n : ℕ) (hn0 : n ≠ 0) (hn : IsUnit (n : R)) (u : Rˣ) :
    residueUnits R u ∈ (powMonoidHom n : (IsLocalRing.ResidueField R)ˣ →*
        (IsLocalRing.ResidueField R)ˣ).range
      ↔ u ∈ (powMonoidHom n : Rˣ →* Rˣ).range := by
  constructor
  · -- ⇐ 方向的反向：剩余是 n 次幂 ⟹ 单位是 n 次幂
    intro h
    rw [MonoidHom.mem_range] at h ⊢
    obtain ⟨w, hw⟩ := h
    -- 提升 `w` 到单位
    obtain ⟨W, hW⟩ := exists_unit_residue_eq R w
    have hW' : residueUnits R W = w := by
      ext
      simpa [residueUnits] using hW
    -- `u · W^{-n}` 落在核里
    have hker : residueUnits R (u * (W ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hW', ← hw]
      simp [powMonoidHom]
    obtain ⟨z, hz⟩ := exists_pow_eq_of_residue_eq_one R n hn0 hn hker
    have key : u = z ^ n * W ^ n := by rw [hz]; group
    refine ⟨W * z, ?_⟩
    rw [powMonoidHom_apply, mul_pow, mul_comm (W ^ n) (z ^ n)]
    exact key.symm
  · rintro ⟨v, rfl⟩
    rw [MonoidHom.mem_range]
    exact ⟨residueUnits R v, by simp⟩

/-- ★★★★★ **论文 `prop:prelim-kummer-valuation`(1)（抽象 Hensel 版）**：
单位约化诱导同构
`𝒪_F^×/(𝒪_F^×)^p ≃* 𝓀_F^×/(𝓀_F^×)^p`。

证明 = 逐点判据 `residue_mem_pow_range_iff` 的两方向：
`N₁ ≤ comap ρ N₂`（⟸）给出 `φ̄`；反向给出 `φ̄` 单射；`ρ` 满给出 `φ̄` 满。 -/
noncomputable def unitQuotPowEquiv (n : ℕ) (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range
      ≃* (IsLocalRing.ResidueField R)ˣ ⧸
        (powMonoidHom n : (IsLocalRing.ResidueField R)ˣ →*
          (IsLocalRing.ResidueField R)ˣ).range := by
  classical
  set N₁ : Subgroup Rˣ := (powMonoidHom n : Rˣ →* Rˣ).range with hN₁
  set N₂ : Subgroup (IsLocalRing.ResidueField R)ˣ :=
    (powMonoidHom n : (IsLocalRing.ResidueField R)ˣ →*
      (IsLocalRing.ResidueField R)ˣ).range with hN₂
  have hiff : ∀ u : Rˣ, residueUnits R u ∈ N₂ ↔ u ∈ N₁ := fun u =>
    residue_mem_pow_range_iff R n hn0 hn u
  have hle : N₁ ≤ Subgroup.comap (residueUnits R) N₂ := fun u hu => (hiff u).mpr hu
  -- 单位约化满
  have hsurjρ : Function.Surjective (residueUnits R) := by
    intro w
    obtain ⟨W, hW⟩ := exists_unit_residue_eq R w
    exact ⟨W, by ext; simpa [residueUnits] using hW⟩
  -- 约化后的映射
  set φ : Rˣ ⧸ N₁ →* (IsLocalRing.ResidueField R)ˣ ⧸ N₂ :=
    QuotientGroup.map N₁ N₂ (residueUnits R) hle with hφ
  have hφmk : ∀ x : Rˣ, φ (QuotientGroup.mk x : Rˣ ⧸ N₁) =
      (QuotientGroup.mk (residueUnits R x) : _ ⧸ N₂) := fun x =>
    QuotientGroup.map_mk N₁ N₂ (residueUnits R) hle x
  have hsurj : Function.Surjective φ := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H w =>
      obtain ⟨x, rfl⟩ := hsurjρ w
      exact ⟨QuotientGroup.mk x, by rw [hφmk]⟩
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    induction z using QuotientGroup.induction_on with
    | H x =>
      have h1 : (QuotientGroup.mk (residueUnits R x) : _ ⧸ N₂) = 1 := by
        rw [← hφmk]; exact hz
      have h2 : residueUnits R x ∈ N₂ := by
        exact (QuotientGroup.eq_one_iff (N := N₂) (residueUnits R x)).mp h1
      have h3 : x ∈ N₁ := (hiff x).mp h2
      exact (QuotientGroup.eq_one_iff (N := N₁) x).mpr h3
  exact MulEquiv.ofBijective φ ⟨hinj, hsurj⟩

end AbstractHensel

/-! ## 论文层实例化：`R := ↥𝒪[F]`（`ValuativeRel` ＋ Hensel，**无完备性/无局部域**） -/

section ValuativeInstantiation

variable {F : Type} [Field F] [ValuativeRel F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]

/-- ★★★★★ **论文 `prop:prelim-kummer-valuation`(1)**，逐字口径（`F` Hensel 离散赋值域，
`p` 在 `𝒪_F` 中可逆），**无** `[IsNonarchimedeanLocalField]`、**无**完备性。

（引用核在紧随其后的逐点判据 `unit_pow_range_iff_residue_pow_range_ofF` 上——本件是它的打包形态，
故不再重复 `@source`。） -/
noncomputable def unitQuotPowEquiv_ofF (p : ℕ) (hp0 : p ≠ 0) (hp : IsUnit (p : ↥𝒪[F])) :
    𝒪[F]ˣ ⧸ (powMonoidHom p : 𝒪[F]ˣ →* 𝒪[F]ˣ).range
      ≃* 𝓀[F]ˣ ⧸ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range :=
  unitQuotPowEquiv ↥𝒪[F] p hp0 hp

/-- 同上，**逐点判据**形态（下游更好用）：`u ∈ (𝒪_F^×)^p ⟺ \bar u ∈ (𝓀_F^×)^p`。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="单位约化诱导同构 $\mathcal O_F^\times/\mathcal O_F^{\times p} \simeq K^\times/K^{\times p}$；"
theorem unit_pow_range_iff_residue_pow_range_ofF (p : ℕ) (hp0 : p ≠ 0)
    (hp : IsUnit (p : ↥𝒪[F])) (u : 𝒪[F]ˣ) :
    residueUnits ↥𝒪[F] u ∈ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range
      ↔ u ∈ (powMonoidHom p : 𝒪[F]ˣ →* 𝒪[F]ˣ).range :=
  residue_mem_pow_range_iff ↥𝒪[F] p hp0 hp u

/-- 论文 `:1622` 那一步的抽象版：`\bar w ∈ 𝓀^{×p} ⟹ w ∈ (𝒪^×)^p`。 -/
theorem unit_mem_pow_range_of_residue_mem_ofF (p : ℕ) (hp0 : p ≠ 0)
    (hp : IsUnit (p : ↥𝒪[F])) {u : 𝒪[F]ˣ}
    (h : residueUnits ↥𝒪[F] u ∈ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range) :
    u ∈ (powMonoidHom p : 𝒪[F]ˣ →* 𝒪[F]ˣ).range :=
  (unit_pow_range_iff_residue_pow_range_ofF p hp0 hp u).mp h

end ValuativeInstantiation

end L20261018

#print axioms L20261018.residue_units_eq_one_iff
#print axioms L20261018.principalUnit_mem_pow_range_of_eq_one
#print axioms L20261018.residue_mem_pow_range_iff
#print axioms L20261018.unitQuotPowEquiv
#print axioms L20261018.unitQuotPowEquiv_ofF
#print axioms L20261018.unit_pow_range_iff_residue_pow_range_ofF
#print axioms L20261018.unit_mem_pow_range_of_residue_mem_ofF
