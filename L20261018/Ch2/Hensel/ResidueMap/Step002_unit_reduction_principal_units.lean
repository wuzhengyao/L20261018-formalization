import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic

/-!
# R941：`prop:prelim-kummer-valuation` 的**第一块**机检 —— 单位约化与主单位 `p`-可除

本文件开始形式化 `raw/L20261018.tex` §2.4 的两个命题。**本块只做第一条命题**
（`prop:prelim-kummer-valuation`）里**不涉及上同调**的那半：

| 论文 | 本文件 |
|---|---|
| `:1017–1023`「群 $1+\m_F$ 称为主单位群；映射 $u\mapsto u^p$ 是该群的自同构」 | `principalUnits_le_pow_range` |
| `prop:prelim-kummer-valuation`(1)「单位约化诱导同构 $\mathcal O_F^\times/\mathcal O_F^{\times p}\simeq K^\times/K^{\times p}$」 | `unitPow_iff_residuePow`（逐点形式）＋ **`unit_pow_of_residue_pow`**（论文 `:1622`「$\bar w\in K^{\times p}$ ⟹ $w=(yz)^p$」那一步） |

## 范围决策（**硬登记**，`PROMPT-CH4` §8(乙)）

本块及后续 §2.4 形式化**在非阿基米德局部域上**进行
（`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`），
因为 TauCeti 的整套工具（`unitFiltration`／`normalizedValuation`／`kummerMap`／`localSymbol`）
**全部**建立在 `IsNonarchimedeanLocalField` 之上（见 `PowerSubgroup/Basic.lean` 的 `variable`）。

**这是对论文假设的真实缩小**：论文 `:978` 明写「完备离散赋值域是 Hensel 的，逆命题不作假设；
本节不以完备性替代 Hensel 性」。⟹ 本块的形式化是**完备情形**。
抽象 Hensel 层可用件见 `Hyp113`（`HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem`，
已在工作区机检）；把它升成完整替代是另一件事，登记为残余。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## 1. 主单位群上的 `p` 次幂映射（论文 `:1017–1023`） -/

/-- **论文 `:1017–1023`**：`p` 在整数环中可逆（⟸ `char K ≠ p`）时，
主单位群 `1+𝔪_F = unitFiltration F 1` 的每个元素都是 `p` 次幂。

论文用的是「Hensel ⟹ 唯一的主单位根」；TauCeti 的证明用单位滤过链。 -/
-- @source file=raw/L20261018.tex locator=line:1017 quote="群 $1+\mF$ 称为主单位群；映射 $u\mapsto u^p$ 是该群的自同构。"
theorem principalUnits_le_pow_range {p : ℕ} (hp : IsUnit (p : 𝒪[F])) :
    unitFiltration F 1 ≤ (powMonoidHom p : Fˣ →* Fˣ).range :=
  TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit hp

/-- 主单位可 `p` 次开方（把上面的 `≤` 写成存在形式 —— 论文证明实际使用它的形状）。 -/
theorem principalUnit_exists_pow_eq {p : ℕ} (hp : IsUnit (p : 𝒪[F])) {u : Fˣ}
    (hu : u ∈ unitFiltration F 1) : ∃ z : Fˣ, z ^ p = u := by
  have h := principalUnits_le_pow_range (F := F) hp hu
  rw [MonoidHom.mem_range] at h
  obtain ⟨z, hz⟩ := h
  exact ⟨z, by simpa [powMonoidHom] using hz⟩

/-! ## 2. `prop:prelim-kummer-valuation`(1)：单位约化检测 `p` 次幂 -/

/-- **`prop:prelim-kummer-valuation`(1)**（逐点形式）：`n` 在整数环中可逆时，
整数环的单位 `u` 是 `F` 中的 `n` 次幂 **⟺** 它的剩余是剩余域中的 `n` 次幂。

论文的表述是「单位约化诱导同构 $\mathcal O_F^\times/\mathcal O_F^{\times p}
\simeq K^\times/K^{\times p}$」；这条 iff 正是该同构的**逐点判据**
（左 = 在 `𝒪^×` 中的 `p` 次幂，右 = 在 `𝓀^×` 中的 `p` 次幂）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="单位约化诱导同构 $\mathcal O_F^\times/\mathcal O_F^{\times p} \simeq K^\times/K^{\times p}$；"
theorem unitPow_iff_residuePow {n : ℕ} (hn : IsUnit (n : 𝒪[F])) (u : 𝒪[F]ˣ) :
    (Units.map (Subring.subtype 𝒪[F] : 𝒪[F] →* F) u ∈ (powMonoidHom n : Fˣ →* Fˣ).range) ↔
      (Units.map (IsLocalRing.residue 𝒪[F] : 𝒪[F] →* 𝓀[F]) u ∈
        (powMonoidHom n : 𝓀[F]ˣ →* 𝓀[F]ˣ).range) :=
  TauCeti.unitsMap_subtype_mem_range_powMonoidHom_iff hn u

/-- **论文 `:1622` 的那一步**（`lem:ramified-vanishing` 证明的最后一行）：
单位 `w` 的剩余 `\bar w` 是剩余域中的 `p` 次幂 ⟹ `w` 本身是 `F` 中的 `p` 次幂
（论文写 $w=(yz)^p$，用 Hensel ＋ 主单位 `p`-可除）。

这是 `unitPow_iff_residuePow` 的 `⇐` 方向，正是 T3 第五步所需的形态。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="因此 $\bar w\in K^{\times p}$。选择 $y\in\mathcal O_F^\times$，使 $\bar w=\bar y^{\,p}$，则 $wy^{-p}\in1+\mathfrak m_F$。"
theorem unit_pow_of_residue_pow {p : ℕ} (hp : IsUnit (p : 𝒪[F])) (u : 𝒪[F]ˣ)
    (h : Units.map (IsLocalRing.residue 𝒪[F] : 𝒪[F] →* 𝓀[F]) u ∈
      (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range) :
    Units.map (Subring.subtype 𝒪[F] : 𝒪[F] →* F) u ∈ (powMonoidHom p : Fˣ →* Fˣ).range :=
  (unitPow_iff_residuePow (F := F) hp u).mpr h

end L20261018

#print axioms L20261018.principalUnits_le_pow_range
#print axioms L20261018.principalUnit_exists_pow_eq
#print axioms L20261018.unitPow_iff_residuePow
#print axioms L20261018.unit_pow_of_residue_pow
