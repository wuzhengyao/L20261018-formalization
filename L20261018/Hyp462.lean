import Hyp163
import Hyp162

/-!
# S40 R1：`𝒪^×/(𝒪^×)^p ≅ κ^×/(κ^×)^p` 在**论文层级**（Hensel，不要完备性）

## 1. 本轮要裁定的事（`PROMPT-S40` §⑦.14 ＝ "开工第一件要裁定的事"）

`PROMPT-S40` §⑦.14（承 `RECON-R3` §51／§78）登记了一条张力：

> `ker v̄ = 𝒪^×/(𝒪^×)^p ≅ μ_p × κ^×/(κ^{×p})`（Teichmüller 分解），
> **严格大于**不分歧部分 `im(infl₁) = κ^×/(κ^{×p})`，多出的 `μ_p` 支**是分歧的**。

并推论「`d` 的定义域/目标域究竟是 `ker v̄` 还是 `H¹(κ)`；若是后者，`Hyp432` 需重述
—— 这可能是 B 一直做不出来的真正原因」。

## 2. 本轮的裁定：**张力不存在；`ker v̄ = H¹(κ, μ_p)`**

论文 `raw/L20261018.tex:998–1006` 自己写：

> `x = inf(x₀) + m(π)`, `x₀ ∈ H¹(K, μ_p)`, `m ∈ F_p`
> 「其中**不分歧子空间 `ker v̄`** 是典范的」

即 **`ker v̄ = im(inf) = H¹(K, μ_p)`**，不是 `μ_p × H¹(K)`。论文 `:1050` 的两条值公式
`∂₂((u)∪(π)) = (ū)` 也落在 `K^×/K^{×p}`。

**为什么 `μ_p × κ^×/κ^{×p}` 不对**：Teichmüller 分解 `𝒪^× ≅ μ(κ) × (1+𝔪)` 的 `1+𝔪` 段
在 `p` 为**单位**时 `p`-可除（论文 `:1017–1023`；`Hyp163.principalUnit_pow_surjective_of_hensel`），
故 `𝒪^×/(𝒪^×)^p ≅ μ(κ)/μ(κ)^p`。而 `μ(κ) ⊂ κ^×` ⟹ 该 `μ_p` 是 `κ^×/κ^{×p}` 的
**子群**，不是并列的直和项。`μ_p × κ^×/κ^{×p}` 只在 **`p` 非单位**（剩余特征 `= p`）时成立，
而全战役带 `hpF : IsUnit (p : F)`（论文 `char K ≠ p`），**排除**该情形。

**⟹ `Hyp432` 的等价形式（目标域 `ker v̄`）是正确形式，无需重述；B 的缺口与此无关。**

## 3. 本轮机检的数学内容

论文 `prop:prelim-kummer-valuation`(1)：单位约化诱导同构 `𝒪_F^×/𝒪_F^{×p} ≃ K^×/K^{×p}`。

`Hyp114.unitPow_iff_residuePow` 只在 `[IsNonarchimedeanLocalField F]`（完备＋有限剩余）下
机检，其 `⇒` 方向被 `Hyp163` §1 登记为"未移植"（"需要 `v(u) = 1 ⟺ u ∈ 𝒪^×` 的幂律刻画"）。

本轮**不用** `Hyp114` 的赋值刻画，只用赋值本身的单调性（`pow_le_one_iff`）：

| 声明 | 内容 | 层级 |
|---|---|---|
| `mem_subring_of_pow_mem` | `w^p ∈ 𝒪`（`p ≠ 0`）⟹ `w ∈ 𝒪` | 纯赋值环 |
| `exists_unit_pow_eq` | `u ∈ 𝒪^×` 且 `u = w^p`（`w ∈ F^×`）⟹ `u = v^p`（`v ∈ 𝒪^×`） | 纯估值环 |
| `residue_pow_of_pow` | 同上 ⟹ `residue u` 是 `κ^×` 中的 `p` 次幂 | 纯估值环 |
| **`unit_pow_iff_residue_pow_of_hensel`** | **`𝒪^×/(𝒪^×)^p ≅ κ^×/(κ^×)^p`（逐点，双向）** | **Hensel**（无完备性、无有限剩余） |

`⇐` 方向 ＝ `Hyp163.unit_pow_of_residue_pow_of_hensel`（不重做）；
本轮补 `⇒` ⟹ **双向闭合**，并把 `Hyp114` 的 `IsNonarchimedeanLocalField` 假设降到
论文自己的 Hensel 假设（`raw/L20261018.tex:978`：「完备离散赋值域是 Hensel 的，
逆命题不作假设；本节不以完备性替代 Hensel 性」）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-! ## 1. 纯赋值环事实：`w^p ∈ 𝒪` ⟹ `w ∈ 𝒪` -/

/-- **估值环在开 `p` 次方下封闭**：`p ≠ 0` 且 `w ^ p ∈ 𝒪[F]` ⟹ `w ∈ 𝒪[F]`。

用赋值本身：`𝒪[F] = (valuation F).integer = {x | v x ≤ 1}`，而 `v (w^p) = (v w)^p`；
`(v w)^p ≤ 1 ⟹ v w ≤ 1`（`pow_le_one_iff`）。 -/
theorem mem_subring_of_pow_mem {p : ℕ} (hp : p ≠ 0) {w : F}
    (hw : w ^ p ∈ 𝒪[F]) : w ∈ 𝒪[F] := by
  rw [Valuation.mem_integer_iff] at hw ⊢
  rw [Valuation.map_pow] at hw
  exact (pow_le_one_iff hp).mp hw

/-! ## 2. `𝒪^×` 中的 `p` 次幂 ⟹ 有 `𝒪^×` 中的 `p` 次根 -/

/-- **`u ∈ 𝒪[F]^×` 且 `u` 是 `F` 中的 `p` 次幂 ⟹ `u` 是 `𝒪[F]^×` 中的 `p` 次幂**。

由 `mem_subring_of_pow_mem` 得 `w ∈ 𝒪[F]`；`⟨w,_⟩^p = u` 是单位 ⟹ `⟨w,_⟩` 是单位。 -/
theorem exists_unit_pow_eq {p : ℕ} (hp : p ≠ 0) {u : 𝒪[F]ˣ} {w : Fˣ}
    (hw : ((u : ↥𝒪[F]) : F) = (w : F) ^ p) :
    ∃ v : 𝒪[F]ˣ, ((v : ↥𝒪[F]) : F) ^ p = ((u : ↥𝒪[F]) : F) := by
  classical
  have hmem : (w : F) ∈ 𝒪[F] := by
    refine mem_subring_of_pow_mem (F := F) hp ?_
    rw [← hw]
    exact Subtype.coe_prop _
  -- `⟨w, hmem⟩ ^ p = u` 作为 `𝒪[F]` 的元素
  have hpow : ((⟨(w : F), hmem⟩ : ↥𝒪[F]) ^ p) = ((u : ↥𝒪[F])) := by
    apply Subtype.ext
    show ((w : F)) ^ p = ((u : ↥𝒪[F]) : F)
    rw [hw]
  have hunit : IsUnit (⟨(w : F), hmem⟩ : ↥𝒪[F]) :=
    (isUnit_pow_iff hp).mp (by rw [hpow]; exact u.isUnit)
  refine ⟨hunit.unit, ?_⟩
  show (((hunit.unit : ↥𝒪[F])) : F) ^ p = ((u : ↥𝒪[F]) : F)
  rw [IsUnit.unit_spec hunit]
  exact (hw).symm ▸ rfl

/-! ## 3. 剩余域侧：`⇒` 方向 -/

/-- **`prop:prelim-kummer-valuation`(1) 的 `⇒` 方向**：若 `u ∈ 𝒪^×` 是 `F` 中的 `p` 次幂，
则 `residue u` 是 `𝓀[F]` 中的 `p` 次幂。 -/
-- @source file=raw/L20261018.tex locator=line:992 quote="\item 单位约化诱导同构"
theorem residue_pow_of_pow {p : ℕ} (hp : p ≠ 0) (u : 𝒪[F]ˣ)
    (hpow : Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) u ∈
      (powMonoidHom p : Fˣ →* Fˣ).range) :
    Units.map (IsLocalRing.residue ↥𝒪[F] : ↥𝒪[F] →* 𝓀[F]) u ∈
      (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range := by
  rw [MonoidHom.mem_range] at hpow ⊢
  obtain ⟨w, hw⟩ := hpow
  have hw' : ((u : ↥𝒪[F]) : F) = (w : F) ^ p := by
    have h := congrArg (fun z : Fˣ => (z : F)) hw
    simpa [powMonoidHom] using h.symm
  obtain ⟨v, hv⟩ := exists_unit_pow_eq (F := F) hp (u := u) (w := w) hw'
  refine ⟨Units.map (IsLocalRing.residue ↥𝒪[F] : ↥𝒪[F] →* 𝓀[F]) v, ?_⟩
  have hv' : ((v : ↥𝒪[F]) ^ p) = (u : ↥𝒪[F]) := Subtype.ext hv
  apply Units.ext
  show IsLocalRing.residue ↥𝒪[F] ((v : ↥𝒪[F]) ^ p) = IsLocalRing.residue ↥𝒪[F] ((u : ↥𝒪[F]))
  rw [hv']

/-! ## 4. 双向闭合（论文 `prop:prelim-kummer-valuation`(1)，**论文层级**） -/

/-- ★★★★★ **`𝒪_F^×/𝒪_F^{×p} ≅ K^×/K^{×p}`（逐点）在论文层级机检**。

论文 `raw/L20261018.tex:1017–1023` ＋ `prop:prelim-kummer-valuation`(1)。
假设只有 `[HenselianRing 𝒪[F] 𝔪_F]` ＋ `IsUnit (p : 𝒪[F])`：
**不要完备性、不要有限剩余域**（对比 `Hyp114.unitPow_iff_residuePow` 的
`[IsNonarchimedeanLocalField F]`）。

* `⇐` ＝ `Hyp163.unit_pow_of_residue_pow_of_hensel`（论文 `:1622` 那一行）；
* `⇒` ＝ 本文件 `residue_pow_of_pow`（本轮新补，`Hyp163` §1 登记为未移植）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="单位约化诱导同构"
theorem unit_pow_iff_residue_pow_of_hensel
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])] {p : ℕ} (hp : IsUnit (p : ↥𝒪[F]))
    (u : 𝒪[F]ˣ) :
    Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) u ∈ (powMonoidHom p : Fˣ →* Fˣ).range ↔
      Units.map (IsLocalRing.residue ↥𝒪[F] : ↥𝒪[F] →* 𝓀[F]) u ∈
        (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hp.ne_zero (Nat.cast_zero (R := ↥𝒪[F]))
  exact ⟨residue_pow_of_pow (F := F) hp0 u, unit_pow_of_residue_pow_of_hensel (F := F) hp u⟩

end L20261018

#print axioms L20261018.mem_subring_of_pow_mem
#print axioms L20261018.exists_unit_pow_eq
#print axioms L20261018.residue_pow_of_pow
#print axioms L20261018.unit_pow_iff_residue_pow_of_hensel
