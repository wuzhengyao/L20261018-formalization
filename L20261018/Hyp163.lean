import L20261018.Hyp161
import L20261018.Hyp162
import L20261018.Hyp113
import TauCeti.RingTheory.Henselian.Basic

/-!
# R1015：§2.4 的**主单位层**脱离完备性 ＋ **(R1) 归约到 Kummer 类形态**

## 1. 论文 `:1017–1023` 与 `:1622` 在论文层级（Hensel，不假设完备性）

论文 `raw/L20261018.tex:1017–1023`：

> 群 $1+\mF$ 称为主单位群；映射 $u\mapsto u^p$ 是该群的自同构。
> 事实上，对 $u\in1+\mF$，多项式 $X^p-u$ 在剩余域中有单根 $1$，Hensel 引理给出唯一的主单位根。

以及 4.2 证明末行（`:1622`）：

> 因此 $\bar w\in K^{\times p}$。选择 $y\in\mathcal O_F^\times$，使 $\bar w=\bar y^{\,p}$，则 $wy^{-p}\in1+\mathfrak m_F$。
> 主单位的 $p$-可除性给出 $z\in1+\mathfrak m_F$，使 $wy^{-p}=z^p$。于是 $w=(yz)^p$。

`Hyp113` 已把「Hensel 那半」包成 `principalUnit_pow_surjective`，`Hyp114` 把这两步在
**`IsNonarchimedeanLocalField`**（完备＋有限剩余）上机检。本轮把两者的**完备性去掉**：
唯一需要的输入是 **`𝒪[F]` 对 `𝔪_F` 是 Hensel 环**（`[HenselianRing 𝒪[F] 𝔪_F]` ＝论文的「Hensel 性」）。
证明只用「把 `\bar u` 的 `p` 次根提升成 `𝒪[F]ˣ` 的元素 ＋ 主单位 `p`-可除性」，**不经过完备化**。

| 声明 | 内容 |
|---|---|
| `principalUnit_pow_surjective_of_hensel` | `w ≡ 1 mod 𝔪` ⟹ `∃ a, a^p = w ∧ a ≡ 1 mod 𝔪` |
| **`unit_pow_of_residue_pow_of_hensel`** | **`\bar u` 是 `p` 次幂 ⟹ `u` 是 `p` 次幂**（论文 `:1622`，论文层级） |

> **`Hyp114.unitPow_iff_residuePow` 的 `⇒` 方向未移植**：它需要 `v(u) = 1 ⟺ u ∈ 𝒪^×` 的幂律刻画；
> 论文 `:1622` 只用 `⇐`。登记为写作义务，不阻塞本轮的归约。

## 2. **(R1) 的 Kummer 类形态**（范数路线的入口）

`Hyp161` 的两条剩余事实中，(R1) 是 `Φ := ∪(·,π)` 在 `ker \bar v` 上单射。由
`KummerV.kummerClass_surjective`（类无关）与 `valLinOf_kummerClass`，(R1) **等价于**：

> 对每个 `v`-整单位 `u`（`v(u) ≡ 0 mod p`），`(u) ∪ (π) = 0 ⟹ (u) = 0`。

这正是 **符号–范数判据**（`ClassFieldTheory.cup_kummerClass_eq_zero_iff_mem_normGroup`，
"K need not be a local field"）作用的形式：`(u)∪(π) = 0 ↔ u ∈ N_{F(π^{1/p})/F}`，
故 (R1) ⟺ 「`N_{F(π^{1/p})/F}(L^×) ∩ 𝒪_F^× = F^{×p}`」。本文件把该归约**机检**
（`residuePhi_injective_iff_kummer`），下一轮的数学目标就是这条范数刻画。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

/-! ## 1. 主单位层的论文层级版本 -/

section Hensel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- **主单位的 `p`-可除（论文 `:1017–1023`，论文层级）**：`Hensel 性` 作假设，不要完备性。 -/
-- @source file=raw/L20261018.tex locator=line:1017 quote="群 $1+\mF$ 称为主单位群；映射 $u\mapsto u^p$ 是该群的自同构。"
theorem principalUnit_pow_surjective_of_hensel [HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F])]
    {p : ℕ} (hp : IsUnit (p : 𝒪[F])) {w : 𝒪[F]} (hw : w - 1 ∈ IsLocalRing.maximalIdeal 𝒪[F]) :
    ∃ a : 𝒪[F], a ^ p = w ∧ a - 1 ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
  TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem
    (I := IsLocalRing.maximalIdeal 𝒪[F]) (J := IsLocalRing.maximalIdeal 𝒪[F]) le_rfl hp hw

/-- 单位 `u` 的剩余是 `1` 时 `u - 1 ∈ 𝔪_F`（`residue` 的核刻画）。 -/
theorem sub_one_mem_maximalIdeal_of_residue_eq_one {u : 𝒪[F]ˣ}
    (h : IsLocalRing.residue 𝒪[F] (u : 𝒪[F]) = 1) : (u : 𝒪[F]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  have h0 : IsLocalRing.residue 𝒪[F] ((u : 𝒪[F]) - 1) = 0 := by
    rw [map_sub, h, map_one, sub_self]
  exact (IsLocalRing.residue_eq_zero_iff _).mp h0

/-- **论文 `:1622` 在论文层级**：单位 `u` 的剩余是 `p` 次幂 ⟹ `u` 本身是 `F` 中的 `p` 次幂。

与 `Hyp114` 同构的证明，但完备性换成 `[HenselianRing 𝒪[F] 𝔪_F]`：
`\bar u = \bar y^p` 提升成 `y`，`u y^{-p} = 1 + t`（`t ∈ 𝔪`）由主单位 `p`-可除性开方。 -/
-- @source file=raw/L20261018.tex locator=line:1622 quote="因此 $\bar w\in K^{\times p}$。选择 $y\in\mathcal O_F^\times$，使 $\bar w=\bar y^{\,p}$，则 $wy^{-p}\in1+\mathfrak m_F$。"
theorem unit_pow_of_residue_pow_of_hensel [HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F])]
    {p : ℕ} (hp : IsUnit (p : 𝒪[F])) (u : 𝒪[F]ˣ)
    (h : Units.map (IsLocalRing.residue 𝒪[F] : 𝒪[F] →* 𝓀[F]) u ∈ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range) :
    Units.map (Subring.subtype 𝒪[F] : 𝒪[F] →* F) u ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  classical
  obtain ⟨y, hy⟩ := h
  -- 把 `y : 𝓀[F]ˣ` 提升成 `𝒪[F]ˣ` 的元素
  obtain ⟨y₀, hy₀⟩ := IsLocalRing.residue_surjective (y : 𝓀[F])
  have hy₀ne : y₀ ∉ IsLocalRing.maximalIdeal 𝒪[F] := by
    intro hmem
    have hz : IsLocalRing.residue 𝒪[F] y₀ = 0 := (IsLocalRing.residue_eq_zero_iff y₀).mpr hmem
    rw [hy₀] at hz
    exact Units.ne_zero y hz
  have hy₀u : IsUnit y₀ := (IsLocalRing.notMem_maximalIdeal).mp hy₀ne
  let y' : 𝒪[F]ˣ := hy₀u.unit
  have hy' : Units.map (IsLocalRing.residue 𝒪[F] : 𝒪[F] →* 𝓀[F]) y' = y := by
    ext
    show IsLocalRing.residue 𝒪[F] (y' : 𝒪[F]) = (y : 𝓀[F])
    rw [show (y' : 𝒪[F]) = y₀ from IsUnit.unit_spec hy₀u, hy₀]
  -- `u * (y'^p)⁻¹` 的剩余是 `1`
  have hone : Units.map (IsLocalRing.residue 𝒪[F] : 𝒪[F] →* 𝓀[F]) (u * (y' ^ p)⁻¹) = 1 := by
    have hpow : (y : 𝓀[F]ˣ) ^ p
        = Units.map (IsLocalRing.residue 𝒪[F] : 𝒪[F] →* 𝓀[F]) u := hy
    rw [map_mul, map_inv, map_pow, hy', hpow]
    exact mul_inv_cancel _
  have hval1 : IsLocalRing.residue 𝒪[F] ((u * (y' ^ p)⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) = 1 := by
    simpa using congrArg (fun z : 𝓀[F]ˣ => (z : 𝓀[F])) hone
  have hmem : ((u * (y' ^ p)⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
    sub_one_mem_maximalIdeal_of_residue_eq_one hval1
  -- 主单位 `p`-可除
  obtain ⟨a, ha, ha1⟩ := principalUnit_pow_surjective_of_hensel (F := F) (p := p) hp hmem
  -- `a` 是单位
  have ha_ne : a ∉ IsLocalRing.maximalIdeal 𝒪[F] := by
    intro hamem
    have h1 : (1 : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have hsub : a - (a - 1) ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
        Ideal.sub_mem _ hamem ha1
      simpa using hsub
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).ne_top
      ((Ideal.eq_top_iff_one (IsLocalRing.maximalIdeal 𝒪[F])).mpr h1)
  have hau : IsUnit a := (IsLocalRing.notMem_maximalIdeal).mp ha_ne
  let z : 𝒪[F]ˣ := hau.unit
  have hzval : (z : 𝒪[F]) = a := IsUnit.unit_spec hau
  have hzp : z ^ p = u * (y' ^ p)⁻¹ := by
    ext
    rw [Units.val_pow_eq_pow_val, hzval, ha]
  have hmain : u = (z * y') ^ p := by
    rw [mul_pow, hzp, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨Units.map (Subring.subtype 𝒪[F] : 𝒪[F] →* F) (z * y'), ?_⟩
  show (Units.map (Subring.subtype 𝒪[F] : 𝒪[F] →* F) (z * y')) ^ p
      = Units.map (Subring.subtype 𝒪[F] : 𝒪[F] →* F) u
  rw [← map_pow, hmain]

end Hensel

/-! ## 2. (R1) 的 Kummer 类形态（范数路线的入口） -/

section KummerForm

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **(R1) 的 Kummer 类形态**：`Φ := ∪(·,π)` 在 `ker \bar v` 上单射 **⟺**
「每个 `v`-整单位类的杯积消失 ⟹ 该 Kummer 类消失」。

右端正是符号–范数判据（`cup_kummerClass_eq_zero_iff_mem_normGroup`）作用的形式：
`(u)∪(π)=0 ↔ u ∈ N_{F(π^{1/p})}`。 -/
theorem residuePhi_injective_iff_kummer (hp : IsUnit (p : F))
    (v : Fˣ →* Multiplicative ℤ) (π : Fˣ) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π)) ↔
      ∀ u : Fˣ, valOfUnitOf (p := p) v u = 0 →
        GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp u)
          (KummerBridge.kummerClass F p hp π) = 0 →
        KummerBridge.kummerClass F p hp u = 0 := by
  constructor
  · -- (R1) ⟹ Kummer 形态
    intro hinj u hu hcup
    have hmem : valLinOf (F := F) (p := p) v hp (KummerBridge.kummerClass F p hp u) = 0 := by
      rw [valLinOf_kummerClass]
      exact hu
    have hEq : residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hp)
        (KummerBridge.kummerClass F p hp π) (⟨KummerBridge.kummerClass F p hp u, hmem⟩) =
        residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hp)
          (KummerBridge.kummerClass F p hp π) ⟨0, map_zero _⟩ := by
      rw [residuePhi_apply, residuePhi_apply, hcup]
      simp
    exact congrArg Subtype.val (hinj hEq)
  · -- Kummer 形态 ⟹ (R1)
    intro hk y z hyz
    obtain ⟨a, ha⟩ := KummerV.kummerClass_surjective (F := F) (p := p) hp (y : GaloBase.V F p)
    obtain ⟨b, hb⟩ := KummerV.kummerClass_surjective (F := F) (p := p) hp (z : GaloBase.V F p)
    have hya : valOfUnitOf (p := p) v a = 0 := by
      rw [← valLinOf_kummerClass (F := F) (p := p) v hp a, ha]
      exact y.2
    have hyb : valOfUnitOf (p := p) v b = 0 := by
      rw [← valLinOf_kummerClass (F := F) (p := p) v hp b, hb]
      exact z.2
    -- `(a) ∪ (π) = (b) ∪ (π)`
    have hcup_eq : GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
        (KummerBridge.kummerClass F p hp π)
        = GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp b)
          (KummerBridge.kummerClass F p hp π) := by
      rw [residuePhi_apply, residuePhi_apply] at hyz
      rw [← ha, ← hb] at hyz
      exact hyz
    -- `a * b⁻¹` 的 Kummer 形态
    have hinv : valOfUnitOf (p := p) v b⁻¹ = -valOfUnitOf (p := p) v b := by
      have h1 : valOfUnitOf (p := p) v (b⁻¹ * b) = 0 := by
        rw [inv_mul_cancel]
        exact valOfUnitOf_one (p := p) v
      rw [valOfUnitOf_mul] at h1
      exact eq_neg_iff_add_eq_zero.mpr h1
    have hvalab : valOfUnitOf (p := p) v (a * b⁻¹) = 0 := by
      rw [valOfUnitOf_mul, hinv, hyb, neg_zero, add_zero]
      exact hya
    have hsplit : KummerBridge.kummerClass F p hp (a * b⁻¹)
        = KummerBridge.kummerClass F p hp a - KummerBridge.kummerClass F p hp b := by
      rw [KummerV.kummerClass_mul, KummerV.kummerClass_inv, sub_eq_add_neg]
    have hcupab : GaloBase.cup (K := F) (p := p)
        (KummerBridge.kummerClass F p hp (a * b⁻¹))
        (KummerBridge.kummerClass F p hp π) = 0 := by
      rw [hsplit, map_sub, LinearMap.sub_apply, hcup_eq, sub_self]
    have hab : KummerBridge.kummerClass F p hp a = KummerBridge.kummerClass F p hp b := by
      have h := hk (a * b⁻¹) hvalab hcupab
      rw [hsplit] at h
      exact sub_eq_zero.mp h
    apply Subtype.ext
    show (y : GaloBase.V F p) = (z : GaloBase.V F p)
    rw [← ha, ← hb, hab]

end KummerForm

end L20261018

#print axioms L20261018.principalUnit_pow_surjective_of_hensel
#print axioms L20261018.unit_pow_of_residue_pow_of_hensel
#print axioms L20261018.residuePhi_injective_iff_kummer
