import Hyp388

/-!
# R1303（S37 第 11 轮）：**(R2) 的忠实形态** —— `residueSpan ⊆ ker res`，而非「字面为零」

## 为什么必须改

`Hyp383`／`Hyp385` 用的是 `UnitsCupVanish`（单位杯积**字面为零**）。收尾自审发现它
**⟺ `H²(κ,μ_p) = 0`**（推理：单位 Kummer 类 `(u) = inf(ū)`（论文 `prop:prelim-kummer-valuation` (1)）；
杯积与膨胀相容；`inf` 单射（GS 6.8.8 分裂正合列））。该条件对有限 `κ` 真，对 `κ = ℚ`
（`F = ℚ((π))`，仍在论文设定内）**假**。⟹ 那不是论文 (R2) 的忠实对应。

GS 的 (R2) 只要求 `∂₂((u)∪(w)) = 0`，即 **`residueSpan ⊆ ker ∂₂`**。

## 本文件的两个结果

### A. 抽象层：**(R2) 是定理，不是假设**

`ResidueCupData`（`Hyp109`）**已经带 `res` 与三条驯符号事实**（`tame_uu`／`tame_u_pi`／`tame_pi_u`）。
故在抽象层，`TameResidueFacts`（构造 `d` 所需的全部）**只差 (R1) `phi_injective`**：

| 声明 | 内容 |
|---|---|
| **`ker_val_eq_range_infl`** | `ker val = range infl`（由 `split` ＋ `val_infl` ＋ `val_pi`） |
| **`residueSpan_le_ker_res`** | ★★★★ `residueSpan ≤ ker res`（由 `tame_uu`）—— **这就是 (R2)** |
| **`disjoint_range_residuePhi`** | ★★★★ `Disjoint (range Φ) residueSpan`（由上面两条 ＋ `tame_u_pi`） |
| **`tameResidueFacts_of_data`** | ★★★★★ `TameResidueFacts`，**唯一输入 = `phi_injective`** |

### B. 具体层（Galo 载体）：忠实 (R2') 取代 `UnitsCupVanish`

具体载体没有 `res`（它正是要构造的 `d`），故 (R2) 必须以**剩余域侧载体**陈述：

```
R2′ :  ∃ (H2K) (infl₂ : H2K →ₗ[k] H2),
         residueSpan ≤ range infl₂  ∧  Disjoint (range Φ) (range infl₂)
```

| 声明 | 内容 |
|---|---|
| **`disjoint_of_faithfulR2`** | `R2′ ⟹ Disjoint (range Φ) residueSpan` |
| **`exists_residueMap_of_faithfulR2`** | ★★★★★ 论文 (1) 的 `∃d`（两条性质），**模 `R2′` ＋ (R1)** |
| `faithfulR2_of_span_eq_bot` | **回归对照**：`residueSpan = ⊥`（旧 `UnitsCupVanish` 路线）是 `R2′` 取 `infl₂ = 0` 的特例 |

⟹ 论文 (1) 的忠实缺口从「`UnitsCupVanish`（一般情形为假）」改为
「`R2′`（= 剩余域侧 `H²` 载体 ＋ 膨胀 ＋ 两条可证事实）」—— 这**正是** `GS68-LEDGER.md` 的 R2/G2
（载体层），与 S2 同一个缺口，而非一条错误的假设。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section Abstract

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {VK : Type*} [AddCommGroup VK] [Module k VK]
-- 库内 `ResidueCupData.ker_val_eq_range_infl`（`Hyp112:45`）带 `[NeZero 2]` 隐式参数
variable [NeZero (2 : k)]

/-- ★★★★ **(R2)**：单位类之间的杯积落在 `ker res` 里（GS 的 `∂₂((u)∪(w)) = 0`）。
由 `tame_uu` ＋ `ker val = range infl`（`Hyp112.ResidueCupData.ker_val_eq_range_infl`）得到。
**这是 (R2) 的忠实形态**：只要求落在核里，不要求字面为零。 -/
theorem residueSpan_le_ker_res (D : ResidueCupData k V H2 VK) :
    residueSpan D.cup D.val ≤ LinearMap.ker D.res := by
  rw [residueSpan, Submodule.span_le]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  change D.res (D.cup (y : V) (z : V)) = 0
  obtain ⟨y₀, hy₀⟩ := LinearMap.mem_range.mp (by
    rw [← ResidueCupData.ker_val_eq_range_infl (D := D)]; exact y.2)
  obtain ⟨z₀, hz₀⟩ := LinearMap.mem_range.mp (by
    rw [← ResidueCupData.ker_val_eq_range_infl (D := D)]; exact z.2)
  rw [← hy₀, ← hz₀]
  exact D.tame_uu y₀ z₀

/-- ★★★★ **不相交性**：`range Φ` 与 `residueSpan` 不相交。
由 (R2) ＋ `tame_u_pi`（`res ∘ Φ` 是 `y ↦ y₀`，故 `Φ y ∈ ker res ⟹ y₀ = 0 ⟹ y = 0`）。 -/
theorem disjoint_range_residuePhi (D : ResidueCupData k V H2 VK) :
    Disjoint (LinearMap.range (residuePhi D.cup D.val D.pi))
      (residueSpan D.cup D.val) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨y, rfl⟩ := hx
  rw [residuePhi_apply]
  obtain ⟨y₀, hy₀⟩ := LinearMap.mem_range.mp (by
    rw [← ResidueCupData.ker_val_eq_range_infl (D := D)]; exact y.2)
  have h1 : D.res (D.cup (y : V) D.pi) = y₀ := by
    rw [← hy₀]; exact D.tame_u_pi y₀
  have h2 : D.res (D.cup (y : V) D.pi) = 0 := residueSpan_le_ker_res (D := D) hx'
  rw [h1] at h2
  simp only [← hy₀, h2, map_zero, LinearMap.zero_apply]

/-- ★★★★★ **抽象层：(R2) 不再是假设** —— `TameResidueFacts` 的唯一输入是 (R1) `phi_injective`。 -/
theorem tameResidueFacts_of_data (D : ResidueCupData k V H2 VK)
    (hR1 : Function.Injective (residuePhi D.cup D.val D.pi)) :
    TameResidueFacts D.cup D.val D.pi :=
  ⟨hR1, disjoint_range_residuePhi (D := D)⟩

end Abstract

section Concrete

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- **回归对照**：`residueSpan = ⊥`（旧 `UnitsCupVanish` 路线）是忠实 (R2′) 取 `infl₂ = 0` 的特例。 -/
theorem faithfulR2_of_span_eq_bot (hpF : IsUnit (p : F))
    (hspan : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) = ⊥) :
    residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF) ≤
      LinearMap.range (0 : ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hpF)) →ₗ[ZMod p]
        GaloBase.H2 F p) := by
  rw [hspan, LinearMap.range_zero]

/-- ★★★★★ **不相交性由忠实 (R2′) 推出**（`Disjoint.mono_right`）。 -/
theorem disjoint_of_faithfulR2 {ζ : F} (_hζ : IsPrimitiveRoot ζ p) (hpF : IsUnit (p : F))
    {HK2 : Type*} [AddCommGroup HK2] [Module (ZMod p) HK2]
    (infl₂ : HK2 →ₗ[ZMod p] GaloBase.H2 F p)
    (hspan : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) ≤ LinearMap.range infl₂)
    (hdisj : Disjoint (LinearMap.range
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π))) (LinearMap.range infl₂)) :
    Disjoint (LinearMap.range
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π)))
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)) :=
  hdisj.mono_right hspan

/-- ★★★★★ **论文 (1) 的 `∃d`，模忠实 (R2′)**（取代 `Hyp383` 的 `UnitsCupVanish`）。

输入只有两条：
* **(R1)** `residuePhi` 单射 —— 由库内 `residuePhi_injective_t1`（`Hyp319`）供给，**无有限剩余域**；
* **(R2′)** 单位杯积落在某个「剩余域侧膨胀」`infl₂` 的像里（`hspan`），且该像与 `range Φ` 不相交（`hdisj`）。

这正是 GS `prop:prelim-residue` (1) 的**忠实**条件：GS 的 (R2) 只要求 `∂₂((u)∪(w)) = 0`
（即 `(u)∪(w) ∈ ker ∂₂ = im(inf₂)`），**不要求字面为零**。 -/
theorem exists_residueMap_of_faithfulR2 {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    {HK2 : Type*} [AddCommGroup HK2] [Module (ZMod p) HK2]
    (infl₂ : HK2 →ₗ[ZMod p] GaloBase.H2 F p)
    (hspan : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) ≤ LinearMap.range infl₂)
    (hdisj : Disjoint (LinearMap.range
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π))) (LinearMap.range infl₂)) :
    ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
      (∀ y z : VKG F p v hpF,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0) ∧
      (∀ y : VKG F p v hpF,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
          (KummerBridge.kummerClass F p hpF π)) = y) :=
  (exists_residueMap_iff_tameResidueFacts (GaloBase.cup (K := F) (p := p))
    (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)
    (valLinOf_pi (F := F) (p := p) v hpF hπ)
    (GaloBase.cup_skew (K := F) (p := p))).mpr
    ⟨residuePhi_injective_t1 (F := F) (p := p) hp hζ hv hπ hp2,
      disjoint_of_faithfulR2 (F := F) (p := p) (v := v) (π := π) hζ hpF infl₂ hspan hdisj⟩

end Concrete

end L20261018

#print axioms L20261018.residueSpan_le_ker_res
#print axioms L20261018.disjoint_range_residuePhi
#print axioms L20261018.tameResidueFacts_of_data
#print axioms L20261018.faithfulR2_of_span_eq_bot
#print axioms L20261018.disjoint_of_faithfulR2
#print axioms L20261018.exists_residueMap_of_faithfulR2
