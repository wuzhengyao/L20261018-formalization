import L20261018.Hyp382
import L20261018.Hyp344

/-!
# R1297（S37 第 5 轮）：`prop:prelim-residue` (1) 的**单一具名假设**分解

## 问题：`[Finite (ResidueField)]` 到底从哪里进来？

论文 `prop:prelim-residue` 声称对**任意** Hensel 离散赋值域成立，而本战役的
`exists_residueMap_of_finite`（`Hyp344`）带 `[Finite (𝓀[F])]`。本轮实测（`Hyp321` 去掉该实例后
重编译）表明：**整条证明链只有两处需要它**，且两处都来自同一个引理 `Hyp302.unitsCupVanish`：

```text
tameResidueFacts_Galo_noBridge_of_hζ   ← unitsCupVanish
exists_henselResidueData_noBridge      ← unitsCupVanish
```

其余全部（`residueSpan_Galo_eq_bot_of_muNRep'`、`residueSpan_eq_bot_of_units`、
`residuePhi_injective_t1`、`tameResidueFacts_of_span_eq_bot`、`generalHensel_reduction`）
**都不需要**有限剩余域。

**`unitsCupVanish` 里有限性用在哪**（逐行读过）：`Hyp302.powClassGen_of_hensel:95` 的
`exists_pow_mul_pow_of_isCyclic (G := (𝓀[F])ˣ)` —— 即**剩余域的单位群循环**（有限域才有的性质）。
⟹ 这是**证明路线的产物**，不是数学必然：GS 6.8.8 的驯符号对一般剩余域成立。

## 本轮结果：把这个唯一入口提成具名假设

| 声明 | 内容 | 假设 |
|---|---|---|
| **`UnitsCupVanish`** | 具名假设：`v(u)=v(w)=0 ⟹ (u)∪(w) = 0`（GS 的 `∂₂((u)∪(w))=0`） | — |
| **`tameResidueFacts_Galo_of_unitsCupVanish`** | `TameResidueFacts`（Galo 载体） | `UnitsCupVanish`，**无 `[Finite]`** |
| **`exists_residueMap_of_unitsCupVanish`** | ★★★★★ `∃ d : H² → VKG` ＋ `d` 的两条性质（论文 (1)） | 同上，**无 `[Finite]`** |
| **`exists_henselResidueData_of_unitsCupVanish`** | ★★★★★ `∃ D : HenselResidueData`（`muNRep` 载体，第 4 章的入口） | 同上，**无 `[Finite]`** |
| **`unitsCupVanish_of_finite`** | ★★★★ **非空见证**：有限剩余域 ⟹ 假设成立（=`Hyp302.unitsCupVanish`） | `[Finite (𝓀[F])]` |
| `exists_residueMap_of_finite'` | **回归对照**：由本轮两个件重新得到 `Hyp344` 的结论 | `[Finite (𝓀[F])]` |

## 结论（缺口精确到一条）

**`prop:prelim-residue` (1) 现在对任意 Hensel 离散赋值域成立，模**：
```
UnitsCupVanish : ∀ u w : Fˣ, v u = 1 → v w = 1 → (u)∪(w) = 0
```
其**非空见证** = 有限剩余域（`unitsCupVanish_of_finite`，已机检；论文的两个例子
`ℚ_[7]`／`𝔽₇((t))` 都落在其中）。
要彻底去掉它，须重证 `powClassGen_of_hensel` 而不经 `(𝓀[F])ˣ` 的循环性
（路线：Milnor `K₂` 的驯符号 / 一般剩余域的 Hilbert 90），见 `HANDOFF` 与 `RECON-S2.md`。
## ⚠ 更正（S37 收尾自审，2026-10-27）：本件的「一般 Hensel」不是论文的忠实推广

`UnitsCupVanish`（单位杯积**字面为零**）⟺ `H²(κ,μ_p) = 0`（推理：`(u) = inf(ū)`（论文
`prop:prelim-kummer-valuation` (1)）＋ 杯积与膨胀相容 ＋ `inf` 单射（GS 6.8.8 分裂正合列））。
故它对有限 `κ` 成立，对 `κ = ℚ`（`F = ℚ((π))`，仍属论文设定）**不成立**。
⟹ 本件是**更强假设**下的条件定理；论文的 (R2) 只要求 `∂₂((u)∪(w)) = 0`（即 `∈ ker ∂₂ = im(inf)`）。
忠实推广须把 `residueSpan = ⊥` 换成 `residueSpan ⊆ ker res`。详见 `RECON-S2.md` 的「更正」节。
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

section UnitsCupHyp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- **唯一的具名假设**：两个**单位**的 Kummer 类的杯积在 `H²(G_F, μ_p)` 里消失
（论文 `prop:prelim-residue` (2) 的 `∂₂((u)∪(w))=0`）。 -/
def UnitsCupVanish (ζ : F) (hζ : IsPrimitiveRoot ζ p) (hpF : IsUnit (p : F)) : Prop :=
  ∀ u w : Fˣ, v u = 1 → v w = 1 →
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0

/-- ★★★★ **`TameResidueFacts`（`GaloBase` 载体）⟸ `UnitsCupVanish`**，**无 `[Finite (𝓀[F])]`**。

与 `Hyp321.tameResidueFacts_Galo_noBridge` 相同，只把 `unitsCupVanish` 换成假设。 -/
theorem tameResidueFacts_Galo_of_unitsCupVanish {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) := by
  refine tameResidueFacts_of_span_eq_bot ?_ ?_
  · exact residueSpan_Galo_eq_bot_of_muNRep' (F := F) (p := p) (v := v) hζ hpF
      (residueSpan_eq_bot_of_units (p := p) hζ v hpF hπ hUU)
  · exact residuePhi_injective_t1 (F := F) (p := p) (v := v) (π := π) hp hζ hv hπ hp2

/-- ★★★★★ **`∃ d`（论文 `prop:prelim-residue` (1) 的两条性质），无 `[Finite (ResidueField)]`**。 -/
-- @source file=raw/L20261018.tex locator=line:1023 quote="\partial_q\bigl(\mathrm{inf}(\eta)\cup(\pi)\bigr)=\eta,\partial_q(\mathrm{inf}(\xi))=0."
theorem exists_residueMap_of_unitsCupVanish {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF) :
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
    (tameResidueFacts_Galo_of_unitsCupVanish (F := F) (p := p) hζ hp hpF hv hπ hp2 hUU)

/-- ★★★★★ **`∃ D : HenselResidueData`（`muNRep` 载体，第 4 章的入口），无 `[Finite (ResidueField)]`**。 -/
theorem exists_henselResidueData_of_unitsCupVanish {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x))
    (hUU : UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
        ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hpF :=
  (generalHensel_reduction (p := p) v hpF hζ hπ hskew).mpr
    (tameResidueFacts_of_units_cup (p := p) hζ v hpF hπ hUU
      (residuePhi_injective_muNRep' (F := F) (p := p) (v := v) (π := π) hp hpF hζ hv hπ hp2))

/-! ### 非空见证 ＋ 回归对照 -/

section Finite

variable [Finite (IsLocalRing.ResidueField ↥𝒪[F])]

/-- ★★★★ **非空见证**：**有限剩余域** ⟹ `UnitsCupVanish`（即 `Hyp302.unitsCupVanish`）。 -/
theorem unitsCupVanish_of_finite {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2) :
    UnitsCupVanish (F := F) (p := p) (v := v) ζ hζ hpF :=
  unitsCupVanish (p := p) (v := v) hζ hp hpF hp2 hv

/-- ★★★★ **回归对照**：由本轮的分解重新得到 `Hyp344.exists_residueMap_of_finite` 的结论
（两条独立路径同结论）。 -/
theorem exists_residueMap_of_finite' {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
      (∀ y z : VKG F p v hpF,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0) ∧
      (∀ y : VKG F p v hpF,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
          (KummerBridge.kummerClass F p hpF π)) = y) :=
  exists_residueMap_of_unitsCupVanish (F := F) (p := p) (v := v) hζ hp hpF hv hπ hp2
    (unitsCupVanish_of_finite (F := F) (p := p) (v := v) hζ hp hpF hv hp2)

end Finite

end UnitsCupHyp

end L20261018

#print axioms L20261018.tameResidueFacts_Galo_of_unitsCupVanish
#print axioms L20261018.exists_residueMap_of_unitsCupVanish
#print axioms L20261018.exists_henselResidueData_of_unitsCupVanish
#print axioms L20261018.unitsCupVanish_of_finite
#print axioms L20261018.exists_residueMap_of_finite'
