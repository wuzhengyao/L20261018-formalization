import Hyp429
import Hyp692
import Hyp680

/-!
# S62 R1：**第 4 章 4 条断言去 `[Finite 𝓀[F]]`** —— 入口改接 `MerkurjevSuslin`

## 判据（`PROMPT-S62` §①-1 / `G2-PLAN.md` §0）

「第 4 章 100%」 ⟺ `FRONTIER.md` 里 4 条带 **残域有限** 的断言全部变空：

```
4.2      orth_eq_bot_noBridge            （Hyp321:102）
4.3-1    thm_ramified_1_noBridge
4.4      corollary_4_4_noBridge
D-ex     exists_henselResidueData_noBridge
```

## 这一轮换掉了什么（**零数学内容，全是接线**）

`Hyp321` 里那 4 条共用的入口是 `tameResidueFacts_Galo_noBridge`，它经
`unitsCupVanish`（`Hyp302`）取 (R2) 那一半，**而 `unitsCupVanish` 带 `[Finite 𝓀[F]]`**
（`frontier.py` 的探针实测：`Hyp302` 是 `[Finite 𝓀]` 的唯一来源）。

(R2) 的那一半正好是论文 `thm:prelim-ms`（Merkurjev–Suslin）覆盖的内容：`Hyp691` 已机检
`MerkurjevSuslin ⟹ TameSymbolFactors`，`Hyp680.tameSymbolFactors_iff` 再把它转成
`TameResidueFacts`（**两者都是载体无关的抽象陈述**，不需要残域有限）。故：

```
MerkurjevSuslin ⟹ TameSymbolFactors ⟹ TameResidueFacts
                ⟹ 4.2／4.3(1)／4.4（经 Hyp429 的 *_nofin 路线，连 FiniteDimensional 也不需要）
```

这与论文口径一致：论文第 4 章本来就引用 `thm:prelim-ms`，而**不假设**残域有限。

## 机检件

| 声明 | 内容 | 与旧版的差异 |
|---|---|---|
| **`tameResidueFacts_of_merkurjevSuslin`** | `MS ⟹ TameResidueFacts`（`GaloBase` 载体） | **零** `[Finite 𝓀]` |
| **`orth_eq_bot_of_merkurjevSuslin`** | ★ **4.2** | 去 `[Finite 𝓀]`、去 `[FiniteDimensional V]`、去 `ζ` |
| **`thm_ramified_1_of_merkurjevSuslin`** | ★ **4.3(1)** | 去 `[Finite 𝓀]`、去 `[FiniteDimensional V]`、去 `ζ` |
| **`corollary_4_4_of_merkurjevSuslin`** | ★ **4.4** | 去 `[Finite 𝓀]`、去 `[FiniteDimensional V]`、去 `ζ` |
| **`exists_henselResidueData_of_merkurjevSuslin`** | ★★ **`∃D`**（`GaloBase` 载体） | 去 `[Finite 𝓀]`、去 `ζ`、去 `hskew` |

## 诚实边界

* 本件**不证** `MerkurjevSuslin`（＝论文 `thm:prelim-ms`，Merkurjev 1982）。
* `D-ex` 的载体从 `muNRep` 换成 `GaloBase`（`valH1LinearGen` → `valLinOf`）：两者经
  `H2Bridge.redEquiv1` 同构（`Hyp319.valH1LinearGen_redEquiv1_smul`，差一个非零标量），
  论文 `prop:prelim-residue` 说的是抽象 `H²(F,μ_p^{⊗2}) → H¹(K,μ_p)`，不指定载体。
  `muNRep` 载体的版本见下一轮（需把 `residueSpan = ⊥` 反向运输）。
- 保留下来的 `IsUnit (p : ↥𝒪[F])` 是**结构性**假设（`p` 在整数环中可逆，`A3` 的两条值性质用它），
  不是本轮的靶子；论文 §2 的 `char K ≠ p` 与之对应。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section MerkurjevSuslinEntry

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **`MerkurjevSuslin ⟹ TameResidueFacts`**（`GaloBase` 载体，**无** `[Finite 𝓀]`）。

`Hyp321.tameResidueFacts_Galo_noBridge` 的 (R2) 那一半来自带 `[Finite 𝓀]` 的 `unitsCupVanish`；
本件把它换成论文 `thm:prelim-ms`。 -/
-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem tameResidueFacts_of_merkurjevSuslin (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2' : NeZero (2 : ZMod p))
    (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) := by
  have hval : valLinOf (F := F) (p := p) v hpF (KummerBridge.kummerClass F p hpF π) = 1 :=
    valLinOf_pi (F := F) (p := p) v hpF hπ
  have h2 : (2 : ZMod p) ≠ 0 := fun h0 => NeZero.ne (2 : ZMod p) h0
  exact (tameSymbolFactors_iff (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) hval
      (fun x y => GaloBase.cup_skew (K := F) (p := p) x y) h2).mp
    (tameSymbolFactors_of_merkurjevSuslin (F := F) (p := p) (v := v) hp hpF hv hp2 hMS)

/-- ★★★★★ **4.2（`lem:ramified-vanishing`）—— 只依赖论文 `thm:prelim-ms`**。

与 `Hyp321.orth_eq_bot_noBridge` 相比：去 `[Finite 𝓀[F]]`（改接 MS）、去
`[FiniteDimensional (ZMod p) (GaloBase.V F p)]`（`Hyp429` 的平面归约）、去 `ζ`（MS 侧不需要
单位根，`HasEnoughRootsOfUnity` 已在上下文）。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_of_merkurjevSuslin (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2' : NeZero (2 : ZMod p))
    {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation_nofin (F := F) (p := p) hpF v hπ hp2' hne hval
    (tameResidueFacts_of_merkurjevSuslin (F := F) (p := p) hp hpF hv hp2 hπ hp2' hMS)

/-- ★★★★★ **4.3(1)（`thm:ramified` (1)）—— 只依赖论文 `thm:prelim-ms`**。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_of_merkurjevSuslin (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F,
      x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hpF a1) (KummerBridge.kummerClass F p hpF a2),
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    (Theo352.Bex (F := F) (p := p) hpF hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ :=
  thm_ramified_1_of_discrete_valuation_nofin (F := F) (p := p) (Δ := Δ) (hp := hpF) (hp2 := hp2)
    hroots hU v hπ
    (tameResidueFacts_of_merkurjevSuslin (F := F) (p := p) hp hpF hv hp2 hπ
      (neZero_two_zmod p hp2) hMS) ha1 ha2 hne hval

/-- ★★★★★ **4.4（`cor:rank-barrier`）—— 只依赖论文 `thm:prelim-ms`**。 -/
-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_of_merkurjevSuslin (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2),
      valLinOf (F := F) (p := p) v hpF (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hpF)) = 1)
    [FiniteDimensional (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    [NeZero (2 : ZMod p)]
    (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a2)).range = 2
      ∧ Module.finrank (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 :=
  corollary_4_4_of_discrete_valuation (F := F) (p := p) (a1 := a1) (a2 := a2) hpF v hπ
    (tameResidueFacts_of_merkurjevSuslin (F := F) (p := p) hp hpF hv hp2 hπ (neZero_two_zmod p hp2) hMS)
    hne hval hK1

/-- ★★★★★★ **`∃D`（`prop:prelim-residue`(1) 的 `D` 存在）—— 只依赖论文 `thm:prelim-ms`**。

与 `Hyp321.exists_henselResidueData_noBridge` 相比：**去 `[Finite 𝓀[F]]`、去 `ζ`、去 `hskew`**。
载体为 `GaloBase`（`valLinOf`）；`muNRep` 载体（`valH1LinearGen`）版本需反向运输 `residueSpan`，
见下一轮。 -/
-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem exists_henselResidueData_of_merkurjevSuslin (hp : IsUnit (p : ↥𝒪[F]))
    (hpF : IsUnit (p : F)) (hv : ValCompat (F := F) v) (hp2 : p ≠ 2)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2' : NeZero (2 : ZMod p))
    (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    ∃ D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p)
        (VKG F p v hpF) (GaloBase.cup (K := F) (p := p)),
      D.val = valLinOf (F := F) (p := p) v hpF :=
  nonempty_henselResidueData_of_merkurjevSuslin (F := F) (p := p) (v := v) hp hpF hv hp2 hπ hp2' hMS

end MerkurjevSuslinEntry

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.tameResidueFacts_of_merkurjevSuslin
#print axioms L20261018.orth_eq_bot_of_merkurjevSuslin
#print axioms L20261018.thm_ramified_1_of_merkurjevSuslin
#print axioms L20261018.corollary_4_4_of_merkurjevSuslin
#print axioms L20261018.exists_henselResidueData_of_merkurjevSuslin
