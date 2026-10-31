import Hyp109
import Hyp101
import Hyp103

/-!
# 第 4 章 T3 论文层：`lem:ramified-vanishing` 在论文真实对象上

`Hyp109` 在**抽象层**证明了 T3 的数学内核（`ResidueCupData.vanishing`）。本文件把它
**实例化到论文的真实载体**，即论文的 `V = H¹(F,μ_p)` 与 `∪`。

## 具名假设：`HenselResidueData`

论文 `lem:ramified-vanishing` 的证明只经由 §2.4 的三条工具（`prop:prelim-kummer-valuation`
的赋值分解 ＋ `prop:prelim-residue` 的驯符号公式 ＋ `prop:prelim-cup` 的双线性／斜对称）。
`HenselResidueData` 就是这三条在**给定真实 `cup`** 上的形态（**逐字段类型锁定**）：

| 字段 | 论文出处 |
|---|---|
| `res`／`val`／`infl`／`inj_infl`／`val_infl`／`pi`／`val_pi`／`split` | `prop:prelim-kummer-valuation`（`raw/L20261018.tex:962–1130`） |
| `tame_uu`／`tame_u_pi`／`tame_pi_u` | `prop:prelim-residue` 的 `eq:prelim-tame` 的**三处特化** |
| `cup` 的斜对称 | `prop:prelim-cup`（由具体 `cup` 的 `cup_skew` 供给，**不是**假设） |

> **与 `RECON-CH4.md` 的 Route A′ 建议的关系**：侦察指出「一般 `p` 的 `∂₂` **值等式**
> 五库皆无」。本结构不假设那条值等式，只假设**证明实际用到的三处特化**——
> 这是 `∅-open` 残余，已登记于 `STATUS.md`。侦察给的替代路线（`hilbertSymbol` ＋
> `localSymbol` ＋ 分裂分解）是**可选升级**，见 `STATUS.md` R938 段。

## 两个载体

第 3 章的「真实对象」有两个载体（这是第 3 章已登记的载体身份问题）：

* **`GaloBase` 层**：`V = GaloBase.V F p`、`cup = GaloBase.cup`（3.1／3.2 用）；
* **显式层**：`V = H1 (AbsoluteGaloisGroup F) (ZMod p)`、`cup = Theo352.cupLin`（3.3(2)／3.5／3.6／`Nsub` 用）。

故 `HenselResidueData` 按 **`cup` 参数化**，两个载体各得一份（`ramified_vanishing_kummer`
与 `ramified_vanishing_explicit`）。这正是 T4 需要的：T4(1) 的 `N = 0` 在显式层。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000

namespace L20261018

/-! ## 1. 具名假设（按 `cup` 参数化） -/

/-- **§2.4 工具在给定 `cup` 上的形态（具名假设，逐字段类型锁定）**。

**`tame_*` 三条不是本战役的发明**：论文 `raw/L20261018.tex:1117–1121` 在
`prop:prelim-residue` 之后**逐字列出**这三条特化（见紧邻的 `@source` 注解）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
structure HenselResidueData (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V]
    (H2 : Type*) [AddCommGroup H2] [Module k H2]
    (VK : Type*) [AddCommGroup VK] [Module k VK]
    (cup : V →ₗ[k] V →ₗ[k] H2) where
  /-- 二阶剩余映射 `∂ : H²(F,μ_p) → H¹(K,μ_p)`（`prop:prelim-residue`）。 -/
  res : H2 →ₗ[k] VK
  /-- 模 `p` 赋值 `\bar v : H¹(F,μ_p) → F_p`（`prop:prelim-kummer-valuation`）。 -/
  val : V →ₗ[k] k
  /-- 膨胀 `H¹(K,μ_p) → H¹(F,μ_p)`。 -/
  infl : VK →ₗ[k] V
  /-- 正合列左端单射。 -/
  inj_infl : Function.Injective infl
  /-- `v ∘ infl = 0`。 -/
  val_infl : ∀ y : VK, val (infl y) = 0
  /-- 素元的 Kummer 类 `(π)`。 -/
  pi : V
  /-- `v(π) = 1`。 -/
  val_pi : val pi = 1
  /-- 赋值分解 `x = inf x₀ + m·(π)`。 -/
  split : ∀ x : V, ∃ (x₀ : VK) (m : k), x = infl x₀ + m • pi
  /-- 驯符号（两单位）。 -/
  tame_uu : ∀ y z : VK, res (cup (infl y) (infl z)) = 0
  /-- 驯符号（单位 × 素元）。 -/
  tame_u_pi : ∀ y : VK, res (cup (infl y) pi) = y
  /-- 驯符号（素元 × 单位；`eq:prelim-tame` 的 `-1` 次幂）。 -/
  tame_pi_u : ∀ (κ : V), val κ = 1 → ∀ z : VK, res (cup κ (infl z)) = -z

namespace HenselResidueData

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {VK : Type*} [AddCommGroup VK] [Module k VK]
variable {cup : V →ₗ[k] V →ₗ[k] H2}

/-- 把具名假设打包成 `Hyp109` 的 `ResidueCupData`（`skew` 由具体 `cup` 供给）。 -/
def toResidueCupData (D : HenselResidueData k V H2 VK cup)
    (hskew : ∀ x y, cup x y = - cup y x) : ResidueCupData k V H2 VK where
  cup := cup
  skew := hskew
  res := D.res
  val := D.val
  infl := D.infl
  inj_infl := D.inj_infl
  val_infl := D.val_infl
  pi := D.pi
  val_pi := D.val_pi
  split := D.split
  tame_uu := D.tame_uu
  tame_u_pi := D.tame_u_pi
  tame_pi_u := D.tame_pi_u

/-- **T3（真实 `cup` 上的条件定理）**：只带论文假设 ＋ 具名假设 `HenselResidueData`。 -/
theorem ramified_vanishing [NeZero (2 : k)] (D : HenselResidueData k V H2 VK cup)
    (hskew : ∀ x y, cup x y = - cup y x)
    (a1 a2 : V) (hne : cup a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := k) a1 a2, D.val u ≠ 0) :
    ResidueCupData.orth cup a1 a2 = ⊥ :=
  (D.toResidueCupData hskew).vanishing a1 a2 hne hval

end HenselResidueData

/-! ## 2. 论文层（`GaloBase` 载体：`V = H¹(F,μ_p)`、`∪ = GaloBase.cup`） -/

section KummerLayer

variable (F K : Type) [Field F] [Field K] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]

/-- **T3 论文层（`lem:ramified-vanishing`，真实对象）**。

论文假设：`p` 奇素、`F` 特征 `0` 含 `μ_p`、`K` 为剩余域且 `char K ≠ p`、
`a₁ a₂ ∈ F^×`、`(a₁)∪(a₂) ≠ 0`、`\bar v|_U ≠ 0`。结论 `U^⊥ = 0`。

`(F,v)` 为 Hensel 离散赋值域这条假设**由具名假设 `D` 承担**（`D` 的存在性就是
`prop:prelim-kummer-valuation` ＋ `prop:prelim-residue`，两者都需要 Hensel 性）。
`hK : ringChar K ≠ p` 是论文的 `char K ≠ p`（陈述保真，证明不用——它进 `D` 的存在性）。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem ramified_vanishing_kummer (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (hK : ringChar K ≠ p)
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) (GaloBase.V K p)
      (GaloBase.cup (K := F) (p := p)))
    (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2), D.val u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  exact HenselResidueData.ramified_vanishing D
    (fun x y => GaloBase.cup_skew (K := F) (p := p) x y)
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) hne hval

end KummerLayer

/-! ## 3. 论文层（显式载体：`V = H1 (AbsoluteGaloisGroup F) (ZMod p)`、`∪ = Theo352.cupLin`） -/

section ExplicitLayer

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `Theo352.Bex` 的 `U^⊥` 就是 `ResidueCupData.orth cupLin (a₁) (a₂)`（同一载体、同一公式）。 -/
theorem Bex_Uperp_eq_orth (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp =
      ResidueCupData.orth (Theo352.cupLin (F := F) (p := p))
        (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
        (GaloCup.kummerExplicit (F := F) (p := p) hp a2) :=
  rfl

/-- **T3 论文层（显式载体版）**：T4 的 `N = 0` 需要的形态。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem ramified_vanishing_explicit (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (VK : Type) [AddCommGroup VK] [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p)
      (H1 (AbsoluteGaloisGroup F) (ZMod p)) (H2 (AbsoluteGaloisGroup F) (ZMod p)) VK
      (Theo352.cupLin (F := F) (p := p)))
    (a1 a2 : Fˣ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2), D.val u ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  rw [Bex_Uperp_eq_orth (F := F) (p := p) hp hne]
  exact HenselResidueData.ramified_vanishing D
    (fun x y => Theo352.cupLin_skew (F := F) (p := p) x y) _ _ hne hval

end ExplicitLayer

end L20261018

#print axioms L20261018.HenselResidueData.toResidueCupData
#print axioms L20261018.HenselResidueData.ramified_vanishing
#print axioms L20261018.ramified_vanishing_kummer
#print axioms L20261018.Bex_Uperp_eq_orth
#print axioms L20261018.ramified_vanishing_explicit
