import TauCeti.Topology.Algebra.Group.Profinite.ZHat.CohomologicalDimension
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.PadicInt
import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Existence
import TauCeti.Topology.Algebra.Group.Profinite.Sylow.CohomologicalDimension
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ContinuousMulEquiv

/-!
# S42 R1（A.6.9 甲之三）：**`cd_p(ℤ_p) ≤ 1`** —— 全部用库内件

## 本件在 A.6.9 的哪一格

`Hyp499`／`Hyp500` 给了 A.6.9（甲）的 `H¹` 层（`H¹(ℤ_p, ℤ/p) ≃ ℤ/p`）。
本件补 A.6.9（甲）的**另一半**：`cd_p(ℤ_p) ≤ 1`，即
`H^q(ℤ_p, M) = 0`（`q ≥ 2`，`M` 为 `p`-primary 挠离散模）。

## ★★★★★ 本轮的决定性侦察发现：这一格**早已在 TauCeti 里**

S41 的裁定（`S41-STATUS.md` §4.6／§4.9）把 A.6.9（甲）登记为「**无库内支撑**，5–15 轮」。
R1 的内容式检索（规则 23／24：禁按名字搜，须搜目录）推翻了它：

| 需要用的事实 | 库内件 | 位置 |
|---|---|---|
| **`H²(Ẑ, M) = 0`（`M` 离散挠）** | ★ **`TauCeti.zHat.subsingleton_continuousCohomology_two_of_isAddTorsion`** | `Profinite/ZHat/CohomologicalDimension.lean` |
| **`cd_p(Ẑ) ≤ 1`** | **`TauCeti.zHat.cohomologicalDimensionAt_le_one`** | 同上 |
| **`cd_p(Ẑ) = 1`**（GS `prop-cd-Z-hat`） | **`TauCeti.zHat.cohomologicalDimensionAt_eq_one`** | 同上 |
| `cd_p` 的**单次度判据**（只测 `n+1` 次、有限 `p^k`-挠系数） | `TauCeti.cohomologicalDimensionLE_iff_forall_finite_subsingleton_succ` | `ContCohomology/CohomologicalDimension/SingleDegree.lean` |
| **`cd_p G = cd_p P`**（`P` = `G` 的 `p`-Sylow） | ★ **`TauCeti.IsProPSylow.cohomologicalDimensionAt_eq`** | `Profinite/Sylow/CohomologicalDimension.lean` |
| **`Ẑ` 的每个 `p`-Sylow ≅ `ℤ_p`** | ★ **`TauCeti.IsProPSylow.continuousMulEquivPadicInt`** | `Profinite/ZHat/PadicInt.lean` |
| `cd_p` 沿 `≃ₜ*` 不变 | `TauCeti.cohomologicalDimensionAt_congr` | `CohomologicalDimension/ContinuousMulEquiv.lean` |

⟹ 链**一行一步**（GS 的 A.6.9 原论证，逐字对齐，规则 25）：

```
cd_p(ℤ_p) = cd_p(P)        -- P ≅ₜ* ℤ_p（库内 continuousMulEquivPadicInt）＋ cohomologicalDimensionAt_congr
          = cd_p(Ẑ)        -- P = Ẑ 的 p-Sylow（库内 IsProPSylow.cohomologicalDimensionAt_eq）
          = 1              -- GS prop-cd-Z-hat（库内 zHat.cohomologicalDimensionAt_eq_one）
```

对应 GS 正文（`raw/GilleSzamuely2017.tex:9626`）：
"the `ℓ`-Sylow subgroups of `H` are isomorphic to `ℤ_ℓ` … Therefore `cd_ℓ(H) ≤ 1`
by Proposition `prop-cd-Z-hat` and Lemma `lemma-cd-subgroup`" —— 本件走的正是这条。

## 主要声明

| 声明 | 内容 |
|---|---|
| **`cohomologicalDimensionAt_padicInt_le_one`** | ★★★★★ **`cd_p(ℤ_p) ≤ 1`** |
| **`cohomologicalDimensionAt_padicInt_eq_one`** | ★★★★★ **`cd_p(ℤ_p) = 1`**（含下界，故非空洞） |
| **`cdLE_padicInt_one`** | ★★★★★ **`CohomologicalDimensionLE.{0, 0} p ℤ_p 1`**（`H^q(ℤ_p,M)=0`，`q>1`） |
| **`subsingleton_continuousCohomology_padicInt_of_two_le`** | `H^q(ℤ_p, M) = 0`（`q ≥ 2`，`M` 为 `p`-primary 挠） |
| **`subsingleton_H2_padicInt`** | ★★★★ **`H²(ℤ_p, M) = 0`**（`q = 2` 的显式形态，即 §4.6 的 `H²(H,μ_p)=0` 之 **模型群**版） |
| **`subsingleton_H2_padicInt_of_module_zmod`** | `M` 为 `ZMod p`-模（**任意**作用，不必平凡）时的 `H² = 0` |
| `trivialActionZModPadicInt`／`trivialContinuousSMulZMod` | 平凡作用实例（非空见证，L1／L10①） |

## 诚实边界（必须继承）

* 本件只解决 **`H = ℤ_p`（`ℤ_p` 这个模型群）** 的 `cd_p ≤ 1`。
  **惯性群 `I = Gal(K_s/K_nr)` 的 `cd_p(I) ≤ 1` 仍未做**——把 `cd_p(ℤ_p) ≤ 1` 搬到 `I`
  需要的正是 **A.6.9 的群论半（驯歧理论：`I` 的 `ℓ`-Sylow ≅ `ℤ_ℓ`）**，即 S41 的（乙）。
  本件**不**声称（乙）已完成，也**不**声称 `Ch4TameSymbolHyp` 已得。
* 本件**不**触及 `KnrResidueObligation`。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open TauCeti

namespace L20261018

variable (p : ℕ) [Fact p.Prime]

/-- ★★★★★ **`cd_p(ℤ_p) = cd_p(Ẑ)`** 的桥：`ℤ_p` 是 `Ẑ` 的 `p`-Sylow 的拓扑同构像。

`cd_p(ℤ_p) = cd_p(P) = cd_p(Ẑ)`（`P` = `Ẑ` 的 `p`-Sylow）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9625 quote="the $\ell$-Sylow subgroups of $H$ are isomorphic to $\mathbf{Z}_{\ell}$ for $\ell$ prime to $\operatorname{char}(\kappa(v))$"
theorem cohomologicalDimensionAt_padicInt_eq_zHat :
    cohomologicalDimensionAt.{0, 0} p (Multiplicative ℤ_[p])
      = cohomologicalDimensionAt.{0, 0} p (zHat.{0} : Type) := by
  obtain ⟨P, hP⟩ := exists_isProPSylow p (zHat.{0} : Type)
  have h1 : cohomologicalDimensionAt.{0, 0} p (Multiplicative ℤ_[p]) =
      cohomologicalDimensionAt.{0, 0} p (P : Type) :=
    cohomologicalDimensionAt_congr hP.continuousMulEquivPadicInt.symm
  have h2 : cohomologicalDimensionAt.{0, 0} p (zHat.{0} : Type) =
      cohomologicalDimensionAt.{0, 0} p (P : Type) := hP.cohomologicalDimensionAt_eq
  exact h1.trans h2.symm

/-- ★★★★★ **`cd_p(ℤ_p) ≤ 1`**（GS A.6.9 甲的上同调半；GS `prop-cd-Z-hat` ＋ Sylow ＋ `≃ₜ*`）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:prop-cd-Z-hat quote="We have $\operatorname{cd}_{p}(\hat{\mathbf{Z}})=1$ for all primes $p$."
theorem cohomologicalDimensionAt_padicInt_le_one :
    cohomologicalDimensionAt.{0, 0} p (Multiplicative ℤ_[p]) ≤ 1 := by
  rw [cohomologicalDimensionAt_padicInt_eq_zHat p]
  exact zHat.cohomologicalDimensionAt_le_one (Fact.out : p.Prime).ne_zero

/-- ★★★★★ **`cd_p(ℤ_p) = 1`** —— 下界由 `cd_p(Ẑ) = 1`（GS `prop-cd-Z-hat`）经同一链给出，
故本件的上界**不是空洞的**（L1／L10① 的「非空实例义务」在此体现为**下界见证**）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:prop-cd-Z-hat quote="We have $\operatorname{cd}_{p}(\hat{\mathbf{Z}})=1$ for all primes $p$."
theorem cohomologicalDimensionAt_padicInt_eq_one :
    cohomologicalDimensionAt.{0, 0} p (Multiplicative ℤ_[p]) = 1 := by
  rw [cohomologicalDimensionAt_padicInt_eq_zHat p]
  exact zHat.cohomologicalDimensionAt_eq_one p

/-- ★★★★★ **`CohomologicalDimensionLE.{0, 0} p ℤ_p 1`**：`H^q(ℤ_p, M) = 0` 对一切 `q > 1`
与一切 `p`-primary 挠离散模成立。 -/
theorem cdLE_padicInt_one : CohomologicalDimensionLE.{0, 0} p (Multiplicative ℤ_[p]) 1 :=
  (cohomologicalDimensionAt_le_iff p (Multiplicative ℤ_[p]) 1).1
    (cohomologicalDimensionAt_padicInt_le_one p)

/-- ★★★★ **`H^q(ℤ_p, M) = 0`（`q ≥ 2`）**，`M` 为 `p`-primary 挠离散模（作用**任意**）。

这是 §4.6 的 `H²(H, μ_p) = 0` 在**模型群 `ℤ_p`** 上的版本。 -/
theorem subsingleton_continuousCohomology_padicInt_of_two_le
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (Multiplicative ℤ_[p]) M] [ContinuousSMul (Multiplicative ℤ_[p]) M]
    (hM : IsPPrimaryTorsion p M) {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (continuousCohomology q (ofDiscreteModule ℤ (Multiplicative ℤ_[p]) M)) :=
  cohomologicalDimensionLE_iff.1 (cdLE_padicInt_one p) M hM q (by omega)

/-- ★★★★ **`H²(ℤ_p, M) = 0`**（`q = 2` 的显式形态）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9627 quote="Therefore $\operatorname{cd}_{\ell}(H)\leq1$"
theorem subsingleton_H2_padicInt
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction (Multiplicative ℤ_[p]) M] [ContinuousSMul (Multiplicative ℤ_[p]) M]
    (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ (Multiplicative ℤ_[p]) M)) :=
  subsingleton_continuousCohomology_padicInt_of_two_le p M hM le_rfl

/-- `ZMod p`-模都是 `p`-primary 挠（`p • a = 0`）。 -/
theorem isPPrimaryTorsion_of_module_zmod (M : Type) [AddCommGroup M] [Module (ZMod p) M] :
    IsPPrimaryTorsion p M := by
  refine isPPrimaryTorsion_iff.2 fun a => ⟨1, ?_⟩
  rw [pow_one, ← Nat.cast_smul_eq_nsmul (ZMod p) p a, ZMod.natCast_self, zero_smul]

/-- ★★★★ **`H²(ℤ_p, A) = 0`**（`A` 为 `ZMod p`-模，作用**任意**）。

即 S41 §4.6 记作「`H²(H, μ_p) = 0`」的那一格在 `H = ℤ_p` 时的**无条件**版本。 -/
theorem subsingleton_H2_padicInt_of_module_zmod
    (A : Type) [AddCommGroup A] [Module (ZMod p) A]
    [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction (Multiplicative ℤ_[p]) A] [ContinuousSMul (Multiplicative ℤ_[p]) A] :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ (Multiplicative ℤ_[p]) A)) :=
  subsingleton_H2_padicInt p A (isPPrimaryTorsion_of_module_zmod p A)

/-! ### 非空见证（L1／L10①）：假设类非空 ＋ 结论非空洞 -/

/-- `Multiplicative ℤ_[p]` 在 `ZMod p` 上的**平凡作用**。 -/
local instance trivialActionZModPadicInt503 : DistribMulAction (Multiplicative ℤ_[p]) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该作用下 `ContinuousSMul`（`smul` 即投影）。 -/
local instance trivialContinuousSMulZMod503 : ContinuousSMul (Multiplicative ℤ_[p]) (ZMod p) where
  continuous_smul := continuous_snd

/-- **非空见证**：`A = ZMod p`（平凡作用）满足 `subsingleton_H2_padicInt_of_module_zmod` 的全部
实例要求，故该定理的假设类**非空**，结论不空洞。 -/
theorem subsingleton_H2_padicInt_zmod_p_witness :
    Subsingleton (continuousCohomology 2
      (ofDiscreteModule ℤ (Multiplicative ℤ_[p]) (ZMod p))) :=
  subsingleton_H2_padicInt_of_module_zmod p (ZMod p)

/-- **下界／非空洞见证**：`cd_p(ℤ_p) = 1 ≠ 0`，故 `H^q` 的消没**不能**加强到 `q ≥ 1`
（`H¹(ℤ_p, ℤ/p) ≃ ℤ/p ≠ 0`，见 `Hyp500`）。 -/
theorem cd_padicInt_ne_zero : cohomologicalDimensionAt.{0, 0} p (Multiplicative ℤ_[p]) ≠ 0 := by
  rw [cohomologicalDimensionAt_padicInt_eq_one p]
  exact one_ne_zero

end L20261018

#print axioms L20261018.cohomologicalDimensionAt_padicInt_eq_zHat
#print axioms L20261018.cohomologicalDimensionAt_padicInt_le_one
#print axioms L20261018.cohomologicalDimensionAt_padicInt_eq_one
#print axioms L20261018.cdLE_padicInt_one
#print axioms L20261018.subsingleton_H2_padicInt
#print axioms L20261018.subsingleton_H2_padicInt_of_module_zmod
#print axioms L20261018.subsingleton_H2_padicInt_zmod_p_witness
#print axioms L20261018.cd_padicInt_ne_zero
