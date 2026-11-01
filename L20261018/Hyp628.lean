import L20261018.Hyp627
import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic

/-!
# S52 R21：**L2 桥** —— 把 `hκ` 从「`Subsingleton H²`」降为**已发表的 Tsen 形态** `cd_p(κ) ≤ 1`

## 0 本件在路线上的位置

`wiki/hyp-tsen.md`（S52 R20 建件）把档 ⑥ 的 `hκ : Subsingleton (GaloBase.H2 κ p)` 拆成三层：

| 层 | 内容 | R20 时的状态 |
|---|---|---|
| L1 定义层 | `GaloBase.H2 κ p = ↑(continuousCohomology 2 (muP κ p))` | ✅ 机检（`A.lean:665`） |
| **L2 库内层** | `cd_p(κ) ≤ 1 ⟹ Subsingleton (H²(κ, Z/p))` | ⚠ 「只差一次载体运输」 |
| L3 外部层 | Tsen：`C₁ ⟹ cd ≤ 1`（GS `thm-tsen` ⟹ `prop-c1-cd1`） | ✗ 已发表未形式化 |

**本件闭 L2**。⟹ 从此档 ⑥ 的 Tsen 侧假设可以写成**已发表的形态** `cd_p(κ) ≤ 1`，
而不再是不可解读的 `Subsingleton`。

## 1 L2 的两件库内机器（`#check` 实读签名，S52 R20／R21）

```lean
-- ① 消失判据（TauCeti，CohomologicalDimension/Basic.lean:131；_le_iff 在 :194）
def CohomologicalDimensionLE (n : ℕ) : Prop :=
  ∀ (M) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
    ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M))

-- ② 基环桥（TauCeti，ContCohomology/RestrictScalars.lean；文件头：「continuous cohomology
--    does not see the scalars」）
theorem subsingleton_continuousCohomology_ofDiscreteModule_iff (X : TopRep k G)
    [DiscreteTopology ↑X] (n : ℕ) :
  Subsingleton ↑(continuousCohomology n (ofDiscreteModule ℤ G ↑X)).toModuleCat
    ↔ Subsingleton ↑(continuousCohomology n X).toModuleCat
```

⟹ 取 `X := GaloBase.muP κ p`（载体 `ZMod p`，**平凡**作用），① 给 ℤ-系数侧的消失，
② 把它搬回 `ZMod p`-系数侧。**全程无新数学。**

## 2 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| **`TsenHyp`** | ★★★★★ **Tsen 假设的具名形态**：`CohomologicalDimensionLE.{0} p (AbsoluteGaloisGroup K) 1`（＝ `cd_p(K) ≤ 1`） |
| `isPPrimaryTorsion_muP` | `IsPPrimaryTorsion p ↑(muP κ p)`（消失判据的实例前提；`ZMod p` 的元素被 `p` 杀掉） |
| **`subsingleton_H2_of_cohomologicalDimensionLE`** | ★★★★★★ **L2 桥**：`cd_p(K) ≤ 1 ⟹ Subsingleton (GaloBase.H2 K p)` |
| **`subsingleton_H2_of_TsenHyp`** | 同上，具名形态 |
| **`ch4TameSymbolHyp_of_tsen`** | ★★★★★★★ **档 ⑥ 的 Tsen 形态**：`Hyp614` 的 `hκ` 换成 `hTsen` |
| **`residueSpan_eq_bot_of_tsen`** | ★★★★★ 接入 `Hyp611` 正规形（`residueSpan = ⊥`）的 Tsen 形态 |

## 3 工艺（本轮三个真坑，全部是**实例层**，非数学 —— `LESSONS` B1／B18）

1. **`attribute [local instance] TopRep.distribMulAction` 必须显式加**：
   `DistribMulAction G ↑X` 在 TauCeti 里**不是全局实例**（`RestrictScalars.lean:632` 只用
   `attribute [local instance]` 在本文件内注册）。不加则 `subsingleton_continuousCohomology_ofDiscreteModule_iff`
   的语句里 `ofDiscreteModule` 缺实例，报 `failed to synthesize DistribMulAction G ↑X`。
2. **宇宙参数**：`CohomologicalDimensionLE` 的 `M : Type (max u v)`；在 `K : Type`（`u = 0`）时
   必须在**假设的陈述处**就写 `CohomologicalDimensionLE.{0}`，否则定理把 `v` 泛化成宇宙参数，
   `ZMod p : Type 0` 无法实例化它（报 `ZMod p has type Type but expected Type u_1`）。
3. **`IsPPrimaryTorsion p ↑(muP κ p)` 不能用 `Nat.card` 路线**：`↑(muP κ p)` 与 `ZMod p` 是 **`rfl` 级 defeq**
   （实测 `(↑(muP K p) : Type) = ZMod p := rfl`），但**实例搜索不穿透 defeq** ⟹ 没有 `Fintype ↑(muP κ p)`
   （报 `failed to synthesize Fintype`）。**正解**：先证 `IsPPrimaryTorsion p (ZMod p)`（在 `ZMod p` 上工作，
   用 `Nat.cast_smul_eq_nsmul` 把 `p • m` 换成 `(p : ZMod p) • m`，再由 `ZMod.natCast_self` 得 0），
   然后 `exact`（defeq 行得通——**陈述层的 defeq 能过，实例搜索不过**，这是两者的分界）。
4. **`ℕ∞` 形态本轮未做**：`cohomologicalDimensionAt p G ≤ 1` 与 `CohomologicalDimensionLE` 的互换
   在库内是 `cohomologicalDimensionAt_le_iff`，但它带**独立的宇宙参数**（`M : Type (max u v)`），
   在 `K : Type` 时与 `CohomologicalDimensionLE.{0}` 的对齐会在陈述处留下宇宙元变量
   （`cohomologicalDimensionAt.{?u, 0}` vs `.{u_1, 0}`）⟹ 本轮**只保留 `CohomologicalDimensionLE.{0}` 形态**，
   `ℕ∞` 形态登记为下一轮（须在 `TsenHyp` 的定义处显式写死 `cohomologicalDimensionAt.{0, 0}` 或改陈述方式）。
5. **库内有平行路线（诚实登记）**：`CohomologicalDimension/TrivialFp.lean` 为 `trivialFp p G` 这个载体
   **专门写了** `CohomologicalDimensionLE.subsingleton_cohomFp`。本件走的是战役自己的载体
   `GaloBase.muP κ p`（＝ 平凡 `ZMod p` 表示），两条路线等价；选后者的理由是 `muP` 才是 `GaloBase.H2` 的定义载体。

## 4 诚实边界

* **`hTsen` 仍是假设**：`TsenHyp (ℂ(t))` 的**证明**（＝ Tsen 定理 ＋ `C₁ ⟹ cd ≤ 1`）未形式化，
  见 `wiki/hyp-tsen.md` §5 的步 1／2／4。
* **本件不证 `(CI)`**，也不动 `FbarValuationHyp₄`；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
* **非空实例义务（L1＋L10①）**：`TsenHyp` 的机检见证**仍无**（`TsenHyp (κ)` 的见证需要
  「`cd_p(G_κ) ≤ 1` 对某个 `κ`」的机检证明）；数学见证是 `κ = ℂ(t)`（已发表）。
  且**「剩余域恰为 `ℂ(t)` 的 `F`」在库内仍不存在**（`ValCompat` 见证只到 `ℚ_[p]`）。
  ⟹ 本件的条件定理按 `∅-open` 的条件形式登记，**不得**读成无条件结论。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

/- TauCeti 只在 `RestrictScalars.lean` 内部局部注册了 `TopRep.distribMulAction`；
要用它的消失判据（`ofDiscreteModule` 的 `DistribMulAction` 前提）必须同样局部注册。 -/
attribute [local instance] TopRep.distribMulAction

namespace L20261018

section TsenBridge

/-! ### 一、具名形态：`cd_p(K) ≤ 1` -/

/-- ★★★★★ **Tsen 假设的具名形态**：`κ` 的 `p`-上同调维数 `≤ 1`。

数学读法：`cd_p(κ) ≤ 1`（[GS, `def-cd-field`] 的定义：绝对 Galois 群的 `p`-上同调维数）。
`κ = ℂ(t)` 时由 Tsen 定理成立（[GS, `thm-tsen`] ＋ `prop-c1-cd1`）。 -/
def TsenHyp (K : Type) [Field K] (p : ℕ) [Fact p.Prime] : Prop :=
  CohomologicalDimensionLE.{0} p (AbsoluteGaloisGroup K) 1

/-- `IsPPrimaryTorsion p ↑(GaloBase.muP K p)`：`ZMod p` 中的元素都被 `p` 杀掉。

工艺：走**元素层**（`↑(muP K p)` 与 `ZMod p` 是 `rfl` 级 defeq，但实例搜索不穿透 defeq，
故 `Nat.card` 路线拿不到 `Fintype` 实例）。 -/
theorem isPPrimaryTorsion_muP {K : Type} [Field K] (p : ℕ) [Fact p.Prime] :
    IsPPrimaryTorsion p ↑(GaloBase.muP K p) := by
  have hpt : IsPPrimaryTorsion p (ZMod p) := by
    rw [isPPrimaryTorsion_iff]
    intro m
    exact ⟨1, by
      rw [pow_one, ← Nat.cast_smul_eq_nsmul (ZMod p) p m, ZMod.natCast_self p, zero_smul]⟩
  exact hpt

/-! ### 二、L2 桥：`cd_p(K) ≤ 1 ⟹ Subsingleton (H²(G_K, Z/p))` -/

/-- ★★★★★★ **L2 桥**：`cd_p(K) ≤ 1` ⟹ `H²(G_K, μ_p) = 0`（即档 ⑥ 的 `hκ`）。

两件库内机器一步拼：`CohomologicalDimensionLE` 给 `ℤ`-系数侧的消失，
`subsingleton_continuousCohomology_ofDiscreteModule_iff` 把它搬回 `muP`（`ZMod p` 系数）侧。 -/
theorem subsingleton_H2_of_cohomologicalDimensionLE
    {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
    (hcd : CohomologicalDimensionLE.{0} p (AbsoluteGaloisGroup K) 1) :
    Subsingleton (GaloBase.H2 K p) := by
  have h : Subsingleton
      ↑(continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K)
        ↑(GaloBase.muP K p))).toModuleCat :=
    hcd ↑(GaloBase.muP K p) (isPPrimaryTorsion_muP (K := K) p) 2 (by norm_num)
  exact (subsingleton_continuousCohomology_ofDiscreteModule_iff (GaloBase.muP K p) 2).mp h

/-- `TsenHyp` 形态的 L2 桥（档 ⑥ 的 `hκ`）。 -/
theorem subsingleton_H2_of_TsenHyp {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
    (hTsen : TsenHyp K p) : Subsingleton (GaloBase.H2 K p) :=
  subsingleton_H2_of_cohomologicalDimensionLE p hTsen

end TsenBridge

/-! ### 三、装配：档 ⑥ 的 Tsen 形态（`Hyp614` 的消费者） -/

section TameResidueTsen

variable {F' : Type} [Field F'] [ValuativeRel F'] [TopologicalSpace F']
  [HenselianRing ↥𝒪[F'] (IsLocalRing.maximalIdeal ↥𝒪[F'])]

variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F' p]
variable {v : F'ˣ →* Multiplicative ℤ} {π : F'ˣ}

/-- ★★★★★★★ **档 ⑥ 的 Tsen 形态**：`(CI)` ＋ **`cd_p(κ) ≤ 1`** ⟹ `Ch4TameSymbolHyp`。

与 `Hyp614.ch4TameSymbolHyp_of_subsingleton_H2_residueField` 的差别**只有一处**：
`hκ : Subsingleton (H²(κ,μ_p))` 换成 `hTsen : TsenHyp κ p`——即**已发表的 Tsen 形态**
`cd_p(κ) ≤ 1`（`κ = ℂ(t)` 时由 Tsen 定理给出）。 -/
theorem ch4TameSymbolHyp_of_tsen
    {ζ : F'} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F'])) (hpF : IsUnit (p : F'))
    (hv : ValCompat (F := F') v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (φ : ContinuousMonoidHom (AbsoluteGaloisGroup F')
      (AbsoluteGaloisGroup (IsLocalRing.ResidueField ↥𝒪[F'])))
    (hCI : ∀ y : VKG F' p v hpF,
      ∃ a : GaloBase.V (IsLocalRing.ResidueField ↥𝒪[F']) p,
        inflH1 p φ a = (y : GaloBase.V F' p))
    (hTsen : TsenHyp (IsLocalRing.ResidueField ↥𝒪[F']) p) :
    Ch4TameSymbolHyp (F := F') p (v := v) (π := π) hpF :=
  ch4TameSymbolHyp_of_subsingleton_H2_residueField (F' := F') p
    hζ hp hpF hv hπ hp2 φ hCI (subsingleton_H2_of_TsenHyp p hTsen)

/-- ★★★★★ **接入 `Hyp611` 正规形**的 Tsen 形态：`(CI)` ＋ `cd_p(K') ≤ 1` ⟹ `residueSpan = ⊥`。 -/
theorem residueSpan_eq_bot_of_tsen
    (K' : Type) [Field K'] (φ' : ContinuousMonoidHom (AbsoluteGaloisGroup F')
      (AbsoluteGaloisGroup K'))
    (hpF : IsUnit (p : F'))
    (hCI : ∀ y : VKG F' p v hpF,
      ∃ a : GaloBase.V K' p, inflH1 p φ' a = (y : GaloBase.V F' p))
    (hTsen : TsenHyp K' p) :
    residueSpan (GaloBase.cup (K := F') (p := p)) (valLinOf (F := F') (p := p) v hpF) = ⊥ :=
  residueSpan_eq_bot_of_subsingleton_H2 (F' := F') (K' := K') p φ' hpF hCI
    (subsingleton_H2_of_TsenHyp p hTsen)

end TameResidueTsen

end L20261018

#print axioms L20261018.isPPrimaryTorsion_muP
#print axioms L20261018.subsingleton_H2_of_cohomologicalDimensionLE
#print axioms L20261018.subsingleton_H2_of_TsenHyp
#print axioms L20261018.ch4TameSymbolHyp_of_tsen
#print axioms L20261018.residueSpan_eq_bot_of_tsen
