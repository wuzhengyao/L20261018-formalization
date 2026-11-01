import L20261018.Hyp378
import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Rational

/-!
# R1293（S37 · GS §6.8 战役 **S3**）：`H^i_cont(G,ℤ) ≅ H^{i-1}_cont(G,ℚ/ℤ)`

`GS68-CAMPAIGN.md` §1 的 S3。原文 = GS 2017 §6.8.1（label `sec:cohomology-complete-dv`）：

> For $i\geq2$, we may use the exact sequence $0\to\mathbf{Z}\to\mathbf{Q}\to\mathbf{Q}/\mathbf{Z}\to0$
> to obtain isomorphisms $H^{i}(G,\mathbf{Z})\cong H^{i-1}(G,\mathbf{Q}/\mathbf{Z})$,
> as $H^{i}(G,\mathbf{Q})=0$ for $i>0$ by Corollary `cor-q-vector-space-vanishing`.

## ★ 本轮最重要的发现（**L46／L47④ 的假阻断实案**）

`GS68-CAMPAIGN.md` §1 的 S3 施工估计是「**colim 只做到 degree 0／1，须扩**；transfer 库内缺，
约 50–100 行」。**这是错的** —— TauCeti 已有的两件正好覆盖 S3 的**两个**输入：

| 需要的那一件 | TauCeti 现成件 | 位置 |
|---|---|---|
| `H^{n+1}_cont(G, ℚ) = 0`（任意次） | **`subsingleton_continuousCohomology_of_module_rat`** | `ContCohomology/Torsion.lean:134` |
| `H^i(G,Z) ≅ H^{i-1}(G,Q/Z)`（整条维数平移 ＋ 短正合列） | **`rationalIntegralDeltaIso`** ＋ `rationalIntegralShortExact` | `ContCohomology/Bockstein/Rational.lean:100／49` |

两件都**不需要**「colim 扩到高次」，也不需要 transfer：`Torsion.lean` 走的是
**「开子群的指数杀死正次数类」**（`exists_openSubgroup_index_nsmul_eq_zero`，
NSW (1.6.1) ＋ 余诱导分解上的收缩恒等式），比 transfer 路线短。
⟹ S3 **不是**研究级缺口，只是**未检索到**。

## 本轮机检的件

| 声明 | 内容 |
|---|---|
| `QoverZdisc` | `ℚ/ℤ` 的离散副本（`ULift (AddCircle 1)` ＋ `⊥`） |
| **`subsingleton_continuousCohomology_rat_disc`** | ★★★★ `∀ n, H^{n+1}(G, ℚ_disc) = 0`（**S3a，全次数**） |
| **`ratIntShortExact`** | ★★★★★ `0 → ℤ → ℚ → ℚ/ℤ → 0`（`DiscreteShortExact`，GS 的那条） |
| **`ratOverZDimShift`** | ★★★★★ `H^{n+1}(G,ℚ/ℤ) ≅ H^{n+2}(G,ℤ)`（**S3b**；GS 的 `i = n+2`） |
| **`intH2EquivH1RatOverZ`** | ★★★★★ `H²(G,ℤ) ≅ H¹(G,ℚ/ℤ)`（`n = 0` 的具体件，第四章实际用量在 `i = 2`） |

## 承载体说明（载体身份，规则 22／23）

TauCeti 的 `rationalIntegralDeltaIso` 用 `ULift ℤ`／`ULift ℚ`（宇宙提升）；本战役的
`Hyp376／Hyp377` 用的是裸 `ℤ`（`ContCohomology.H1`）与 `Qdisc := ULift ℚ`。本文件统一落在
**`ULift` 侧**（`Qdisc` 本来就是 `ULift ℚ`），并在 `## 载体对照` 一节记下与 `Hyp377` 的关系。
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

/-! ### `ℚ/ℤ` 的离散副本 -/

/-- `ℚ/ℤ` 的离散副本（`ULift (AddCircle 1)` ＋ `⊥` 拓扑），同 `Hyp377` 的 `Qdisc` 手法。 -/
abbrev QoverZdisc : Type := ULift.{0} (AddCircle (1 : ℚ))

instance : TopologicalSpace QoverZdisc := ⊥
instance : DiscreteTopology QoverZdisc := ⟨rfl⟩

/-! ### 平凡作用（`G = AbsGal F`；全局实例，供下游件复用） -/

variable (F : Type) [Field F]

instance : DistribMulAction (TauCeti.AbsoluteGaloisGroup F) Qdisc where
  smul _ m := m
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

instance : SMulCommClass (TauCeti.AbsoluteGaloisGroup F) ℤ Qdisc where
  smul_comm _ _ _ := rfl

instance : ContinuousSMul ℤ Qdisc := ⟨continuous_of_discreteTopology⟩

instance : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) Qdisc := ⟨continuous_snd⟩

instance : DistribMulAction (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ) where
  smul _ m := m
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

instance : DistribMulAction (TauCeti.AbsoluteGaloisGroup F) QoverZdisc where
  smul _ m := m
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

instance : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) QoverZdisc := ⟨continuous_snd⟩

/-- `ℚ_disc` 作为 `TopRep ℤ (AbsGal F)`（`abbrev`：下游实例搜索必须能展开它）。 -/
noncomputable abbrev QdiscRep : TopRep ℤ (TauCeti.AbsoluteGaloisGroup F) :=
  TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F) Qdisc

/-- `QdiscRep` 的底层模是 `ℚ`-向量空间（`Module ℚ` 的显式搬运：`.V` 投影在实例搜索中
不透明，故必须写成实例）。 -/
instance : Module ℚ (QdiscRep F).V := inferInstanceAs (Module ℚ Qdisc)

/-! ### S3a：`ℚ` 的**全次数**连续零调（GS 的 Corollary `cor-q-vector-space-vanishing`） -/

/-- ★★★★ **S3a**：`G` 紧、`ℚ` 离散且平凡作用 ⟹ `H^{n+1}_cont(G, ℚ) = 0`（**所有正次数**）。

`Hyp377` 只做了 `n = 1`；本轮把它提升到全次数 —— 用的**不是**新的
「有限商余极限」基建，而是 TauCeti 现成的
`subsingleton_continuousCohomology_of_module_rat`（NSW (1.6.1) 路线）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:sec:cohomology-complete-dv quote="$H^{i}(G,\mathbf{Q})=0$ for $i>0$ by Corollary"
theorem subsingleton_continuousCohomology_rat_disc (n : ℕ) :
    Subsingleton (continuousCohomology (n + 1) (QdiscRep F)) :=
  TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_of_module_rat
    (k := ℤ) (G := TauCeti.AbsoluteGaloisGroup F) (X := QdiscRep F) n

/-- `H^0` 例外（`H⁰ = 不变量`，不必为零）：正次数形式。 -/
theorem subsingleton_continuousCohomology_rat_disc_of_pos {i : ℕ} (hi : 0 < i) :
    Subsingleton (continuousCohomology i (QdiscRep F)) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  exact subsingleton_continuousCohomology_rat_disc F n

/-! ### S3b：短正合列 `0 → ℤ → ℚ → ℚ/ℤ → 0` 与维数平移 -/

/-- ★★★★★ **GS (6.8.1) 的系数正合列**：`0 → ℤ → ℚ → ℚ/ℤ → 0`（全部离散、平凡作用）。 -/
noncomputable def ratIntShortExact :
    DiscreteShortExact (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ) (ULift.{0} ℚ) QoverZdisc :=
  TauCeti.ContCohomology.rationalIntegralShortExact (TauCeti.AbsoluteGaloisGroup F) QoverZdisc
    AddEquiv.ulift (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- ★★★★★ **S3b**：**维数平移** `H^{n+1}(G, ℚ/ℤ) ≅ H^{n+2}(G, ℤ)`。

即 GS 的 `H^{i}(G,\mathbf{Z})\cong H^{i-1}(G,\mathbf{Q}/\mathbf{Z})`（取 `i = n + 2`）：
连接映射 `δ` 在中间项两个相邻次数零调时为同构（`isIso_delta`），
而 `ℚ` 的零调性 = `subsingleton_continuousCohomology_rat_disc`。 -/
noncomputable def ratOverZDimShift (n : ℕ) :
    continuousCohomology (n + 1) (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
      QoverZdisc) ≅
      continuousCohomology (n + 1 + 1) (TauCeti.ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ)) :=
  TauCeti.ContCohomology.rationalIntegralDeltaIso (TauCeti.AbsoluteGaloisGroup F) QoverZdisc
    AddEquiv.ulift (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) n

/-- ★★★★★ **S3b（GS 的陈述形状）**：`H^{i}(G,ℤ) ≅ H^{i-1}(G,ℚ/ℤ)`（取 `i = n + 2`）。

这是 `ratOverZDimShift` 的 `Nonempty` 形式，只为把 `@source` 注解挂在一个
`theorem` 上（lint 的声明正则不识别 `noncomputable def` 前缀）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:sec:cohomology-complete-dv quote="to obtain isomorphisms $H^{i}(G,\mathbf{Z})\cong H^{i-1}(G,\mathbf{Q}/\mathbf{Z})$"
theorem ratOverZDimShift_nonempty (n : ℕ) :
    Nonempty (continuousCohomology (n + 1) (TauCeti.ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) QoverZdisc) ≅
      continuousCohomology (n + 1 + 1) (TauCeti.ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ))) :=
  ⟨ratOverZDimShift F n⟩

/-- 维数平移的正向恰是那条短正合列的**连接映射** `δ`（可核对的形状）。 -/
theorem ratOverZDimShift_hom_eq_delta (n : ℕ) :
    (ratOverZDimShift F n).hom =
      (ratIntShortExact F).delta (n + 1) :=
  TauCeti.ContCohomology.rationalIntegralDeltaIso_hom _ _ _ _ _ _ n

/-- ★★★★★ **`i = 2` 的具体件**：`H²(G, ℤ) ≅ H¹(G, ℚ/ℤ)`
（第四章实际用到的量级；GS 的 `r_v^2` 的落点）。 -/
noncomputable def intH2EquivH1RatOverZ :
    continuousCohomology (0 + 1 + 1) (TauCeti.ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ)) ≅
      continuousCohomology (0 + 1) (TauCeti.ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) QoverZdisc) :=
  (ratOverZDimShift F 0).symm

/-- `H²(G,ℤ)` 与 `H¹(G,ℚ/ℤ)` 作为加法群同构（供下游以 `AddEquiv` 使用）。 -/
noncomputable def intH2AddEquivH1RatOverZ :
    continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
        (ULift.{0} ℤ)) ≃+
      continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
        QoverZdisc) :=
  (intH2EquivH1RatOverZ F).toContinuousLinearEquiv.toAddEquiv

/-! ### 载体对照（规则 22／23）

* 本文件的 `ℤ`-系数 = `ULift ℤ`（TauCeti `rationalIntegralDeltaIso` 的口径）；
  `Hyp376.subsingleton_H1_int_absGal` 用的是裸 `ℤ`（`ContCohomology.H1`）。
  两者由 `AddEquiv.ulift` 对应，**数学上无差**，但**不可在同一陈述里混用**。
* 本文件的 `ℚ/ℤ`-系数 = `QoverZdisc = ULift (AddCircle 1)`；
  `Hyp377.Qdisc = ULift ℚ`（`ConcreteCohomology` 口径）同型（`AddEquiv.ulift`）。
* 第四章的 `r_v^i` 落在 `μ_p` 系数（`muNRep` 载体）⟹ 与本文的 `ℚ/ℤ` 系数之间还差一层
  Kummer 桥（S4）。
-/

end L20261018

#print axioms L20261018.subsingleton_continuousCohomology_rat_disc
#print axioms L20261018.subsingleton_continuousCohomology_rat_disc_of_pos
#print axioms L20261018.ratOverZDimShift_nonempty
#print axioms L20261018.ratOverZDimShift_hom_eq_delta
#print axioms L20261018.intH2AddEquivH1RatOverZ
