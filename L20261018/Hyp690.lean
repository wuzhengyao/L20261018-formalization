import L20261018.Hyp688
import L20261018.Hyp127

/-!
# S61 R3：**A2 收口** —— `∪(a, 1−a) = 0`（Steinberg 关系，杯积侧）

## 意义（`G2-PLAN.md` §2 的 A2 格）

A1 已给出 `TameSymbolFactors ⟺ ker ∪ ≤ ker tame`（`Hyp689`）；`A3` 已给出**驯符号**侧的
Steinberg 关系 `tame(κa, κ(1−a)) = 0`（`Hyp688`）。本件补**杯积**侧的同一条关系：

```
κ a ∪ κ b = 0        只要  a + b = 1        （＝ `∪(a, 1−a) = 0`）
```

两侧合起来才是 A4（`ker ∪` 由 Steinberg 元生成）所需的关系对。

## 关键侦察读数（`L46`；本轮实测，**不要重走自建路线**）

本轮**没有**自建范数／corestriction／投影公式——TauCeti 全都有（侦察报告见 `S61-A2-RECON.md`）：

| 需要的件 | 库内位置 | 读数 |
|---|---|---|
| **Steinberg 关系（杯积层）** | `ClassFieldTheory.cup_kummerClass_eq_zero_of_add_one`（`Symbol.lean:148`） | ✅ **任意系数配对 `P` 皆成立** |
| 显式层 Steinberg（Tate 的证明） | `TauCeti.explicitCup11_kummerMap_eq_zero_of_add_eq_one`（`Steinberg.lean:149`） | ✅ |
| `μₙ` 载体 ↔ `trivialFp` 载体的杯积相容 | `ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup`（`Symbol.lean:297`） | ✅ |
| `cupFp` ↔ `GaloBase.cup` 的载体桥 | `GaloCupTransport.cupFp_coeffMap_eq_cup`（`Hyp46`） | ✅（`Hyp127` 已用过） |
| `cupFp` 的群变元自然性 | `TauCeti.cupFp_map` | ✅ |
| corestriction／投影公式／`cor∘res = index` | `ContCohomology/Corestriction/`（20 件）＋ `Cup/ProjectionFormula.lean` | ✅（**本件不需要**） |

⟹ 本轮**唯一**的工作是**载体运输**（三段），数学内容是 TauCeti 已证的第 1、2 行。

## 与 `PROMPT-S61` 的差异（诚实登记）

`PROMPT-S61` 把 A2 记为「Hilbert 90／显式余圈」的自建任务。**侦察表明这是「假阻断」**
（规则 17 / L46）：Tate 的证明（范数分解 `Xⁿ − a = ∏ f`、`f(1) = N(1−θ)`、投影公式）已在
TauCeti 的 `FieldTheory/GaloisCohomology/Steinberg.lean` 里完成，且**在任意系数配对上成立**。
本件因此只做运输，零自建数学。

## 机检件

| 声明 | 内容 |
|---|---|
| **`cupFp_kummerClass_eq_zero_of_add_eq_one`** | ★★★★★ `cupFp`（`Field.absoluteGaloisGroup` 载体）上的 Steinberg 关系 |
| **`cup_bridgeKc_of_add_eq_one`** | ★★★★★ `GaloBase.cup (bridgeKc a) (bridgeKc b) = 0`（战役载体，**无**单位滤子／`tr`／剩余特征假设） |
| **`cup_kummerClass_of_add_eq_one`** | ★★★★★ 换成 `KummerBridge.kummerClass`（唯一接口假设：T1 尺度桥） |
| **`cup_kummerClass_oneSub_eq_zero`** | ★★★★★ ★A2 的**最终形态**：`∪(κ a, κ(1−a)) = 0`（与 `Hyp688.tameExpr_kummerClass_oneSub` **严格对偶**） |

## 接口假设（诚实登记，**不是**本件引入的缺口）

`cup_kummerClass_of_add_eq_one` 与 `cup_kummerClass_oneSub_eq_zero` 取**唯一的**接口假设

```
(T1)  ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ, bridgeKc hζ a = c • KummerBridge.kummerClass F p hp a
```

这是战役**既有**的具名缺口（`Hyp127.hUU_of_scale`、`Hyp207`：`(R1-σ)` 与 T1 是**同一条**载体桥），
本件未新增任何假设。**Steinberg 关系对尺度不变**（`cup (c•x) (c•y) = (c·c) • cup x y`，`c ≠ 0`），
故 T1 一旦补上，A2 即无条件成立 —— 这正是把 `bridgeKc` 版本也一并机检的原因。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section SteinbergCup

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p]

/-- ★★★★★ **Steinberg 关系（`cupFp` 载体层）**：`a + b = 1` ⟹ `(a) ⌣ (b) = 0`。

**纯运输**：`μₙ` 载体的 Steinberg（`ClassFieldTheory.cup_kummerClass_eq_zero_of_add_eq_one`，
任意系数配对）经 `muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup` 落到 `trivialFp` 载体。
**不需要** `tr`、剩余特征、单位滤子 —— 与 `Hyp125.cupFp_unit_unit_eq_zero` 的假设集严格更弱。 -/
theorem cupFp_kummerClass_eq_zero_of_add_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hn : IsUnit (p : F)) {a b : Fˣ} (hab : (a : F) + b = 1) :
    TauCeti.cupFp p (Field.absoluteGaloisGroup F)
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1
        (ClassFieldTheory.kummerClass F hn a))
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1
        (ClassFieldTheory.kummerClass F hn b)) = 0 := by
  rw [← ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup (n := p) (hζ := hζ)]
  rw [ClassFieldTheory.cup_kummerClass_eq_zero_of_add_eq_one
    (ClassFieldTheory.kummerCupPairing ζ hζ) hn hab, map_zero]

/-- ★★★★★ **A2 在战役载体上（`bridgeKc` 版）**：`a + b = 1` ⟹ `∪(a) (b) = 0`。

三段运输与 `Hyp127.cup_bridgeKc_unit_unit_eq_zero` 逐字同构，只把「单位滤子」输入换成
Steinberg 关系 ⟹ **假设集严格变弱**（不再需要 `tr`、`¬ ringChar 𝓀 ∣ p`、`unitFiltration`）。 -/
theorem cup_bridgeKc_of_add_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ p) {a b : Fˣ}
    (hab : (a : F) + b = 1) :
    GaloBase.cup (K := F) (p := p) (bridgeKc (F := F) p hζ a)
      (bridgeKc (F := F) p hζ b) = 0 := by
  have hsmall := cupFp_kummerClass_eq_zero_of_add_eq_one (F := F) p hζ
    hζ.neZero'.out.isUnit hab
  have hbig : TauCeti.cupFp p (TauCeti.AbsoluteGaloisGroup F)
      ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
        ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
          (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a)))
      ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
        ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
          (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit b))) = 0 := by
    rw [← TauCeti.cupFp_map (p := p) (G := Field.absoluteGaloisGroup F)
      (H := TauCeti.AbsoluteGaloisGroup F)
      (φ := (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm), hsmall, map_zero]
  rw [show bridgeKc (F := F) p hζ a
        = ContinuousCohomology.coeffMap (GaloTrivialFp.iso F p).hom 1
            ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
              ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
                (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a))) from rfl,
      show bridgeKc (F := F) p hζ b
        = ContinuousCohomology.coeffMap (GaloTrivialFp.iso F p).hom 1
            ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1)
              ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
                (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit b))) from rfl,
      ← GaloCupTransport.cupFp_coeffMap_eq_cup (K := F) (p := p), hbig, map_zero]

end SteinbergCup

/-! ## 尺度桥（T1）→ `KummerBridge.kummerClass` 版

`KummerBridge.kummerClass` 需要 `[HasEnoughRootsOfUnity F p]`，故本段单列。 -/

section Scaled

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- 双线性：`cup (c • x) (c • y) = (c * c) • cup x y`（`GaloBase.cup` 是 `V →ₗ V →ₗ H2`）。 -/
theorem cup_smul_smul (c : ZMod p) (x y : GaloBase.V F p) :
    GaloBase.cup (K := F) (p := p) (c • x) (c • y)
      = (c * c) • GaloBase.cup (K := F) (p := p) x y := by
  have e1 : GaloBase.cup (K := F) (p := p) (c • x)
      = c • GaloBase.cup (K := F) (p := p) x := LinearMap.map_smul _ c x
  have e2 : GaloBase.cup (K := F) (p := p) x (c • y)
      = c • GaloBase.cup (K := F) (p := p) x y := LinearMap.map_smul _ c y
  calc GaloBase.cup (K := F) (p := p) (c • x) (c • y)
      = (c • GaloBase.cup (K := F) (p := p) x) (c • y) := by rw [e1]
    _ = c • GaloBase.cup (K := F) (p := p) x (c • y) := rfl
    _ = c • (c • GaloBase.cup (K := F) (p := p) x y) := by rw [e2]
    _ = (c * c) • GaloBase.cup (K := F) (p := p) x y := by rw [smul_smul]

/-- ★★★★★ **A2（`KummerBridge.kummerClass` 版）**：唯一接口假设 ＝ T1 尺度桥。

Steinberg 关系对尺度**不变**（`cup_smul_smul`：`c² ≠ 0`），故 `bridgeKc` 侧的零点可原样搬回。 -/
theorem cup_kummerClass_of_add_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : F))
    (hT1 : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      bridgeKc (F := F) p hζ a = c • KummerBridge.kummerClass F p hp a)
    {a b : Fˣ} (hab : (a : F) + b = 1) :
    GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
      (KummerBridge.kummerClass F p hp b) = 0 := by
  obtain ⟨c, hc, hscale⟩ := hT1
  have hz : GaloBase.cup (K := F) (p := p)
      (c • KummerBridge.kummerClass F p hp a)
      (c • KummerBridge.kummerClass F p hp b) = 0 := by
    rw [← hscale a, ← hscale b]
    exact cup_bridgeKc_of_add_eq_one (F := F) p hζ hab
  rw [cup_smul_smul] at hz
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  calc GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
        (KummerBridge.kummerClass F p hp b)
      = ((c * c)⁻¹ * (c * c)) • GaloBase.cup (K := F) (p := p)
          (KummerBridge.kummerClass F p hp a)
          (KummerBridge.kummerClass F p hp b) := by
        rw [inv_mul_cancel₀ hc2, one_smul]
    _ = (c * c)⁻¹ • ((c * c) • GaloBase.cup (K := F) (p := p)
          (KummerBridge.kummerClass F p hp a)
          (KummerBridge.kummerClass F p hp b)) := by rw [smul_smul]
    _ = (c * c)⁻¹ • 0 := by rw [hz]
    _ = 0 := smul_zero _

end Scaled

/-! ## A2 的最终形态：`∪(κ a, κ(1−a)) = 0`（与 `Hyp688` 的 `tame` 侧严格对偶） -/

section OneSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ ★**A2（最终形态）**：`∪(κ a, κ(1−a)) = 0`。

与 `Hyp688.tameExpr_kummerClass_oneSub`（`tame(κa, κ(1−a)) = 0`）**严格对偶** —— 两者一起
就是 A4 需要的关系对：Steinberg 元同时落在 `ker ∪` 与 `ker tame` 里。 -/
theorem cup_kummerClass_oneSub_eq_zero {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F))
    (hT1 : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      bridgeKc (F := F) p hζ a = c • KummerBridge.kummerClass F p hp a)
    {a : Fˣ} (ha : a ≠ 1) :
    GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
      (KummerBridge.kummerClass F p hp (oneSub a ha)) = 0 :=
  cup_kummerClass_of_add_eq_one (F := F) p hζ hp hT1 (b := oneSub a ha) (by
    rw [oneSub_coe]
    ring)

end OneSub

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.cupFp_kummerClass_eq_zero_of_add_eq_one
#print axioms L20261018.cup_bridgeKc_of_add_eq_one
#print axioms L20261018.cup_smul_smul
#print axioms L20261018.cup_kummerClass_of_add_eq_one
#print axioms L20261018.cup_kummerClass_oneSub_eq_zero
