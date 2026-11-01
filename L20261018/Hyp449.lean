import Hyp433
import Hyp448

/-!
# S39 第 23 轮（B 第 19 步）：**把 `∂₂` 登记为具名假设**（`Hyp449`）

## 本轮的裁决与登记

### (乙) 侦察结论：**不可行**

「不经 `∂₂` 造分离泛函」的两条可能机制经 L46 式内容检索均**不在库**：
* **Brauer 剩余 `∂_Br : Br(F)[p] → H¹(κ, ℤ/p)`** —— TauCeti 的 Brauer 材料是二次型／2-挠
  （`RegularFormClass/Hasse`、Clifford 不变量），**没有**一般的驯剩余映射。
* 战役内的 `H2Bridge.brOfH2` 只承担「`D ↦ Σ(aᵢ)∪(bᵢ)` 的上同调模型」，**无**剩余。

### (甲) 的可行性：**同样需自建**

Tate 扭曲需要在惯性 `I` 上看分圆特征 `χ` 对 `μ_p^{⊗j}` 的作用。
战役的 `Hyp380` 有 `I` 的闭性／正规性／`galoisQuotientInertiaEquivZHat`，但**没有** `χ` 作用于 `μ_p`。
TauCeti 只有 `inertiaSubgroup`（椭圆曲线用），亦无 `χ`。

⟹ **两条「造 `d`」的路都需自建大件**。按本仓纪律（L1＋L10①、`hyp-*.md` 类型锁定），
本轮把 `∂₂` 的存在**登记为具名假设**，并给**非空见证**，使 4.2／4.3(1)／4.4 成为
**条件性定理**（本仓认可的形式：「引用外部已发表定理写成具名假设（`hyp-*.md` ＋ 类型锁定）
即得可标 ✓ 的条件定理」）。

## 机检件

| 件 | 内容 |
|---|---|
| **`Ch4TameSymbolHyp`** | ★★★★★ 具名假设（`Prop`，类型锁定）：`∃ d` 满足 `∂₂` 的两条值性质 |
| **`ch4TameSymbolHyp_iff_disjoint`** | ★★★★ 与 `Disjoint` 等价（由 `Hyp432`） |
| **`ch4TameSymbolHyp_of_dependent`** | ★★★★★ **非空见证**（L1＋L10①）：`ker v̄` 一维时假设成立（覆盖有限残域） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section Ch4Hyp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **第 4 章的具名假设**（`hyp-ch4-tame-symbol` 的 Lean 侧，类型锁定）：

**驯符号分离泛函 `∂₂` 存在** —— 即存在 `d : H²(F, Z/p) → ker v̄` 使
`d(单位杯积) = 0`、`d(y ∪ π) = y`。

论文的 `∂₂`（GS 6.8.8）由构造给出；本战役**未**形式化其带 Tate 扭曲的系数层
（见 `Hyp449` 文件头的 (甲)/(乙) 侦察），故此处作为**具名假设**锁定。 -/
def Ch4TameSymbolHyp (hpF : IsUnit (p : F)) : Prop :=
  ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
    (∀ y z : VKG F p v hpF,
      d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p)) (z : GaloBase.V F p)) = 0) ∧
    (∀ y : VKG F p v hpF,
      d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p))
        (KummerBridge.kummerClass F p hpF π)) = y)

/-- ★★★★ 具名假设与 `Disjoint`（`R2′`）**等价**（由 `Hyp432` 的双向机检）。 -/
theorem ch4TameSymbolHyp_iff_disjoint {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF
      ↔ Disjoint
          (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
            (KummerBridge.kummerClass F p hpF π)).range
          (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)) :=
  (disjoint_iff_exists_residueMap (F := F) (p := p) (v := v) (π := π) hζ hp hpF hv hπ hp2).symm

/-- ★★★★★ **非空见证（L1 ＋ L10①）**：若 `ker v̄` 一维（`Hyp138.ker_dependent` 的类无关版，
**覆盖有限残域／完备情形**），则具名假设**成立**。

⟹ 该假设类**非空**，且案例（`κ = ℂ(t)`）落在其**外部**（那里 `dim ker v̄ = ∞`）——
这正是本假设的**精确残余**。 -/
theorem ch4TameSymbolHyp_of_dependent {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p))
    (hdep : ∀ y z : GaloBase.V F p,
      valLinOf (F := F) (p := p) v hpF y = 0 → valLinOf (F := F) (p := p) v hpF z = 0 →
      y ∈ ZMod p ∙ z ∨ z ∈ ZMod p ∙ y) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  (ch4TameSymbolHyp_iff_disjoint (F := F) (p := p) (v := v) (π := π) hζ hp hpF hv hπ hp2).mpr
    (disjoint_of_dependent (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)
      (fun x => cup_self_free (F := F) (p := p) hp2' x) hdep)

end Ch4Hyp

end L20261018

#print axioms L20261018.ch4TameSymbolHyp_iff_disjoint
#print axioms L20261018.ch4TameSymbolHyp_of_dependent
