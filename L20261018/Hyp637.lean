import L20261018.Hyp636

/-!
# S53 R29：**商群层的余圈** —— `Hyp632` 的两条搬到 `Γ_F ⧸ I` 上（`Hyp637`）

## 0 本轮目标（`PROMPT-S53` §① 的 **A**）

`Hyp636` 交付了下降件 `kummerCocycleQuot : Γ_F ⧸ I → F̄`，但只到「能下降」为止。
本轮把 `Hyp632` 的两条余圈性质搬到**商群层**，并补上 `Hyp636` 文件头**声称但未落盘**的
`kummerCocycleQuot_mk`（见 §4 登记）。

| 性质 | 商群层陈述 |
|---|---|
| 取值公式 | `cq (mk σ) = c(σ)`（`Hyp636` 头部的表里列了它，**实际未声明**） |
| **余圈恒等式** | `cq (mk (στ)) = cq (mk σ) · σ (cq (mk τ))` |
| **值在 `μ_p`** | `cq (mk σ)^p = 1` |
| 单位元 | `cq (mk 1) = 1` |

## 1 ★★★★★ 本轮真正的数学增量：**惯性群固定 `μ_p`**

商群层的余圈恒等式若要写成「`Γ⧸I` 作用在系数上」的形式，**必须**先有

```
σ ∈ I, ζ^p = 1  ⟹  σ ζ = ζ        （`I` 在 `μ_p ⊂ F̄` 上平凡）
```

否则 `σ (cq (mk τ))` 依赖代表元的选取（`σ` 换成 `σh`、`h ∈ I` 时值会变）。
本轮机检了这一条（`inertia_fixes_pow_eq_one_of_rootOfUnity`）：
它是 `Hyp631.inertia_fixes_pow_root_of_unit` 在 `x = 1`（`u = 1` 是赋值单位）处的**直接特例**
——`μ_p ⊂ F̄` 的每个元素都是「`1 ∈ 𝒪[F]ˣ` 的 `p` 次根」。

⟹ 从此 `Γ_F ⧸ I` 在 `μ_p` 上的作用**良定义**，`(CI)`／`(N5)` 的 inflation 侧有了系数层。

## 2 本件交付（全机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| **`kummerCocycleQuot_mk`** | 取值公式（**补 `Hyp636` 的登记缺口**） |
| **`kummerCocycleQuot_one`** | `cq (mk 1) = 1` |
| **`kummerCocycleQuot_mul`** | ★★★★★ 商群层余圈恒等式（代表元形态 `mk (στ)`） |
| **`kummerCocycleQuot_mul_quot`** | ★★★★★ 同上，**商群乘法形态** `mk σ * mk τ`（带 `[hN : I.Normal]`） |
| **`kummerCocycleQuot_pow_eq_one`** | ★★★★★ 值在 `μ_p` |
| **`inertia_fixes_pow_eq_one_of_rootOfUnity`** | ★★★★★★ **`I` 在 `μ_p` 上平凡**（商群作用的良定义前提） |
| `kummerUnit_mem_rootsOfUnity` | `kummerUnit` 落在 `rootsOfUnity p ↥𝒪_W` 里（**系数的载体层**） |
| `kummerCocycleQuot_mem_rootsOfUnity` | `cq (mk σ) ∈ μ_p(F̄)`（同上，`F̄` 层） |

## 3 工艺（三条，皆本轮实付）

* **`rfl` 级**：`kummerCocycleQuot_mk` 是 `rfl`（`Quotient.lift` 在 `mk` 上的计算规则），
  不需要 `Quotient.lift_mk`（后者与 `QuotientGroup.mk` 的 `Setoid` 元变量不统一）。
* **`QuotientGroup.mk` 的乘法形态要实例**：`mk σ * mk τ` 的 `HMul` 搜索**超时**（不是失败），
  故把带 `*` 的陈述单独放进带 `[hN : (inertia W hval).Normal]` 的 section（`inertia_normal` 不是实例）；
  代表元形态（`mk (σ * τ)`）**不需要**任何实例，作为主陈述。
* **`hα` 的层转换**：`α^p = algebraMap ↥𝒪[F] F̄ ↑x` 转 `F` 层写 `rw [hα]; rfl`
  （`algebraMap F F̄ (↑x : F) = algebraMap ↥𝒪[F] F̄ ↑x` 是 `rfl` 级，同 `Hyp634`）。

## 4 登记：`Hyp636` 文件头的**声称-落盘不一致**（本轮修复）

`Hyp636.lean` 的头表列了 `kummerCocycleQuot_mk`（「取值公式」），但**该文件没有这条声明**
（`grep -c "kummerCocycleQuot_mk" Hyp636.lean` 只命中注释区）。本轮把它**真的**落盘。
⟹ 教训（登记进 `LESSONS` D 组）：**头表里的交付清单必须由 `grep` 核对**，不能手写。

## 5 诚实边界

* **未做**：送进 `H¹(Γ_F, μ_p)`／`H¹(I, μ_p)`（`Z¹`／restriction 的载体等同）——`PROMPT-S53` §① 的 **B**。
* **未做**：`hLoc`（= **C**）／`κ ↪ κ̄`（= **D**）／N3 后半（= **E**）。
* 本件**不**声称 `(CI)`；**不增覆盖率**（`(R2)` 仍 `∅-open`，**不得读作「否」**）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section QuotLevel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- **取值公式**：下降后的余圈在 `mk σ` 上取值 `c(σ)`（`Hyp636` 头表声称、实际未落盘的一条）。 -/
theorem kummerCocycleQuot_mk {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk σ)
      = kummerCocycle (F := F) (α := α) σ := rfl

include hval hO in
/-- **单位元条件**：`cq (mk 1) = 1`。 -/
theorem kummerCocycleQuot_one {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    kummerCocycleQuot W hO hval hp hpun hα0 hα
        (QuotientGroup.mk (1 : SeparableClosure F ≃ₐ[F] SeparableClosure F)) = 1 := by
  rw [kummerCocycleQuot_mk]
  exact kummerCocycle_one hα0

include hval hO in
/-- ★★★★★ **商群层的余圈恒等式**（代表元形态）：`cq (mk (στ)) = cq (mk σ) · σ (cq (mk τ))`。

右端的 `σ (cq (mk τ))` 依赖 `σ` 本身（而非 `σ` 的像）——**这正是 `I` 在 `μ_p` 上必须平凡的原因**；
该良定义性由本件 `inertia_fixes_pow_eq_one_of_rootOfUnity` 供给。 -/
theorem kummerCocycleQuot_mul {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ τ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk (σ * τ))
      = kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk σ)
        * σ (kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk τ)) := by
  simp only [kummerCocycleQuot_mk]
  exact kummerCocycle_mul hα0 σ τ

include hval hO in
/-- ★★★★★ **商群层的余圈恒等式**（商群乘法形态）：`cq (mk σ * mk τ) = cq (mk σ) · σ (cq (mk τ))`。

`[hN : I.Normal]` 是 `⧸` 上的群结构所需（`inertia_normal` 不是 `instance`，故显式带入）。 -/
theorem kummerCocycleQuot_mul_quot {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    [hN : (inertia W hval).Normal]
    (σ τ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    kummerCocycleQuot W hO hval hp hpun hα0 hα
        ((QuotientGroup.mk σ : (SeparableClosure F ≃ₐ[F] SeparableClosure F) ⧸ (inertia W hval))
          * QuotientGroup.mk τ)
      = kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk σ)
        * σ (kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk τ)) := by
  rw [← QuotientGroup.mk_mul (inertia W hval) σ τ]
  exact kummerCocycleQuot_mul W hO hval hp hpun hα0 hα σ τ

include hval hO in
/-- ★★★★★ **值在 `μ_p` 里**（商群层）：`cq (mk σ)^p = 1`。 -/
theorem kummerCocycleQuot_pow_eq_one {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    (kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk σ)) ^ p = 1 := by
  rw [kummerCocycleQuot_mk]
  have hαF : α ^ p = (algebraMap F (SeparableClosure F)) (((x : (↥𝒪[F])ˣ) : ↥𝒪[F]) : F) := by
    rw [hα]
    rfl
  exact kummerCocycle_pow_eq_one hα0 hαF σ

include hval hO in
/-- **`cq (mk σ)` 落在 `F̄` 的 `p` 次单位根群 `μ_p` 里**（系数的载体层，`F̄` 口径）。 -/
theorem kummerCocycleQuot_mem_rootsOfUnity {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    Units.mk0 (kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk σ))
        (by
          intro h
          have h1 := kummerCocycleQuot_pow_eq_one W hO hval hp hpun hα0 hα σ
          rw [h, zero_pow hp] at h1
          exact zero_ne_one h1)
      ∈ rootsOfUnity p (SeparableClosure F) := by
  rw [mem_rootsOfUnity]
  refine Units.ext ?_
  show (kummerCocycleQuot W hO hval hp hpun hα0 hα (QuotientGroup.mk σ)) ^ p = 1
  exact kummerCocycleQuot_pow_eq_one W hO hval hp hpun hα0 hα σ

end QuotLevel

/-! ## `I` 在 `μ_p` 上平凡 —— 商群作用的良定义前提 -/

section RootsOfUnityFixed

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- ★★★★★★ **惯性群固定 `μ_p ⊂ F̄`**：`σ ∈ I`、`ζ^p = 1` ⟹ `σ ζ = ζ`。

数学：`ζ^p = 1` ⟹ `W ζ = 1`（值群无挠）⟹ `ζ ∈ 𝒪_Wˣ`；`σ ζ / ζ` 是 `p` 次单位根且 `≡ 1 mod 𝔪_W`
⟹ 由 `μ_p ↪ κ̄^×`（`p` 在 `κ̄` 里可逆）得 `σ ζ / ζ = 1`。

形式上它是 `Hyp631.inertia_fixes_pow_root_of_unit` 在 `x = 1` 处的特例——
**`μ_p` 的每个元素都是 `1 ∈ 𝒪[F]ˣ` 的 `p` 次根**，故不需要任何新的算术。 -/
theorem inertia_fixes_pow_eq_one_of_rootOfUnity {p : ℕ} (hp : p ≠ 0)
    (hpun : IsUnit (p : ↥𝒪[F])) {ζ : SeparableClosure F} (hζ : ζ ^ p = 1)
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hσ : σ ∈ inertia W hval) :
    σ ζ = ζ := by
  have hα : ζ ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((1 : (↥𝒪[F])ˣ) : ↥𝒪[F]) := by
    simpa using hζ
  exact inertia_fixes_pow_root_of_unit W hO hval hp hpun hα σ hσ

include hval hO in
/-- ★★★★★ **`kummerUnit` 落在 `rootsOfUnity p ↥𝒪_W` 里**（系数的赋值环口径）。 -/
theorem kummerUnit_mem_rootsOfUnity {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    kummerUnit W (hval := hval) (hO := hO) hp hpun hα0 hα σ
      ∈ rootsOfUnity p (↥W.valuationSubring) := by
  rw [mem_rootsOfUnity]
  exact kummerUnit_pow_eq_one W hO hval hp hpun hα0 hα σ

end RootsOfUnityFixed

/-! ## 假设类的非空见证（L1 ＋ L10①） -/

section Witness

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- **L1／L10① 非空见证**：`σ = 1`（`1 ∈ I` 恒成立）时主定理对**任意** `p` 次单位根 `ζ` 适用
——故 `inertia_fixes_pow_eq_one_of_rootOfUnity` 的假设类非空，且结论不是只在 `ζ = 1` 处的退化陈述。

注意：本条的结论本身是 `AlgEquiv.one_apply` 级的**平凡**结论，但它**经由主定理**得到，
故其作用是证明**假设束可满足**（`σ ∈ I` 有见证、`hpun` 与 `hp` 不冲突）。 -/
theorem inertia_one_fixes_pow_eq_one {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {ζ : SeparableClosure F} (hζ : ζ ^ p = 1) :
    (1 : SeparableClosure F ≃ₐ[F] SeparableClosure F) ζ = ζ :=
  inertia_fixes_pow_eq_one_of_rootOfUnity W hO hval hp hpun hζ 1 (Subgroup.one_mem _)

end Witness

end L20261018

#print axioms L20261018.kummerCocycleQuot_mk
#print axioms L20261018.kummerCocycleQuot_one
#print axioms L20261018.kummerCocycleQuot_mul
#print axioms L20261018.kummerCocycleQuot_mul_quot
#print axioms L20261018.kummerCocycleQuot_pow_eq_one
#print axioms L20261018.kummerCocycleQuot_mem_rootsOfUnity
#print axioms L20261018.inertia_fixes_pow_eq_one_of_rootOfUnity
#print axioms L20261018.kummerUnit_mem_rootsOfUnity
#print axioms L20261018.inertia_one_fixes_pow_eq_one
