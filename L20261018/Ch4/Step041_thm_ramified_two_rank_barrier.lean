import L20261018.Ch3.BiKummer.Step017_rank_barrier_unconditional

/-!
# S62 R28：**4.3(2)** —— 论文 `thm:ramified` 的**第二条**（`rank Φ ≥ 3`）

## 为什么补这一条

用户指出：`comparator` 只验证 `config.json` 里列出的陈述，**不做覆盖率检查**；
而 4.3 有 (1)(2) 两条，此前只形式化了 (1)（`thm_ramified_1_paper`）⟹
「comparator 通过」**不能**读作「第 4 章 100%」。本件补上 (2)。

## 内容与出处

论文 4.3(2)（`raw/L20261018.tex:1635` 逐字）：「共同杯积映射满足 $\rank(\Phi)\ge3$。」
其证明（`:1643`）是「将 $\ind(D)=p^2$ 代入定理~\ref{thm:rank-barrier}(2)」——
本件即该代入的**无参数版**：`L20261018.theorem_3_2_2_kummer'`（`Hyp86:66`，
`thm:rank-barrier`(2) 的消参升档版，已机检）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`thm_ramified_2_paper`** | ★★★★★ **4.3(2)**：`ind(cup(κa₁,b₁)+cup(κa₂,b₂)) = p²` ⟹ `3 ≤ rank Φ` |

## 诚实边界

* `ind` 用 `Hyp82.indOfH2`（论文的「`Br` 类里除代数的指数」）。
* `hne : paperCup ≠ 0` 与 4.3(1) 同一条假设（论文 4.3 开头亦设 $(a_1)\cup(a_2)\ne0$）。
* 本件不证 `thm:rank-barrier`(2)（那是第 3 章 3.2(2)，已在 `Hyp86` 机检）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section ThmRamified2

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **4.3(2)（`thm:ramified` 第二条）**：`ind(D) = p²` ⟹ `rank Φ ≥ 3`。

`D` 的类取 `GaloBase.cup (κ a₁) b₁ + GaloBase.cup (κ a₂) b₂`（论文的 `(a₁,b₁)⊗(a₂,b₂)`），
`Φ x = (x∪(a₁), x∪(a₂))`。 -/
-- @source file=raw/L20261018.tex locator=line:1635 quote="\item 共同杯积映射满足 $\rank(\Phi)\ge3$。"
theorem thm_ramified_2_paper (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {a1 a2 : Fˣ}
    (hne : paperCup (F := F) (p := p) hp a1 a2 ≠ 0) (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2) :
    (3 : Cardinal) ≤ Module.rank (ZMod p)
      ↥(biKummerDataKummer (F := F) (p := p) hp a1 a2 hne).Phi.range :=
  theorem_3_2_2_kummer' (F := F) (p := p) hp hp2 a1 a2 hne b1 b2 hD

end ThmRamified2

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.thm_ramified_2_paper
