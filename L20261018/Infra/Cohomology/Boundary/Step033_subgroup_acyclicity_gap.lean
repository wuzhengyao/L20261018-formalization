import L20261018.Ch2.Hensel.Inertia.Step027_cd_l_inertia_vanishing

/-!
# S43 R43：**位①段的核心逻辑** ＋ 缺口收敛到「子群无环性」一件

## 一、GS 6.8.5 位①的纯逻辑

GS 6.8.5 位①要证 `H^j(H, C) = 0`（`C` ＝ `M^G(A)/A` 的余核）。长正合列给出

```
… → H^j(H, B) → H^j(H, C) →^{δ} H^{j+1}(H, A) → …
```

于是 `H^j(H,C) = 0` 由**两件单点性**给出：
* `H^j(H,B) = 0`（`B = M^G(A)` 的 `H`-无环性）；
* `H^{j+1}(H,A) = 0`（**（★）**：`Hyp533.gsInputHyp_of_cdLE`）。

⟹ 一个**五行**的抽象引理（本件）：`ker δ = range f` ＋ `Y`、`Z` 单点 ⟹ `X` 单点。

## 二、缺口收敛（本轮实查）

| 需要 | 实查 |
|---|---|
| `H^j(G, DiscreteCoind G ⊥ A) = 0` | ✅ `Coinduced/Acyclic.lean:252` **`instance`（全次数）**；`DimensionShifting/Basic.lean:111/116` 的 `H¹`／`H²` 版 |
| **`H^j(H, DiscreteCoind G ⊥ A) = 0`（子群）** | ❌ **无**：`grep "subsingleton.*DiscreteCoind"` 只命中「同一群 `G`」的版本 |
| 余诱导的传递／拉回（可用来补上一行） | ✅ `Coinduced/Transitivity.lean:156 transIso`、`Coinduced/Pullback.lean:47 pullback` |

**⟹ 缺口从「GS 6.8.5 整段」收敛到「`G`-余诱导在 `H` 上的无环性」一件。**
两条补法：
* **(a)** 用 `transIso`／`pullback` 把 `DiscreteCoind G ⊥ A` 当作 `H`-模拆成 `H`-余诱导的乘积，
  再用「上同调与乘积交换」；
* **(b)** 直接对 `DiscreteCoind G ⊥ A` 的 `H`-上链作显式收缩（照 `Acyclic.lean:252` 的证明手法）。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`subsingleton_of_exact_delta`** | ★★★★ `ker δ = range f` ＋ `Subsingleton Y` ＋ `Subsingleton Z` ⟹ `Subsingleton X`（GS 位①的纯逻辑） |
| `subsingleton_of_exact_delta'` | 同上，`δ` 取 `H¹(H,C) → H²(H,A)` 的具体箭头形态（记法对照） |

## 诚实边界

* 本件**不**证子群无环性（上面 (a)(b) 都未做）。
* 但位①的**逻辑**已机检，且缺口只剩**一件**、有两条明确补法。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

section Abstract

variable {X : Type*} [AddCommGroup X]
  {Y : Type*} [AddCommGroup Y]
  {Z : Type*} [AddCommGroup Z]

/-- ★★★★ **GS 6.8.5 位①的纯逻辑**：若 `δ` 的正核等于 `f` 的像（长正合性），
且 `Y`、`Z` 都是单点（两侧的消失），则 `X` 是单点。

（取 `X = H^j(H,C)`、`Y = H^j(H,B)`、`Z = H^{j+1}(H,A)`、`δ` ＝ 连接同态。） -/
theorem subsingleton_of_exact_delta (δ : X →+ Z) (f : Y →+ X)
    (hex : δ.ker = f.range)
    [Subsingleton Y] [Subsingleton Z] : Subsingleton X := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hx : x ∈ δ.ker := by
    rw [AddMonoidHom.mem_ker]
    exact Subsingleton.elim (δ x) 0
  rw [hex] at hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  show f y = 0
  rw [Subsingleton.elim y 0, map_zero]

/-- 同上，`δ` 写成 `H¹(H,C) →+ H²(H,A)` 的箭头形态（仅作记法对照，便于装配时对号入座）。 -/
theorem subsingleton_of_exact_delta' {H1C H1B H2A : Type*}
    [AddCommGroup H1C] [AddCommGroup H1B] [AddCommGroup H2A]
    (δ : H1C →+ H2A) (f : H1B →+ H1C)
    (hex : δ.ker = f.range)
    [Subsingleton H1B] [Subsingleton H2A] : Subsingleton H1C :=
  subsingleton_of_exact_delta δ f hex

end Abstract

end L20261018

#print axioms L20261018.subsingleton_of_exact_delta
#print axioms L20261018.subsingleton_of_exact_delta'
