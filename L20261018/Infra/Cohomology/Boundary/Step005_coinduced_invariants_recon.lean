import TauCeti.RepresentationTheory.Homological.GroupCohomology.Coinduced

/-!
# R1096（**(R2) 主线的关键侦察：GS 的 `lemma-coinduced-invariants` 在库内「抽象侧」已有，且对任意子群成立**）

## 本轮的内容式侦察（`L46`／`L47`）—— 记路径

| 目录／文件 | 命中 | 意义 |
|---|---|---|
| `RepresentationTheory/Homological/GroupCohomology/Coinduced.lean` | ★ **`groupCohomology.isZero_res_coindBot_succ`**（`S ≤ G` **任意子群**，`n+1 ≥ 1`） | **GS `lemma-coinduced-invariants` 的第二条**（「`H^j(H, M^G(A)) = 0` for all `j>0`」）**原样在库**，且**不需有限性** |
| 同上 | ★ **`TauCeti.groupCohomology.isZero_quotientToInvariants_coindBot_succ`**（`S ◁ G`） | **GS 同一条的第一条 ＋ GS 6.8.6 证明里用的 `H^i(G/H, M^G(A)^H) = 0`** |
| 同上 | `groupCohomology.isZero_coindBot_succ`（同群版） | 已知 |
| 同上（机制） | **`resCoindBotIso S X : res S.subtype (coindBot k G X) ≅ coindBot k S (G ⧸ S → X)`** | ★ 分解的**代数形式**：限制就是「以 `Fun(G⧸S, X)` 为系数」的对 `S` 的余诱导——**陪集积被吸收进系数**，故无需「上同调保乘积」！ |
| `GroupCohomology/{InflationRestriction,LongExactSequence,Shapiro}.lean` | 抽象侧 inflation／LES／Shapiro | GS 6.8.5 其余零件在抽象侧齐备 |
| `ContCohomology/GroupCohomologyIso/{Basic,CoeffMap}.lean` | `explicitH0IsoGroupCohomology` 等（连续↔抽象，低次） | 把抽象结论搬回连续侧的桥（次数 ≤ 2 足够 `∂₂`） |

## 与 R1095 的关系（**这是对 R1095 的建设性回答**）

R1095 查明：战役连续载体 `LC(G,A)` 上**没有** GS 用的分解（「族 ⟹ 函数」不局部常值），故 GS 的证明不能逐字搬。
本轮查明：**该分解在代数（全部函数）侧不仅存在、而且库内已证**，其关键恰是 `resCoindBotIso`：
限制后的模块是**对 `S` 的余诱导**，系数换成 `Fun(G ⧸ S, X)`；由 Shapiro（`S` 上）
`H^{n+1}(S, Coind_⊥^S Y) ≅ H^{n+1}(⊥, Y) = 0` —— **对任意系数 `Y`**，故**无限指数也无妨**。

⟹ **路线 (甲)（回抽象侧）不但忠于 GS，而且成本大幅低于原估计**：GS 的两条零调性已在库内，
`∂₂` 构造所需的 inflation／LES／Shapiro 亦在抽象侧；最后用 `ContCohomology/GroupCohomologyIso` 搬回。

## 本轮机检

把 GS 的两条**按 `∀ j ≥ 1` 重述**（与 GS 原文的 `for all j ≥ 1` 逐字对齐），钉成机检读数。

| 声明 | 内容 |
|---|---|
| **`gs_coind_invariants_restrict`** | `∀ j ≥ 1`, `H^j(S, res S (Coind_⊥^G X)) = 0`（`S ≤ G` **任意**） |
| **`gs_coind_invariants_quotient`** | `∀ j ≥ 1`, `H^j(G ⧸ S, (Coind_⊥^G X)^S) = 0`（`S ◁ G`） |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace L20261018

/-- ★ **GS `lemma-coinduced-invariants` 的第二条**（重述为 `∀ j ≥ 1`；`S ≤ G` **任意子群**，**不需有限性**）。

GS 原文（`raw/GilleSzamuely2017.tex:3611`）：`H^{j}(H,M^{G}(A))=0` for all `j>0`。 -/
theorem gs_coind_invariants_restrict {k G : Type} [CommRing k] [Group G]
    (S : Subgroup G) (X : Type) [AddCommGroup X] [Module k X] :
    ∀ j : ℕ, 1 ≤ j →
      IsZero (groupCohomology (Rep.res S.subtype (Rep.coindBot k G X)) j) := by
  intro j hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact groupCohomology.isZero_res_coindBot_succ S X n

/-- ★ **GS `lemma-coinduced-invariants` 的第一条 ＋ GS 6.8.6 证明里用到的** `H^i(G/H, M^G(A)^H) = 0`
（重述为 `∀ j ≥ 1`；`S ◁ G`）。 -/
theorem gs_coind_invariants_quotient {k G : Type} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] (X : Type) [AddCommGroup X] [Module k X] :
    ∀ j : ℕ, 1 ≤ j →
      IsZero (groupCohomology ((Rep.coindBot k G X).quotientToInvariants S) j) := by
  intro j hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact TauCeti.groupCohomology.isZero_quotientToInvariants_coindBot_succ S X n

end L20261018

#print axioms L20261018.gs_coind_invariants_restrict
#print axioms L20261018.gs_coind_invariants_quotient
