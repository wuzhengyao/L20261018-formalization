import L20261018.Hyp213
import L20261018.Hyp210
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialGroup

/-!
# S63 R1：把 C2（Hochschild–Serre 跨零）的缺口压成**一条具名假设**

## 缺口定位（`S63-C2-PLAN.md` §2 的机器版）

GS 的 `Construction 6.8.1`（`raw/GilleSzamuely2017.tex:9438–9490`）造
`∂^i : H^i(G,A) → H^{i-1}(G/H, H¹(H,A))` 的四步里，**只有一步**用到 `M^G(A) = Coind_1^G A`
**在子群 `H` 上**的零调性：

```
H^j(H, M^G(A)) = 0                    (j ≥ 1)   ← 唯一缺口
H^j(H, C) ≅ H^{j+1}(H, A) = 0        (j ≥ 1)   ← 由上 ＋ cd(H) ≤ 1
Inf : H^1(G/H, C^H) → H^1(G,C) 同构            ← 由上（五项正合列）
H^1(G, C) ≅ H^2(G, A)                          ← 环境群，库内已有（Hyp210／Hyp213）
C^H → H^1(H, A)                                ← H-不变量的连接映射
```

TauCeti 的 `subsingleton_continuousCohomology_discreteCoind_bot` 只给**环境群** `G` 的零调性；
`Shapiro/AllDegrees` 的 `shapiroIso : H^n(G, Coind_U^G A) ≅ H^n(U, A)` 形状不对（同一个 `U`；
本战役要的是 `H^n(H, Coind_1^G A)`）。
**故 `H^j(H, Coind_1^G A) = 0` 是 C2 的唯一未证输入。**

## 本件机检内容

| 声明 | 内容 |
|---|---|
| **`CoindSubgroupAcyclic`** | ★★★★★ **具名假设**：`∀ j ≥ 1, Subsingleton (H^j(H, Coind_1^G A))` |
| **`coindShortExactSubgroup`** | `DiscreteShortExact H A (Coind_1^G A) Q`（`Hyp213` 的 `H` 版，同一批映射） |
| **`subsingleton_cohomology_quot_subgroup`** | ★★★★★ **GS 6.8.1 第二步在 `H` 上**：`cd(H) ≤ 1` ＋ 具名假设 ⟹ `H^j(H,Q) = 0 (j ≥ 1)` |

⟹ C2 的剩余工作 = **一条**零调性假设；其余（`(6.15)`、`C^H → H¹(H,A)`、`∂²` 良定义）都是
库内长正合列／五项正合列的机械推导。

## 下一轮的精确靶子（`S63-C2-PLAN.md` §3）

`CoindSubgroupAcyclic` 的路线（已核过的三条）：
* **有限指数 `V ⊇ H`**：`Coind_1^G A ≅ C(V, A^{[G:V]})` 作为 `V`-模（右陪集分解）
  ⟹ 右端是 `Coind_1^V(·)` ⟹ TauCeti 零调性（`subsingleton_continuousCohomology_discreteCoind_bot`）；
* **一般闭 `H`**：`TauCeti.ContinuousCohomology.resolutionMap_subgroupSubtype_eq_zero_iff`
  （`ClosedSubgroup.lean`：`H^n(H,X) = colim_{H ≤ V open} H^n(V,X)`）把 `H` 化成开子群上查；
* ⛔ **不可用**无穷乘积路线（`∏_{G/H} Coind_1^H A`）：`continuousCohomology` 的载体是
  `(C(G,⋯C(G,X)))^G` 而非 `Ext`，无穷乘积与离散拓扑不交换。

## 诚实边界（L16／`D30`）

* 本件的具名假设**未被解除**；`FRONTIER` 的「残域有限 = 0」判据**不变**（不涉及 `[Finite 𝓀]`）。
* 假设类**非空**：取 `H = ⊥`，`CoindSubgroupAcyclic ⊥` 即
  `subsingleton_continuousCohomology_discreteCoind_bot`（下面的 `coindSubgroupAcyclic_bot`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- ★★★★★ **C2 的唯一具名假设**（GS 6.8.1 的第一步）：余诱导模 `Coind_1^G A` 在闭子群 `H` 上零调。

L16 载体身份：`H` 的模结构 = `G`-模结构沿 `H ↪ G` 的**拉回**（不是 `DiscreteCoind H ⊥ A`）。 -/
def CoindSubgroupAcyclic (H : Subgroup G) : Prop :=
  ∀ (j : ℕ), 1 ≤ j → Subsingleton (continuousCohomology j
    (ofDiscreteModule ℤ ↥H (DiscreteCoind G ⊥ A)))

/-- **假设类非空**（L1／L10① 非空实例义务）：`H = ⊥` 时 `↥⊥` 是平凡群，正次数上同调必零
（库内 `subsingleton_continuousCohomology_succ_of_subsingleton`）。 -/
theorem coindSubgroupAcyclic_bot : CoindSubgroupAcyclic (G := G) (A := A) ⊥ := by
  intro j hj
  haveI : Subsingleton ↥(⊥ : Subgroup G) :=
    ⟨fun a b => Subtype.ext (by
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, (Nat.sub_add_cancel hj).symm⟩
  exact inferInstance

section Subgroup

variable (H : Subgroup G) [IsClosed (H : Set G)]

instance : CompactSpace ↥H := isCompact_iff_compactSpace.mp (‹IsClosed (H : Set G)›).isCompact

/-- **`Hyp213.coindShortExact` 的 `H` 版**：同一批映射（`coindIncl`／`CoindQuot.proj`），
只是在 `H`-模结构（`G`-模沿 `H ↪ G` 的拉回）下重述等变性。 -/
def coindShortExactSubgroup :
    ContCohomology.DiscreteShortExact ↥H A (DiscreteCoind G ⊥ A) (Q (G := G) (A := A)) where
  incl := coindIncl (G := G) (A := A)
  proj := CoindQuot.proj (G := G) (A := A)
  incl_equivariant := fun h a => coindIncl_equivariant (g := (h : G)) a
  proj_equivariant := fun h m => proj_equivariant (g := (h : G)) m
  incl_injective := coindIncl_injective
  proj_surjective := CoindQuot.proj_surjective
  exact := fun m => CoindQuot.proj_eq_zero_iff (G := G) (A := A) m

/-- **GS 6.8.1 第二步在子群 `H` 上**：`cd(H) ≤ 1` ＋ **余诱导模在 `H` 上零调** ⟹
`H^j(H, Q) = 0 (j ≥ 1)`，其中 `Q = Coind_1^G A ⧸ A`（`Hyp213`）。

证明 = `Hyp210.subsingleton_cohomology_three_of_acyclic`（环境群取 `H`）＋
`Hyp213.coindShortExact` 的 `H` 版（`coindShortExactSubgroup`）。 -/
theorem subsingleton_cohomology_quot_subgroup
    (hB : CoindSubgroupAcyclic (G := G) (A := A) H)
    (hA : ∀ k, 2 ≤ k → Subsingleton (continuousCohomology k (ofDiscreteModule ℤ ↥H A)))
    {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (continuousCohomology j (ofDiscreteModule ℤ ↥H (Q (G := G) (A := A)))) :=
  subsingleton_cohomology_three_of_acyclic (G := ↥H)
    (coindShortExactSubgroup (G := G) (A := A) H) hA hB hj

end Subgroup

end L20261018

#print axioms L20261018.coindSubgroupAcyclic_bot
#print axioms L20261018.coindShortExactSubgroup
#print axioms L20261018.subsingleton_cohomology_quot_subgroup
