import L20261018.Hyp512
import L20261018.Hyp508
import TauCeti.Topology.Algebra.Group.Profinite.Procyclic
import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic
import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Containment
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Procyclic

/-!
# S43 R19（S3c 的**群论核心**）：procyclic 群的 **ℓ-部分就是它的 ℓ-Sylow**

## 本件在（★）的哪一格

（★）＝「惯性群 `I` 的 ℓ-Sylow ≅ `ℤ_ℓ`」（ℓ ≠ char κ）。
S42 把（★）拆成 S2（Sylow 化到 `I/P_K`）／S3c／S4。S3c 一直被当作「唯一有技术风险的一步」，
`S42-S3-ASSESSMENT` §6 甚至判定它需要「2–3 轮基建」（主分解 ＋ 相容原始根族 ＋ 逆极限投影满射）。

**本件把 S3c 的概念障碍彻底拆掉**：不需要 Eisenstein 塔、不需要主分解、不需要相容原始根族。

### 关键的库内命中（S43 R19 侦察，七件全在 TauCeti）

| 件 | 位置 | 作用 |
|---|---|---|
| `zHat.idem.{0} p` | `ZHat/Decomposition.lean:201` | `ℤ̂` 的 **`p`-进幂等元** `ω_p`（`p` 分量为 `1`，其余为 `0`） |
| `zpowHat`（`x ^ᶻ a`） | `ZHat/Pow.lean:83` | **profinite 幂** |
| `zpowHat_mul` | `ZHat/Pow.lean:142` | `x ^ᶻ (a*b) = (x ^ᶻ a) ^ᶻ b` |
| `isProP_closedZpowers_zpowHat_idem` | `Procyclic.lean:113` | **`x ^ᶻ ω_p` 的闭循环子群是 pro-`p`** |
| `zpowHat_idem_of_isProP` | `Procyclic.lean:85` | pro-`p` 群里 `x ^ᶻ ω_p = x` |
| `isProPSylow_iff_isProP_and_maximal` | `Sylow/Containment.lean:151` | Sylow ⟺ pro-`p` ＋ 极大 |
| `IsProP.padicPowEquiv` | `ProP/Procyclic.lean:135` | pro-`p` ＋ procyclic ＋ 非挠 ⟹ `≅ₜ* ℤ_p` |

## 数学内容

设 `G` procyclic，`x` 是它的拓扑生成元（`closedZpowers x = ⊤`）。令

```
P_p := closedZpowers (x ^ᶻ ω_p)        -- x 的「p-部分」
```

则 **`P_p` 是 `G` 的唯一 Sylow pro-`p` 子群**，且 `P_p ≅ₜ* ℤ_p`（当 `P_p` 无限时）。

**证明（本件核心）**：先取一个已知的 Sylow `Q ⊇ P_p`（`IsProP.exists_le_isProPSylow`），
只需证 `Q ≤ P_p`。取 `q ∈ Q`：

* `Q` 是 Sylow ⟹ **闭**（`IsProPSylow.isClosed`）⟹ `↥Q` 紧，可以在其中用 `zpowHat`；
* `Q` pro-`p` ⟹ `q ^ᶻ ω_p = q`（`zpowHat_idem_of_isProP`，在 `↥Q` 里算再沿子类型包含搬运，
  `map_zpowHat`）；
* `G` 由 `x` 拓扑生成 ⟹ `q = x ^ᶻ a`，于是

```
q = q ^ᶻ ω_p = (x ^ᶻ a) ^ᶻ ω_p = x ^ᶻ (a * ω_p) = x ^ᶻ (ω_p * a) = (x ^ᶻ ω_p) ^ᶻ a ∈ P_p .
```

**没有一步需要指数计算／主分解／逆极限投影** —— 幂等元 `ω_p` 把「取 `p`-部分」这个操作
内建成了 `ℤ̂` 的乘法。这正是 S42 R17 判定为「缺三样基建」的那件事的**替代品**。

**为什么必须先取 Sylow 再证 `Q ≤ P_p`**（而不是直接对「任意 `R ⊇ P_p`、`R` pro-`p`」用同一论证）：
`IsProP` **不蕴含闭性**（反例：`ℤ` 稠密嵌入 `ℤ̂`，`IsProP 2 ↥ℤ` 成立但 `ℤ` 不闭），
故 `zpowHat` 一般无法在 `↥R` 上使用。走「Sylow ⟹ 闭 ⟹ 可用 `zpowHat`」这条是**唯一无漏洞**的路。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`isProPSylow_closedZpowers_zpowHat_idem`** | ★★★★★ **procyclic 群的 ℓ-部分是它的 ℓ-Sylow** |
| **`padicEquiv_closedZpowers_zpowHat_idem`** | ★★★★★ 上述 ℓ-部分**无限** ⟹ `≅ₜ* Multiplicative ℤ_[p]` |
| **`inertiaProPSylowData_of_procyclic_group`** | ★★★★★ **（★）的 `InertiaProPSylowData`**（由「procyclic 生成元 ＋ ℓ-部分无限」） |
| **`cdLE_of_procyclic_group`** | ★★★★ 同一件事的上同调形态 `cd_p(I) ≤ 1`（经 `Hyp504`） |

## 诚实边界

* 本件给的是**抽象群论核心**：它把 S3c 化为**两条**关于具体群 `I_K/P_K ≅ ℤ̂^{(p')}(1)` 的输入：
  ① 它 procyclic（**已有**：`Hyp512` ＝ `exists_generator_primeToPTateModule`）；
  ② 其 `p`-部分 **无限**（下一件：`PrimeToPTateModule` 在 `p^k` 层的投影满射 ⟹ 层数无界）。
* 本件**不**处理 S2／S4（`I_K` 的 Sylow 与 `I_K/P_K` 的 Sylow 之间的关系）。
* **本件不给**（★）本身；`Ch4TameSymbolHyp`（一般 `K`）仍 `∅-open`。

## 侦察记录（L46／规则 23／24 的三件套）

* `grep -rn "zHat.idem\|zpowHat" raw/TauCeti/TauCeti/Topology/Algebra/Group/Profinite/{ZHat,Procyclic.lean}`
  ⟹ 命中上表七件。**扫过的目录**：`Profinite/ZHat/`（16 文件）、`Profinite/` 顶层、
  `Profinite/ProP/`（含 `Procyclic.lean`、`Basic.lean`）、`Profinite/Sylow/`（9 文件全部）；
* `python3 scratch/lean-l20261018/port_tau.py TauCeti.Topology.Algebra.Group.Profinite.Procyclic`
  ＋ `#check @<候选名>`（`.probe/p1.lean`／`.probe/p2.lean`）；
* **未**按名字猜：`IsProP.subgroup`／`zpowHat_idem_mul_of_isProP`／`map_zpowHat`／
  `isProPSylow_iff_isProP_and_maximal` 均由内容检索命中；
* mathlib 侧 `HasEnoughRootsOfUnity`／`Sylow` 亦已扫（见 `raw/fermats-last-theorem/.lake/packages/mathlib`）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- ★★★★★ **procyclic 群的 ℓ-部分是它的 ℓ-Sylow**。

设 `x` 拓扑生成 `G`（`closedZpowers x = ⊤`）。则 `P_p := closedZpowers (x ^ᶻ ω_p)`
（`ω_p = zHat.idem.{0} p`）是 `G` 的 Sylow pro-`p` 子群。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9626 quote="the $\ell$-Sylow subgroups of $H$ are isomorphic to $\mathbf{Z}_{\ell}$ for $\ell$ prime to $\operatorname{char}(\kappa(v))$"
theorem isProPSylow_closedZpowers_zpowHat_idem (p : ℕ) [Fact p.Prime] (x : G)
    (hx : closedZpowers x = ⊤) :
    IsProPSylow p (closedZpowers (x ^ᶻ zHat.idem.{0} p)) := by
  -- 已知的 Sylow `Q ⊇ P_p`；它闭，故可在其中用 `zpowHat`
  obtain ⟨Q, hQ, hPQ⟩ := (isProP_closedZpowers_zpowHat_idem p x).exists_le_isProPSylow
  have hQP : Q ≤ closedZpowers (x ^ᶻ zHat.idem.{0} p) := by
    intro q hq
    haveI : CompactSpace ↥Q := isCompact_iff_compactSpace.mp hQ.isClosed.isCompact
    -- ⑴ `q ∈ Q`、`Q` pro-`p` ⟹ `q ^ᶻ ω_p = q`（在 `↥Q` 里算，沿子类型包含搬运）
    have hfix : q ^ᶻ zHat.idem.{0} p = q := by
      let f : ↥Q →ₜ* G := ⟨Q.subtype, continuous_subtype_val⟩
      have h := congrArg f (zpowHat_idem_of_isProP (G := ↥Q) hQ.isProP ⟨q, hq⟩)
      rw [map_zpowHat] at h
      exact h
    -- ⑵ `G` 由 `x` 拓扑生成 ⟹ `q = x ^ᶻ a`
    obtain ⟨a, ha⟩ := mem_closedZpowers_iff.1 (hx ▸ Subgroup.mem_top q)
    rw [← ha] at hfix ⊢
    -- ⑶ 幂等元代数：`q = x ^ᶻ a = x ^ᶻ (a * ω_p) = x ^ᶻ (ω_p * a) = (x ^ᶻ ω_p) ^ᶻ a ∈ P_p`
    have hmul : x ^ᶻ (a * zHat.idem.{0} p) = x ^ᶻ a := by
      rw [zpowHat_mul]
      exact hfix
    rw [← hmul, mul_comm a (zHat.idem.{0} p), zpowHat_mul]
    exact zpowHat_mem (isClosed_closedZpowers (x ^ᶻ zHat.idem.{0} p)) (mem_closedZpowers _) a
  exact le_antisymm hQP hPQ ▸ hQ

/-- ★★★★★ **ℓ-部分无限 ⟹ `ℓ`-部分 ≅ `ℤ_p`**（`IsProP.padicPowEquiv`）。

生成元取 `⟨x ^ᶻ ω_p, _⟩`（`topologicallyGenerates_closedZpowers`），非挠性由无限性给出
（`Hyp508` 的 `not_isOfFinOrder_of_infinite`）。 -/
noncomputable def padicEquiv_closedZpowers_zpowHat_idem (p : ℕ) [Fact p.Prime] (x : G)
    (hx : closedZpowers x = ⊤) [Infinite ↥(closedZpowers (x ^ᶻ zHat.idem.{0} p))] :
    ↥(closedZpowers (x ^ᶻ zHat.idem.{0} p)) ≃ₜ* Multiplicative ℤ_[p] := by
  haveI hP : IsProP p ↥(closedZpowers (x ^ᶻ zHat.idem.{0} p)) :=
    isProP_closedZpowers_zpowHat_idem p x
  have hgen : (Subgroup.closure
      ({⟨x ^ᶻ zHat.idem.{0} p, mem_closedZpowers _⟩} :
        Set ↥(closedZpowers (x ^ᶻ zHat.idem.{0} p)))).topologicalClosure = ⊤ := by
    rw [← Subgroup.zpowers_eq_closure]
    exact topologicallyGenerates_closedZpowers (x ^ᶻ zHat.idem.{0} p)
  exact (hP.padicPowEquiv (a := ⟨x ^ᶻ zHat.idem.{0} p, mem_closedZpowers _⟩) hgen
    (not_isOfFinOrder_of_infinite _ hgen)).symm

/-- ★★★★★ **（★）的 `InertiaProPSylowData`，由「procyclic 生成元 ＋ ℓ-部分无限」给出**。

这是 S3c 的最终形态：只要在**惯性群的模型** `I_K/P_K ≅ ℤ̂^{(p')}(1)` 上找到一个
拓扑生成元 `x`，并证明它的 `p`-部分 `closedZpowers (x ^ᶻ ω_p)` 无限，即得 `InertiaProPSylowData`。 -/
noncomputable def inertiaProPSylowData_of_procyclic_group {I : Type} [Group I]
    [TopologicalSpace I] [IsTopologicalGroup I] [CompactSpace I] [TotallyDisconnectedSpace I]
    (p : ℕ) [Fact p.Prime] (x : I) (hx : closedZpowers x = ⊤)
    [Infinite ↥(closedZpowers (x ^ᶻ zHat.idem.{0} p))] :
    InertiaProPSylowData I p where
  P := closedZpowers (x ^ᶻ zHat.idem.{0} p)
  isProPSylow := isProPSylow_closedZpowers_zpowHat_idem p x hx
  padicEquiv := ⟨padicEquiv_closedZpowers_zpowHat_idem p x hx⟩

/-- ★★★★★ **同一件事的上同调形态**：`cd_p(I) ≤ 1`（经 `Hyp504`）。 -/
theorem cdLE_of_procyclic_group {I : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [CompactSpace I] [TotallyDisconnectedSpace I]
    (p : ℕ) [Fact p.Prime] (x : I) (hx : closedZpowers x = ⊤)
    [Infinite ↥(closedZpowers (x ^ᶻ zHat.idem.{0} p))] :
    CohomologicalDimensionLE.{0, 0} p I 1 :=
  (inertiaProPSylowData_of_procyclic_group p x hx).cdLE

end L20261018

#print axioms L20261018.isProPSylow_closedZpowers_zpowHat_idem
#print axioms L20261018.padicEquiv_closedZpowers_zpowHat_idem
#print axioms L20261018.inertiaProPSylowData_of_procyclic_group
#print axioms L20261018.cdLE_of_procyclic_group
