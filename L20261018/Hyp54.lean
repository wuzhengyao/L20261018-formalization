import L20261018.Hyp53
import TauCeti.Algebra.CentralSimple.Index
import TauCeti.Algebra.BrauerGroup.Division

/-!
# `(3)` 的 `(i)` 环：**`Algebra.index` 对 Brauer 等价不变**（侦察更正）

`STATUS.md`／`HANDOFF.md` 与 R846 的定界把 `(3)` 的 `(i)` 环记为

> `ind` 具体化为 Brauer 指数（`H² → Br → Algebra.index`）：**缺基建**：`Algebra.index`
> 对 Brauer 等价的不变性，库内 **0 命中**。

**这是错的**（L46 教训「『库无 X』几乎总是假的」的又一次实例）。TauCeti 的
`TauCeti/Algebra/CentralSimple/Index.lean` 恰好有这两条：

```lean
TauCeti.Algebra.index_eq_of_algEquiv (e : A ≃ₐ[K] B) : index K A = index K B
TauCeti.Algebra.index_matrix (n) [NeZero n]       : index K (Matrix (Fin n) (Fin n) A) = index K A
```

第二条就是 **Brauer 等价下的不变性**（Brauer 等价 = 差一个矩阵代数），第一条让它对呈现无交。
另有 `index_eq_deg_of_divisionRing`（除代数上 `index = deg`）、`index_dvd_deg`、`index_le_deg`。

⟹ **`(3)` 的 `(i)` 不是「缺基建」**：`ind` 只需定义为「代表代数的 `index`」，与本环无关。
`(3)` 的唯一实质缺口是 `(ii)`（`h = (a₁)∪(a₂)` 认成**符号代数的类**），那需要的正是
`(1b)` 的**等式形式**（`[(a,b)_F] = crossedProductClass c`）。

## 本文件

* `index_eq_of_algEquiv_matrix`：`A ≃ₐ M_n(B)` ⟹ `index A = index B`（Brauer 不变的直接形态）；
* `index_eq_of_mk_eq`：`mk (CSA.of K A) = mk (CSA.of K B)` ⟹ `index A = index B`
  （`ind` 作为 Brauer 类上的函数**良定**的精确陈述 = `(3)(i)` 的接口）。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolIndex

universe u

variable {K : Type u} [Field K]

open TauCeti

/-- **`index` 对矩阵扩张不变**（重述 `TauCeti.Algebra.index_matrix`）。 -/
theorem index_matrix {A : Type u} [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (n : ℕ) [NeZero n] :
    Algebra.index K (Matrix (Fin n) (Fin n) A) = Algebra.index K A :=
  TauCeti.Algebra.index_matrix (K := K) (A := A) n

/-- **Brauer 不变的直接形态**：`A ≃ₐ M_n(B)` ⟹ `index A = index B`。 -/
theorem index_eq_of_algEquiv_matrix {A B : Type u} [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B] [FiniteDimensional K B]
    {n : ℕ} [NeZero n] (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) B) :
    Algebra.index K A = Algebra.index K B := by
  rw [TauCeti.Algebra.index_eq_of_algEquiv (K := K) e, index_matrix]

/-- **`(3)(i)` 的接口**：`index` 只依赖 Brauer 类。

即：若两个中心单代数代表同一个 Brauer 类（`mk` 相等），则它们的 `index` 相等。
这使论文的 `ind : H²(F,μ_p) → ℕ` 可以**良定义**为「代表代数的 `index`」，与代表选取无关。 -/
theorem index_eq_of_mk_eq {A B : Type u} [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B] [FiniteDimensional K B]
    (h : TauCeti.BrauerGroup.mk (CSA.of K A) = TauCeti.BrauerGroup.mk (CSA.of K B)) :
    Algebra.index K A = Algebra.index K B := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := (TauCeti.BrauerGroup.mk_eq_mk_iff (K := K)).mp h
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero m := ⟨hm⟩
  rw [← index_matrix (K := K) (A := A) n, ← index_matrix (K := K) (A := B) m]
  exact TauCeti.Algebra.index_eq_of_algEquiv (K := K) e

end SymbolIndex
