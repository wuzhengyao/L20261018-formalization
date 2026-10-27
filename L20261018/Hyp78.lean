import L20261018.Hyp76
/-!
# `(4)` 的无条件形式：两个绝对 Galois 群对**任意**域同构（R882 的侦察更正之更正）

R882（`ASSUMPTIONS.md` 第 87 轮）判定 `Field.absoluteGaloisGroup K = Gal(K̄/K)` 与
`TauCeti.AbsoluteGaloisGroup K = Gal(K^sep/K)` 相差一个**纯不可分**部分，
故「`K` 完美时才同构」，`Hyp73` 因此带上了 `[PerfectField K]`。**这个判定是错的。**

TauCeti 早已有一个**无条件**的典范同构（
`raw/TauCeti/TauCeti/FieldTheory/Galois/AbsoluteGaloisGroup/Basic.lean:325`）：

```lean
def absoluteGaloisGroupRestrictEquiv :
    Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K :=
  separableClosureRestrictEquiv K (AlgebraicClosure K)
```

其 docstring 逐字：「**Mathlib's absolute Galois group and `AbsoluteGaloisGroup` are the same
topological group**: restricting an automorphism of an algebraic closure of `K` to the separable
closure is an isomorphism `Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K`.」

**为什么无条件成立**：限制映射 `Gal(K̄/K) → Gal(K^sep/K)` 的核是 `Gal(K̄/K^sep)`，而
`K̄/K^sep` 是**纯不可分**扩张：每个元素 `x` 满足 `x^{p^n} ∈ K^sep`，而 `x` 是它在 `K̄` 中的
**唯一** `p^n` 次根（特征 `p`），故任何固定 `K^sep` 的自同构必须固定 `x`（等特征 `0` 时
`K̄ = K^sep`，平凡）。满射性由 `K^sep` 可分闭、`K̄` 代数闭给出（提升）。

⟹ `Hyp73.absoluteGaloisGroup_mulEquiv` 的 `[PerfectField K]` **是多余前提**，
本文件给出去掉它的无条件版本。

**教训**（`HANDOFF` §3 教训 1／18b 的第 N 次复现）：R882 只 `grep` 了
「两个闭包之间的桥」（0 命中）就判「库内无现成件」，而没有扫
`AbsoluteGaloisGroup/Basic.lean` 的 `## Main results`——**同构件一直在库**，只是名字叫
`absoluteGaloisGroupRestrictEquiv` 而不是 `SeparableClosure.equiv`。
-/

set_option linter.unusedSectionVars false

namespace SymbolCupBridge

open TauCeti

/-- **`(4)` 无条件版**：`Field.absoluteGaloisGroup K` 与 `TauCeti.AbsoluteGaloisGroup K`
对**任意**域 `K`（不要求完美）同构。 -/
theorem absoluteGaloisGroup_mulEquiv_unconditional (K : Type) [Field K] :
    Nonempty (Field.absoluteGaloisGroup K ≃* TauCeti.AbsoluteGaloisGroup K) :=
  ⟨TauCeti.absoluteGaloisGroupRestrictEquiv K⟩

/-- 拓扑群层面的无条件版（更强：`≃ₜ*`）。 -/
theorem absoluteGaloisGroup_continuousMulEquiv_unconditional (K : Type) [Field K] :
    Nonempty (Field.absoluteGaloisGroup K ≃ₜ* TauCeti.AbsoluteGaloisGroup K) :=
  ⟨TauCeti.absoluteGaloisGroupRestrictEquiv K⟩

/-- 该同构就是**限制映射**（TauCeti 的 `absoluteGaloisGroupRestrictEquiv_apply`）。 -/
theorem absoluteGaloisGroup_mulEquiv_apply (K : Type) [Field K]
    (σ : Field.absoluteGaloisGroup K) :
    (TauCeti.absoluteGaloisGroupRestrictEquiv K) σ
      = AlgEquiv.restrictNormalHom
          (separableClosure K (AlgebraicClosure K)) σ :=
  TauCeti.absoluteGaloisGroupRestrictEquiv_apply K σ

end SymbolCupBridge

#print axioms SymbolCupBridge.absoluteGaloisGroup_mulEquiv_unconditional
#print axioms SymbolCupBridge.absoluteGaloisGroup_continuousMulEquiv_unconditional
#print axioms SymbolCupBridge.absoluteGaloisGroup_mulEquiv_apply
