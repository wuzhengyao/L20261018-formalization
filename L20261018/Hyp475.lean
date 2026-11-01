import L20261018.Hyp474

/-!
# S40 R15：系数范畴桥的两块 — `ZMod p`-模结构 ＋ **环变更件已在库**

## 本轮补的两块（`RECON-R3` §92.3／§92.4）

**(1) `KummerCoeff K p` 的 `ZMod p`-模结构**：`p • x = 0`（`x` 是 `p` 次单位根）。

**(2) ★ 环变更件（`ℤ` ↔ `k`）库内已有**：

```lean
TauCeti.ContCohomology.restrictScalarsIntEquiv (X : TopRep k G) (n) :
  H^n(TopRep.restrictScalarsInt.obj X) ≃+ ↑(continuousCohomology n X).toModuleCat
```

（`RestrictScalars.lean`，文件头自述 "Continuous cohomology does not see the scalars"。）
⟹ §92.4 的「环变更 1–2 轮」**降为 0 轮**（只需接线）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`kummerCoeff_nsmul_eq_zero`** | ★★★★ **`p • x = 0`**（`KummerCoeff K p` 是 `ZMod p`-模） |
| **`restrictScalarsInt_available`** | ★★★★★ **`H^n(restrictScalarsInt X) ≃+ H^n(X)`**（环变更件锁定） |
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-- ★★★★ **`KummerCoeff K p` 是 `ZMod p`-模**：`p • x = 0`。 -/
theorem kummerCoeff_nsmul_eq_zero (p : ℕ) (x : KummerCoeff K p) : p • x = 0 := by
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective x
  have h : ((a : (SeparableClosure K)ˣ)) ^ p = 1 :=
    (mem_rootsOfUnity p (a : (SeparableClosure K)ˣ)).mp a.2
  have h' : a ^ p = 1 := Subtype.ext (by simpa using h)
  show Additive.ofMul (a ^ p) = Additive.ofMul 1
  exact congrArg Additive.ofMul h'

/-- ★★★★★ **可用性锁定（环变更件）**：连续上同调**看不见**系数环 ——
`H^n(restrictScalarsInt X) ≃+ H^n(X)`。出处 `TauCeti.ContCohomology.restrictScalarsIntEquiv`。 -/
theorem restrictScalarsInt_available {k : Type} [Ring k] [TopologicalSpace k]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : TopRep k G) (n : ℕ) :
    Nonempty (↑(continuousCohomology n (TopRep.restrictScalarsInt.obj X)).toModuleCat ≃+
      ↑(continuousCohomology n X).toModuleCat) :=
  ⟨ContCohomology.restrictScalarsIntEquiv X n⟩

end L20261018

#print axioms L20261018.kummerCoeff_nsmul_eq_zero
#print axioms L20261018.restrictScalarsInt_available
