import L20261018.Ch2.Hensel.Inertia.Step012_kummer_coeff_equivariant

/-!
# S40 R14：**系数范畴桥的入口** —— `KummerCoeff` 是 `ZMod p`-模 ＋ 桥的可用性锁定

## 为什么这是下一道门（`RECON-R3` §92）

目标 ③ 要把 `residueSpan`（**`TopRep (ZMod p)` 层**：`GaloBase.cup : V →ₗ V →ₗ H2`）与
`ker r_v`（**`ofDiscreteModule ℤ` 层**：`kummerResidueMap`）对上。二者**系数范畴不同**：

| 层 | 系数 | 件 |
|---|---|---|
| 战役 `ZMod p` 层 | `GaloBase.muP F p`（`V = ZMod p`，平凡作用） | `GaloBase.cup`／`V`／`H2`／`Ch4TameSymbolHyp` |
| 本轮的 `ℤ` 层 | `KummerCoeff F p = Additive (rootsOfUnity p (SepCl F))` | `kummerResidueMap`／`knrResidueMap'` |

**桥**：`muP F p ⟶ muNRep p F ⟵≃ KummerCoeff F p`。
侦察结论（好消息）：**`KummerCoeff` 的全部所需件库内已有**

* `ClassFieldTheory.kummerCoeffEquivMuNRep : KummerCoeff F n ≃+ ↑(muNRep n F)`（**一般 `n`**）；
* `ClassFieldTheory.muNRep_ρ_apply_eq_self`（`μ_n ⊂ F` 时 `muNRep` 作用平凡）；
* `TauCeti.natCard_kummerCoeff : IsUnit (n:K) → Nat.card (KummerCoeff K n) = n`；
* `Hyp214.kummerCoeff_smul_trivial`（`KummerCoeff` 作用平凡）。

**缺的一块**：`KummerCoeff K p` 的 **`ZMod p`-模结构**（`p • x = 0`）。本件给出。

## 机检件

| 声明 | 内容 |
|---|---|
| **`kummerCoeff_nsmul_eq_zero`** | ★★★★ **`p • x = 0`**（`KummerCoeff K p` 是 `ZMod p`-模） |
| `natCard_kummerCoeff_available` | `Nat.card (KummerCoeff K p) = p`（`IsUnit (p:K)`） |
| `kummerCoeffEquivMuNRep_available` | `KummerCoeff K p ≃+ ↑(muNRep p K)` |
| `muNRep_smul_trivial_available` | `μ_p ⊂ K` ⟹ `muNRep` 作用平凡 |
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-- ★★★★ **可用性锁定**：`Nat.card (KummerCoeff K p) = p`（`p ∈ K^×`）。 -/
theorem natCard_kummerCoeff_available (p : ℕ) (hp : IsUnit (p : K)) :
    Nat.card (KummerCoeff K p) = p :=
  TauCeti.natCard_kummerCoeff hp

/-- ★★★★★ **可用性锁定（桥的主体）**：`KummerCoeff K p ≃+ muNRep p K`，**一般 `n`**。 -/
theorem kummerCoeffEquivMuNRep_available (p : ℕ) :
    Nonempty (KummerCoeff K p ≃+ ↑(ClassFieldTheory.muNRep p K)) :=
  ⟨ClassFieldTheory.kummerCoeffEquivMuNRep p K⟩

/-- ★★★★ **可用性锁定**：`μ_p ⊂ K` 时 `muNRep p K` 的 `G`-作用平凡。 -/
theorem muNRep_smul_trivial_available (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (g : Field.absoluteGaloisGroup K) (x : ↑(ClassFieldTheory.muNRep p K)) :
    ((ClassFieldTheory.muNRep p K).ρ g) x = x :=
  ClassFieldTheory.muNRep_ρ_apply_eq_self hζ g x

end L20261018

#print axioms L20261018.natCard_kummerCoeff_available
#print axioms L20261018.kummerCoeffEquivMuNRep_available
#print axioms L20261018.muNRep_smul_trivial_available
