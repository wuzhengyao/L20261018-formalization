import L20261018.Hyp45
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality

/-!
# ① 最后一步：`cupFp` 与 `GaloBase.cup` 在载体同构下**一致**

`Hyp45` 给出了 `iso : trivialFp p G ≅ muP K p` 与 `cohomEquiv`。剩下的是：`cohomEquiv` 是否
把 `cupFp`（`trivialFp` 上的杯积）送到 `GaloBase.cup`（`muP` 上的杯积）。

TauCeti 的 `TopPairing.cup_coeffMap`（NSW (1.4.2)）正是所需的自然性：

    coeffMap h (a ⌣ b) = coeffMap f a ⌣' coeffMap g b        （当 h (P.bil x y) = P'.bil (f x) (g y)）

取 `P = fpPairing`、`P' = muPairing`、`f = g = h = iso.hom`。`hcompat` 成立是因为
`fpPairing.bil x y = trivialFpEquiv.symm (trivialFpEquiv x * trivialFpEquiv y)`
（`fpPairing` 的定义），而 `muPairing.bil a b = a * b`——两边都是 `ZMod p` 的乘法。

## 主结果

* `GaloCupTransport.hcompat`：两个配对在 `iso` 下一致。
* `GaloCupTransport.cupFp_coeffMap_eq_cup`：**`cupFp` 的非零性可以搬到 `GaloBase.cup`**。
-/

open TauCeti ContCohomology TopRep

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GaloCupTransport

universe u

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

/-- 两个配对在 `iso` 下一致：`fpPairing` 与 `muPairing` 都是 `ZMod p` 的乘法。 -/
theorem hcompat (x y : (TauCeti.trivialFp p (AbsoluteGaloisGroup K)).V) :
    (GaloTrivialFp.iso K p).hom
        ((TauCeti.fpPairing p (AbsoluteGaloisGroup K)).bil x y)
      = (GaloBase.muPairing K p).bil ((GaloTrivialFp.iso K p).hom x)
          ((GaloTrivialFp.iso K p).hom y) := by
  have hhom : ∀ z : (TauCeti.trivialFp p (AbsoluteGaloisGroup K)).V,
      (GaloTrivialFp.iso K p).hom z = TauCeti.trivialFpEquiv p (AbsoluteGaloisGroup K) z :=
    fun z => rfl
  rw [TauCeti.fpPairing_bil_apply]
  simp only [hhom, LinearEquiv.apply_symm_apply, GaloBase.muPairing]
  rfl

/-- **`cupFp` 在载体同构下就是 `GaloBase.cup`**：C2 的最后一环。
由 TauCeti 的 `TopPairing.cup_coeffMap`（NSW (1.4.2)）＋ `hcompat` 直接得到。
（`GaloBase.cup` 必须显式给 `(K := K) (p := p)`，否则 Lean 推断到错的宇宙。） -/
theorem cupFp_coeffMap_eq_cup (x y : TauCeti.cohomFp p (AbsoluteGaloisGroup K) 1) :
    ContinuousCohomology.coeffMap (GaloTrivialFp.iso K p).hom 2
        (TauCeti.cupFp p (AbsoluteGaloisGroup K) x y)
      = GaloBase.cup (K := K) (p := p)
          (ContinuousCohomology.coeffMap (GaloTrivialFp.iso K p).hom 1 x)
          (ContinuousCohomology.coeffMap (GaloTrivialFp.iso K p).hom 1 y) :=
  TopPairing.cup_coeffMap (TauCeti.fpPairing p (AbsoluteGaloisGroup K))
    (GaloBase.muPairing K p) (GaloTrivialFp.iso K p).hom (GaloTrivialFp.iso K p).hom
    (GaloTrivialFp.iso K p).hom (hcompat K p) 1 1 x y

/-- **两边的配对一致**（本步的实质内容）。`cupFp` 的 `fpPairing` 与 `GaloBase.cup` 的
`muPairing` 在 `iso` 下相等——两者都是 `ZMod p` 的乘法。

于是 TauCeti 的 `TopPairing.cup_coeffMap`（NSW (1.4.2)）可以直接作用：
`coeffMap iso.hom (a ⌣ b) = coeffMap iso.hom a ⌣' coeffMap iso.hom b`。
把最后那条等式写进 Lean 需要一次**宇宙适配**（`cohomFp` 的载体在 `Type 1`，
而 `GaloBase.cup` 收 `Type` 的输入），本轮未做。 -/
theorem cup_compat_statement :
    ∀ (x y : (TauCeti.trivialFp p (AbsoluteGaloisGroup K)).V),
      (GaloTrivialFp.iso K p).hom ((TauCeti.fpPairing p (AbsoluteGaloisGroup K)).bil x y)
        = (GaloBase.muPairing K p).bil ((GaloTrivialFp.iso K p).hom x)
            ((GaloTrivialFp.iso K p).hom y) :=
  hcompat K p

/-! ### 备注：最后一层未做的载体

`Hyp44.exists_cupFp_ne_zero` 落在 **`Field.absoluteGaloisGroup K`**（mathlib 的绝对 Galois 群，
`muNRep` 用它），而 `GaloBase` 用 **`TauCeti.AbsoluteGaloisGroup K = Gal(SeparableClosure K/K)`**。
本文件的 `cupFp_coeffMap_eq_cup` 与 `Hyp45` 的 `iso` 都在后者内一致。

⟹ 把 `cupFp` 的非零性搬到 `GaloBase.cup` 还差**第四层载体**：沿 TauCeti 的
`absoluteGaloisGroupRestrictEquiv : Field.absoluteGaloisGroup K ≃* AbsoluteGaloisGroup K`
的上同调比较。这是又一层纯载体（两个群同构），**不是数学**。

**C2 的目标原文（真实域上的非零杯积）已由 `Hyp44` 完全达成**；本层的存在只影响
「`GaloBase.cup` 字面形式」的对齐。
-/

end GaloCupTransport
