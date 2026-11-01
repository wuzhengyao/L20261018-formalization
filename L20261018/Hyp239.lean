import Hyp238

/-!
# R1110（**★★★★★ (R2)-1 完成：`∂₂` 成为条件定理**）

## 里程碑

`PLAN-R2` §H-10 把 `∂₂` 拆成三段，其中 (3)-模层是**唯一**缺口；S31 前三轮把它拆成三块并逐块机检：

| 块 | 内容 | 件 |
|---|---|---|
| ① | `H^n(S,A)` 的 `G ⧸ S`-模结构（`innerConjTrivialIn ⟹ Rep k (G⧸S)`） | `Hyp236.h1RepQuot` |
| ② | `δ₀` 在共轭作用下的自然性 `δ₀ ≫ conjMap A = conjMap C ≫ δ₀` | `Hyp237.deltaZero_conj` |
| ③ | `H⁰(S,C) ≅ C^S` 与共轭作用相容 | `Hyp238.H0_conj` |

本轮把它们**组装**成

```
deltaZeroBar A S h :  (Rep.dimensionShiftUp A).quotientToInvariants S ⟶ h1RepQuot A S 1 h
deltaTwo A S hcd h :  H²(G,A) ⟶ H¹(G ⧸ S, H¹(S,A))
```

## 形状说明（**照原文，`∂₂` 是「映射」不是同构**）

GS 6.8.5（`raw/GilleSzamuely2017.tex:9498`）原文：
「…Lemma `lemma-conjugation-long-exact`. **Hence there are induced maps**
`H^{i-1}(G/H,C^{H}) → H^{i-1}(G/H,H^{1}(H,A))` for all `i ≥ 1`. Composing with the isomorphism (6.15)
we thus obtain a construction of the maps `∂^{i}` for `i>1`.」

⟹ `∂₂` 是 `H²(G,A) ⟶ H¹(G⧸S, H¹(S,A))`（`ModuleCat` 态射），**不是**同构。
（`PROMPT-S31` ④ 的 `≅` 按其自身括注「形状按实际需要调整」按原文改为 `⟶`。）

## 组装的三步（全部机检）

1. `deltaZeroBar` 的底层线性映射 = `δ₀ ∘ (H0Iso).inv`
   （`H0Iso : H⁰(S,C) ≅ C^S`，把 GS 的 `C^H → H¹(H,A)` 搬到不变元上）；
2. `Rep.Hom` 的等变性 = 对 `g : G ⧸ S` **lift 到 `g : G`**（`QuotientGroup.induction_on`），然后
   `h1RepQuot_ρ_mk`（靶侧作用 = `conjMap`）＋ `H0_conj`（源侧作用 = `conjMap C S g 0`）＋
   `deltaZero_conj`（两者夹住 `δ₀`）；
3. `deltaTwo` = `(deltaTwo_firstHalf A hcd).hom ≫ map (MonoidHom.id (G⧸S)) deltaZeroBar 1`
   —— 前半是 `Hyp229.deltaTwo_firstHalf : H²(G,A) ≅ H¹(G⧸S, C^S)`（`hcd : cd(S) ≤ 1` 的
   抽象形式），后半是本轮的 `Rep k (G⧸S)`-态射。

## 本轮

| 声明 | 内容 |
|---|---|
| **`quotientToInvariants_ρ_mk`** | `C^S` 在 `mk g` 处的作用 = `Rep.toInvariants` 在 `g` 处的作用 |
| **`deltaZeroBar`** | ★★★ `δ₀` 作为 `Rep k (G ⧸ S)`-态射 `C^S ⟶ H¹(S,A)` |
| **`deltaTwo`** | ★★★★★ **`∂₂ : H²(G,A) ⟶ H¹(G⧸S, H¹(S,A))`**（条件：`hcd` ＋ `innerConjTrivialIn`） |

**下一轮**：① 解除 `innerConjTrivialIn`（**(R2)-2**，移植连续侧 `InnerConjugation`）；
② GS 6.8.7 的**值公式层**（**(R2)-3**）。`∂₂` 本身的**存在性**已不再是缺口。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- `C^S`（`Rep.quotientToInvariants`）在 `mk g` 处的作用就是 `Rep.toInvariants` 在 `g` 处的作用
（`Representation.ofQuotient_coe_apply`）。 -/
theorem quotientToInvariants_ρ_mk (C : Rep k G) (S : Subgroup G) [S.Normal] (g : G)
    (z : (Rep.res S.subtype (Rep.dimensionShiftUp C)).ρ.invariants) :
    ((Rep.dimensionShiftUp C).quotientToInvariants S).ρ ((g : G ⧸ S)) z
      = (Rep.toInvariants (Rep.dimensionShiftUp C) S).ρ g z :=
  Representation.ofQuotient_coe_apply _ _ g z

/-- ★★★ **`δ₀` 作为 `Rep k (G ⧸ S)`-态射**：`C^S ⟶ H¹(S,A)`，底层 `δ₀ ∘ (H0Iso).inv`。

等变性（`Rep.Hom` 的 `isIntertwining'`）＝对 `g : G⧸S` 取 lift，用
`h1RepQuot_ρ_mk`（靶侧）＋ `H0_conj`（源侧）＋ `deltaZero_conj`（夹住 `δ₀`）。 -/
noncomputable def deltaZeroBar (A : Rep k G) (S : Subgroup G) [S.Normal]
    (h : innerConjTrivialIn A S 1) :
    (Rep.dimensionShiftUp A).quotientToInvariants S ⟶ h1RepQuot A S 1 h where
  hom' := LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (LinearMap.comp (deltaZero_coindBot A S).hom
      (ModuleCat.Hom.hom
        (groupCohomology.H0Iso (Rep.res S.subtype (Rep.dimensionShiftUp A))).inv))
    (fun g z => by
      induction g using QuotientGroup.induction_on with
      | H g =>
        show deltaZero_coindBot A S
            ((groupCohomology.H0Iso (Rep.res S.subtype (Rep.dimensionShiftUp A))).inv
              ((Rep.toInvariants (Rep.dimensionShiftUp A) S).ρ g z))
          = ((h1RepQuot A S 1 h).ρ ((g : G ⧸ S)))
            (deltaZero_coindBot A S
              ((groupCohomology.H0Iso (Rep.res S.subtype (Rep.dimensionShiftUp A))).inv z))
        rw [h1RepQuot_ρ_mk]
        rw [← H0_conj (Rep.dimensionShiftUp A) S g z]
        exact congrArg (fun t => t ((groupCohomology.H0Iso
          (Rep.res S.subtype (Rep.dimensionShiftUp A))).inv z)) (deltaZero_conj A S g).symm)

/-- ★★★★★ **(R2)-1 完成：`∂₂` 作为条件定理**。

`hcd : ∀ k' ≥ 2, H^{k'}(S,A) = 0`（＝ `cd(S) ≤ 1` 的抽象形式）＋ `h : innerConjTrivialIn A S 1`
⟹ `∂₂ : H²(G,A) ⟶ H¹(G⧸S, H¹(S,A))`。

**GS 原文的 `∂₂` 是映射不是同构**（`raw/GilleSzamuely2017.tex:9499` "there are induced maps"）。 -/
noncomputable def deltaTwo (A : Rep k G) (S : Subgroup G) [S.Normal]
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k'))
    (h : innerConjTrivialIn A S 1) :
    groupCohomology A 2 ⟶ groupCohomology (h1RepQuot A S 1 h) 1 :=
  (deltaTwo_firstHalf A hcd).hom ≫
    groupCohomology.map (MonoidHom.id (G ⧸ S)) (deltaZeroBar A S h) 1

/-- `deltaTwo` 的复合形式（记录定义，供下游展开）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9498 quote="Lemma \ref{lemma-conjugation-long-exact}. Hence there are induced maps"
theorem deltaTwo_eq (A : Rep k G) (S : Subgroup G) [S.Normal]
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k'))
    (h : innerConjTrivialIn A S 1) :
    deltaTwo A S hcd h =
      (deltaTwo_firstHalf A hcd).hom ≫
        groupCohomology.map (MonoidHom.id (G ⧸ S)) (deltaZeroBar A S h) 1 :=
  (rfl)

/-- **`deltaTwo` 的源/靶类型锁定**：它是一个函数 `H²(G,A) → H¹(G⧸S, H¹(S,A))`。
改动源或靶中的任何一处都会使本引理编译失败。 -/
noncomputable def deltaTwo_type_lock (A : Rep k G) (S : Subgroup G) [S.Normal]
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k'))
    (h : innerConjTrivialIn A S 1) :
    (↥(groupCohomology A 2) → ↥(groupCohomology (h1RepQuot A S 1 h) 1)) :=
  deltaTwo A S hcd h

/-- 类型锁定的另一半：`h1RepQuot A S 1 h` 的底层确实是 `H¹(S,A)`。 -/
theorem h1RepQuot_one_V (A : Rep k G) (S : Subgroup G) [S.Normal]
    (h : innerConjTrivialIn A S 1) :
    (h1RepQuot A S 1 h).V = ↥(groupCohomology (Rep.res S.subtype A) 1) :=
  (rfl)

end L20261018

#print axioms L20261018.quotientToInvariants_ρ_mk
#print axioms L20261018.deltaZeroBar
#print axioms L20261018.deltaTwo
#print axioms L20261018.deltaTwo_eq
#print axioms L20261018.deltaTwo_type_lock
#print axioms L20261018.h1RepQuot_one_V
