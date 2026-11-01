import Hyp539

/-!
# S45 R1：★★★★★ **(F2) 完成** —— `δ₀ ∘ (Coind^S ↠ C^S) = 0`（`T` 落在 `δ₀` 的核里）

## 本件在 GS 6.8 的哪一格

GS `prop-residue-map-long-exact` 的证明（`raw/GilleSzamuely2017.tex:9526` 起）把 (6.16)

`0 → A^H → M^G(A)^H → C^H → …`

拆成两条短正合列：

```
0 → A^H → M^G(A)^H → T → 0
0 → T   → C^H      → H¹(H,A) → 0        (6.17)
```

第二条在 `C^H` 处正合 ⟺ **`δ₀ : C^H → H¹(H,A)` 在 `T = im(M^G(A)^H → C^H)` 上为零**。
`T` 的底层正是 `H⁰(S, X₂) = X₂^S` 在 `X₃^S` 中的像（`X := 0 → A|_S → (Coind A)|_S → C|_S → 0`），
故 (6.17) 的右半就是下面这一条**态射等式**：

```
H⁰(S, X₂) --map X.g--> H⁰(S, X₃) --δ₀--> H¹(S, A|_S)   等于 0
```

## 证明：**一行** —— 它本就在库内的短正合列里

`δ₀ = groupCohomology.δ hX 0 1 rfl`（`hX` = `X.ShortExact`），而 `H⁰(S,X₂) → H⁰(S,X₃) → H¹(S,A)`
**就是** mathlib 的 `groupCohomology.mapShortComplex₃ hX rfl`（`L₁'`：`Hⁱ(X₂) → Hⁱ(X₃) → Hʲ(X₁)`），
它是 `ShortComplex`，其 `zero` 字段即 `f ≫ g = 0`。

⟹ 不需要 `δ₀_apply` 的元素公式（S44 三次实测都在那里卡在 `H0Iso` 的载体形状上），
也不需要任何 LES 正合性 API。**记法层之坑（KB 规则 26②）绕开：用复合形态，不碰元素层。**

## 与 `deltaZeroBar` 的关系（本件第二条）

`Hyp239.deltaZeroBar` 的底层线性映射就是 `δ₀ ∘ (H0Iso X.X₃).inv`。
把本件第一条的左端用 `map_id_comp_H0Iso_hom`（mathlib `Functoriality.lean:264`）拆开、
再用 `(H0Iso X.X₂)` 是 iso 消去，即得**线性映射层**的 `T`-消灭式
`coindCompDeltaZeroBar_eq_zero` —— 那是 (d) ＝ `∂₂ ∘ Inf = 0` 真正要消费的形状。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`deltaZero_coindBot_comp_coind`** | ★★★★★ **(F2)**：`map X.g 0 ≫ δ₀ = 0` |
| `dimShiftSES_X₁`／`_X₃` | 类型锁定：复合列两端身份（改一处即编译失败） |
| **`coindCompDeltaZeroBar_eq_zero`** | ★★★★ 线性映射层：`T ↪ C^S` 经 `δ₀∘H0Iso.inv` 为零 |

## 诚实边界

* 本件**只**给 (F2)。(d) 的另一半 (F1)（`HInfRes A S 2 ≫ deltaTwo_firstHalf'` 的识别）**不在**本件。
* 本件是 `S`-侧（`H⁰(S,·) → H¹(S,·)`）；搬到 `G⧸S`-侧要经 `map (id (G⧸S)) (deltaZeroBar) 1`，
  其相容性是 (d) 的组装步骤，见下一轮。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- 本件的短正合列：`0 → A|_S → (Coind A)|_S → C|_S → 0`（`C = Rep.dimensionShiftUp A`），
即 GS (6.14) 沿 `S ↪ G` 限制所得。 -/
noncomputable abbrev dimShiftSES (A : Rep k G) (S : Subgroup G) : ShortComplex (Rep k S) :=
  A.dimensionShiftUpSES.map (Rep.resFunctor S.subtype)

/-- 类型锁定（源端）：`dimShiftSES` 的 `X₁` 就是 `A|_S`。 -/
theorem dimShiftSES_X₁ : (dimShiftSES A S).X₁ = Rep.res S.subtype A := (rfl)

/-- 类型锁定（靶端）：`dimShiftSES` 的 `X₃` 就是 `C|_S`，`C = Rep.dimensionShiftUp A`。

改动任一处（例如误用 `A` 代 `C`）都会使本引理编译失败
（KB 规则 19／L39 的陈述保真机检形态之一）。 -/
theorem dimShiftSES_X₃ :
    (dimShiftSES A S).X₃ = Rep.res S.subtype (Rep.dimensionShiftUp A) := (rfl)

/-- ★★★★★ **(F2)（GS (6.17) 右半，`S`-侧）**：`δ₀` 在 `T = im(H⁰(S,Coind) → H⁰(S,C))` 上为零；
证明只用短正合列 `dimShiftSES A S` 在 `(0,1)` 处的 `mapShortComplex₃` 的 `zero` 字段。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:prop-residue-map-long-exact quote="0\to T\to C^{H}\to H^{1}(H,A)\to0. \tag{6.17}"
theorem deltaZero_coindBot_comp_coind :
    groupCohomology.map (MonoidHom.id S) (A := (dimShiftSES A S).X₂) (dimShiftSES A S).g 0
      ≫ deltaZero_coindBot A S = 0 :=
  (groupCohomology.mapShortComplex₃
    (Rep.dimensionShiftUpSES_res_shortExact A S.subtype) (i := 0) (j := 1) rfl).zero

/-- 记录定义：`δ₀` 就是 `dimShiftSES A S` 的 `δ`（供下游 `rw` 把两者对齐）。 -/
theorem deltaZero_coindBot_eq_δ :
    deltaZero_coindBot A S =
      groupCohomology.δ (Rep.dimensionShiftUpSES_res_shortExact A S.subtype) 0 1 rfl :=
  (rfl)

/-- ★★★★ **线性映射层（(d) 真正要消费的形状）**：`T ↪ C^S` 经 `δ₀ ∘ (H0Iso).inv` 为零。

`deltaZeroBar`（`Hyp239`）的底层线性映射 ＝ `δ₀ ∘ (H0Iso X.X₃).inv`，
故本式即「`deltaZeroBar` 在 `T = range(invariants.map X.g)` 上为零」——
`Rep k (G⧸S)` 里 `(T ↪ C^S) ≫ deltaZeroBar = 0` 的线性层亲本。 -/
theorem coindCompDeltaZeroBar_eq_zero :
    (Rep.invariantsFunctor k S).map (dimShiftSES A S).g
      ≫ (groupCohomology.H0Iso (dimShiftSES A S).X₃).inv
      ≫ deltaZero_coindBot A S = 0 := by
  have hmain := deltaZero_coindBot_comp_coind (k := k) (G := G) A S
  have hsplit : groupCohomology.map (MonoidHom.id S) (A := (dimShiftSES A S).X₂)
        (dimShiftSES A S).g 0 =
      (groupCohomology.H0Iso (dimShiftSES A S).X₂).hom
        ≫ ((Rep.invariantsFunctor k S).map (dimShiftSES A S).g
          ≫ (groupCohomology.H0Iso (dimShiftSES A S).X₃).inv) := by
    rw [← Category.assoc, ← groupCohomology.map_id_comp_H0Iso_hom (dimShiftSES A S).g,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hsplit] at hmain
  have h2 := congrArg (fun t => (groupCohomology.H0Iso (dimShiftSES A S).X₂).inv ≫ t) hmain
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using h2

end L20261018

#print axioms L20261018.dimShiftSES_X₁
#print axioms L20261018.dimShiftSES_X₃
#print axioms L20261018.deltaZero_coindBot_comp_coind
#print axioms L20261018.deltaZero_coindBot_eq_δ
#print axioms L20261018.coindCompDeltaZeroBar_eq_zero
