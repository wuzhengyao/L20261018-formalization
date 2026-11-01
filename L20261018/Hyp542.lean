import L20261018.Hyp541

/-!
# S45 R2：★★★★ **造出 GS 的 `T`** —— `T = coker(A^S ↪ (Coind A)^S)`，`i : T ↪ C^S`

## 为什么要 `T`

(F1) 的核心恒等式 `Inf_2 ≫ (6.15) = δ_T ≫ i_*`（GS `prop-residue-map-long-exact` 证明末句：
「an easy compatibility between inflations and boundary maps」）要在 **`T` 处**取 `δ`：

* 若用 `Y := 0 → A^S → (Coind A)^S → C^S → 0`（`= X.map quotientToInvariantsFunctor`），
  `Y` **不是**短正合（`(Coind A)^S ↠ C^S` 需要 `H¹(S,A) = 0`，而战役只有 `H²(S,A) = 0`），
  故 `δ_Y` 不存在 ⟹ 此路**不通**（S45-STATUS §4 已登记）。
* 用 `T := im((Coind A)^S → C^S) = coker(A^S ↪ (Coind A)^S)`（`Y` 在中项正合 ⟹ 两种写法一致），
  则 `Y' := 0 → A^S → (Coind A)^S → T → 0` **无条件**短正合（GS (6.16)），`δ_T = (δ_{Y'})^{-1}` 存在。

GS (6.17) 左半、以及「`H^i(G/H,A^H) ≅ H^{i-1}(G/H,T)`（`i>1`）」全靠 `Y'`；GS 的 `T` 就是本件的 `tameImage`。

## 机检内容

| 声明 | 内容 |
|---|---|
| `qSES` | `G⧸S`-侧短复形 `A^S → (Coind A)^S → C^S`（`= X.map quotientToInvariantsFunctor`） |
| `qSES_X₁/_X₂/_X₃` | 载体锁定（`A^S`／`(Coind A)^S`／`C^S`），改一处即编译失败 |
| **`mono_qSES_f`** | `A^S ↪ (Coind A)^S`（`Mono`，GS (6.16) 的左端） |
| **`tameImage`** | ★ **GS 的 `T`** ＝ `coker(qSES.f)` |
| **`cokerSES`／`cokerSES_shortExact`** | ★★ `Y' : 0 → A^S → (Coind A)^S → T → 0` **短正合**（无条件） |
| **`iTame`** | `i : T ⟶ C^S`（由 `qSES.f ≫ qSES.g = 0` 经 `cokernel.desc` 诱导） |

## 诚实边界

* 本件**只造 `T`、`i`、`Y'` 与 `Y'` 的短正合性**；(F1) 的方块（`Φ'` ＋ `δ_naturality`）与
  `i ≫ deltaZeroBar = 0` **不在本件**（下一轮）。
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

/-- `G⧸S`-侧的短复形 `A^S → (Coind A)^S → C^S`：GS (6.16)＋(6.17) 合起来那条
「不是短正合、但在中项正合」的序列。 -/
noncomputable abbrev qSES (A : Rep k G) (S : Subgroup G) [S.Normal] :
    ShortComplex (Rep k (G ⧸ S)) :=
  (A.dimensionShiftUpSES).map (Rep.quotientToInvariantsFunctor k S)

/-- 载体锁定（源）：`qSES` 的 `X₁` 就是 `A^S`。 -/
theorem qSES_X₁ : (qSES A S).X₁ = A.quotientToInvariants S := (rfl)

/-- 载体锁定（中项）：`qSES` 的 `X₂` 就是 `(Coind A)^S`。 -/
theorem qSES_X₂ :
    (qSES A S).X₂ = (Rep.coindBot k G A.V).quotientToInvariants S := (rfl)

/-- 载体锁定（靶）：`qSES` 的 `X₃` 就是 `C^S`，`C = Rep.dimensionShiftUp A`。 -/
theorem qSES_X₃ :
    (qSES A S).X₃ = (Rep.dimensionShiftUp A).quotientToInvariants S := (rfl)

/-- ★★★ `A^S ↪ (Coind A)^S` —— GS (6.16) 的左端。

`qSES.f` 的底层是 `(A → Coind A).hom` 在不变元子模上的限制，故单。 -/
theorem mono_qSES_f : Mono (qSES A S).f := by
  rw [Rep.mono_iff_injective]
  intro x y hxy
  have hX : Function.Injective (Rep.Hom.hom (dimShiftSES A S).f) := by
    rw [← Rep.mono_iff_injective]
    exact (Rep.dimensionShiftUpSES_res_shortExact A S.subtype).mono_f
  refine Subtype.ext (hX ?_)
  exact congrArg Subtype.val hxy

/-- ★★★★★ **GS 的 `T`**：`T = coker(A^S ↪ (Coind A)^S) = im((Coind A)^S → C^S)`。

（后一等号用 `qSES` 在中项正合；本件不需要它，故未入机检。） -/
noncomputable abbrev tameImage (A : Rep k G) (S : Subgroup G) [S.Normal] : Rep k (G ⧸ S) :=
  cokernel (qSES A S).f

/-- ★★★★★ **`Y'`：`0 → A^S → (Coind A)^S → T → 0`**（GS (6.16)，**无条件**短正合）。

这是 **(F1)** 要用的那条短正合列；它的 `δ` 就是 GS 的 `δ_T^{-1}`。 -/
noncomputable abbrev cokerSES (A : Rep k G) (S : Subgroup G) [S.Normal] :
    ShortComplex (Rep k (G ⧸ S)) :=
  ShortComplex.mk (qSES A S).f (cokernel.π (qSES A S).f) (cokernel.condition (qSES A S).f)

/-- ★★★★★ **`Y'` 无条件短正合**（`Mono` ⟸ `mono_qSES_f`；`Epi` ⟸ `cokernel.π`）。 -/
theorem cokerSES_shortExact : (cokerSES A S).ShortExact := by
  haveI : Mono (cokerSES A S).f := mono_qSES_f A S
  exact ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (qSES A S).f)

/-- ★★★★ **`i : T ⟶ C^S`** —— GS (6.17) 左端的包含，由 `qSES.f ≫ qSES.g = 0` 诱导。 -/
noncomputable abbrev iTame (A : Rep k G) (S : Subgroup G) [S.Normal] :
    tameImage A S ⟶ (qSES A S).X₃ :=
  cokernel.desc (qSES A S).f (qSES A S).g (qSES A S).zero

/-- `i` 的定义式：`π ≫ i = qSES.g`（供下游 `rw`）。 -/
theorem cokernelπ_comp_iTame :
    cokernel.π (qSES A S).f ≫ iTame A S = (qSES A S).g :=
  cokernel.π_desc _ _ _

end L20261018

#print axioms L20261018.qSES_X₁
#print axioms L20261018.qSES_X₂
#print axioms L20261018.qSES_X₃
#print axioms L20261018.mono_qSES_f
#print axioms L20261018.cokerSES_shortExact
#print axioms L20261018.cokernelπ_comp_iTame
