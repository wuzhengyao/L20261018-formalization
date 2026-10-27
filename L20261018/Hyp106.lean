import L20261018.Hyp105
import L20261018.Hyp92
/-!
# 3.6 组装（九）：第一条 SES 的**子模商**版本（R933）

`A.theorem_3_6` 的 `φ` 域是 `V ⧸ (B.U + N)`（**子模**商），而 `three_five_one_Bex`（R932）给的是
`V ⧸ ((B.U).toAddSubgroup ⊔ (Nsub).toAddSubgroup)`（**加法子群**商）。二者**命题相等但非 defeq**
（`submodule_sup_toAddSubgroup`，R926）。

**修法（本轮）**：用 `quotientAddEquivOfEq`（R928，是个**函数** `AddEquiv`）把域搬过去，
再用**函数式 `LinearMap`**（R932 的决定性修法）——两者都不携带 `AddMonoidHom` 的结构实例参数，
故不存在 R931 那类路径问题。

## 主结果

* `toLinearMapOfAddEquiv`：`(A ≃+ B) → (B →+ N) → (A →ₗ N)`；
* **`three_five_one_submodule`**：域的**子模商**版 SES。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {p : ℕ} [NeZero p] {V N : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [AddCommGroup N] [Module (ZMod p) N]

/-- **沿着 `AddEquiv` 把 `→+` 变成 `→ₗ`**（函数式构造，不碰 `AddMonoidHom` 的结构路径）。 -/
noncomputable def toLinearMapOfAddEquiv {A B : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] (e : A ≃+ B) (f : B →+ N) : A →ₗ[ZMod p] N where
  toFun x := f (e x)
  map_add' x y := by rw [e.map_add, f.map_add]
  map_smul' c x := by
    have hsc : e (c • x) = c • e x :=
      Theo352.addMonoidHom_map_zmod_smul (n := p) e.toAddMonoidHom c x
    rw [hsc]
    exact Theo352.addMonoidHom_map_zmod_smul (n := p) f c (e x)

/-- `toLinearMapOfAddEquiv` 保满射。 -/
theorem toLinearMapOfAddEquiv_surjective {A B : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] (e : A ≃+ B) {f : B →+ N}
    (hf : Function.Surjective f) : Function.Surjective (toLinearMapOfAddEquiv (p := p) e f) :=
  fun y => let ⟨x, hx⟩ := hf y; ⟨e.symm x, show f (e (e.symm x)) = y by
    rw [AddEquiv.apply_symm_apply]; exact hx⟩

/-- `toLinearMapOfAddEquiv` 保单射。 -/
theorem toLinearMapOfAddEquiv_injective {A B : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] (e : A ≃+ B) {f : B →+ N}
    (hf : Function.Injective f) : Function.Injective (toLinearMapOfAddEquiv (p := p) e f) :=
  fun x y h => e.injective (hf h)

end Assemble36

#print axioms Assemble36.toLinearMapOfAddEquiv
#print axioms Assemble36.toLinearMapOfAddEquiv_injective
