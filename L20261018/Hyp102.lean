import L20261018.Hyp101
import L20261018.Hyp13
/-!
# 3.6 组装（五）：商沿子群等式搬运（R928）

`A.theorem_3_6` 的域是 `V ⧸ (B.U + N)`（**子模**商），而第一条 SES 的域是
`V ⧸ (span{(a₁),(a₂)}.toAddSubgroup ⊔ Ncor)`（**加法子群**商）。两者相差**一道命题等式**
（`U_alignment`，R926），不是 defeq ⟹ 需要搬运。

本文件给两个可复用的搬运件：

* `quotientAddEquivOfEq`：`A = B ⟹ (V ⧸ A) ≃+ (V ⧸ B)`；
* `addHomTransport`：`A = B` 时把 `V ⧸ A →+ N` 搬成 `V ⧸ B →+ N`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {V : Type*} [AddCommGroup V]

/-- **商沿子群等式搬运**：`A = B ⟹ (V ⧸ A) ≃+ (V ⧸ B)`。 -/
noncomputable def quotientAddEquivOfEq {A B : AddSubgroup V} (h : A = B) :
    (V ⧸ A) ≃+ (V ⧸ B) :=
  QuotientAddGroup.congr A B (AddEquiv.refl V) (by
    rw [h]
    simp)

/-- **加性同态沿子群等式搬运**：`A = B` 时把 `V ⧸ A →+ N` 搬成 `V ⧸ B →+ N`。 -/
noncomputable def addHomTransport {N : Type*} [AddCommGroup N] {A B : AddSubgroup V}
    (h : A = B) (f : (V ⧸ A) →+ N) : (V ⧸ B) →+ N :=
  f.comp (quotientAddEquivOfEq h).symm.toAddMonoidHom

@[simp]
theorem addHomTransport_apply {N : Type*} [AddCommGroup N] {A B : AddSubgroup V}
    (h : A = B) (f : (V ⧸ A) →+ N) (x : V ⧸ B) :
    addHomTransport h f x = f ((quotientAddEquivOfEq h).symm x) :=
  rfl

/-- 搬运保持单射。 -/
theorem addHomTransport_injective {N : Type*} [AddCommGroup N] {A B : AddSubgroup V}
    (h : A = B) {f : (V ⧸ A) →+ N} (hf : Function.Injective f) :
    Function.Injective (addHomTransport h f) :=
  hf.comp (quotientAddEquivOfEq h).symm.injective

/-- 搬运保持满射。 -/
theorem addHomTransport_surjective {N : Type*} [AddCommGroup N] {A B : AddSubgroup V}
    (h : A = B) {f : (V ⧸ A) →+ N} (hf : Function.Surjective f) :
    Function.Surjective (addHomTransport h f) :=
  hf.comp (quotientAddEquivOfEq h).symm.surjective

end Assemble36

#print axioms Assemble36.quotientAddEquivOfEq
#print axioms Assemble36.addHomTransport
#print axioms Assemble36.addHomTransport_injective
