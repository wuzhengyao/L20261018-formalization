import L20261018.Hyp98
import L20261018.Hyp92
import L20261018.Hyp93
/-!
# 3.6 组装（二）：`→+` → `→ₗ` 的转换器（R925）

`GaloFive.theorem_3_5_1_galo`／`Theo351.theorem_3_5_1_explicit` 给的是**加法**同态，
`A.theorem_3_6` 要 `LinearMap`。`ZMod p` 是域 ⟹ 纯量即 `nsmul` ⟹ 任何加性同态都线性：
关键就是 `Hyp92` 的 `addMonoidHom_map_zmod_smul`（它的陈述**正是** `map_smul'`）。

R924 的失败原因也已定位：`Hyp98` 只 import 了 `Hyp97`，继承不到 `Hyp92` ⟹ `unknown identifier`
（**不是**名字错）。本文件直接 `import Hyp92`。

## 主结果

* `toLinearMap`：`(M →+ N) → (M →ₗ[ZMod p] N)`；
* 保单射／满射／像／核。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {p : ℕ} [NeZero p]

/-- **`→+` 升成 `→ₗ[ZMod p]`**（`ZMod p` 是域 ⟹ 纯量即 `nsmul`）。 -/
noncomputable def toLinearMap {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (f : M →+ N) : M →ₗ[ZMod p] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := Theo352.addMonoidHom_map_zmod_smul (n := p) f c x

@[simp]
theorem toLinearMap_apply {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (f : M →+ N) (x : M) :
    toLinearMap (p := p) f x = f x :=
  rfl

/-- 线性化保单射。 -/
theorem toLinearMap_injective {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] {f : M →+ N} (hf : Function.Injective f) :
    Function.Injective (toLinearMap (p := p) f) :=
  hf

/-- 线性化保满射。 -/
theorem toLinearMap_surjective {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] {f : M →+ N} (hf : Function.Surjective f) :
    Function.Surjective (toLinearMap (p := p) f) :=
  hf

/-- 线性化保像（集合层）。 -/
theorem mem_range_toLinearMap_iff {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (f : M →+ N) (y : N) :
    y ∈ LinearMap.range (toLinearMap (p := p) f) ↔ y ∈ f.range :=
  Iff.rfl

/-- 线性化保核（集合层）。 -/
theorem mem_ker_toLinearMap_iff {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (f : M →+ N) (x : M) :
    x ∈ LinearMap.ker (toLinearMap (p := p) f) ↔ x ∈ f.ker :=
  Iff.rfl

end Assemble36

#print axioms Assemble36.toLinearMap
#print axioms Assemble36.mem_range_toLinearMap_iff
