import Hyp759

/-!
# S72 R1：墙 1 的 **W3 归约** —— 「共轭作用平凡」只需在**一个**非零元素上验证

`explicitConj1 I g : H1 ↥I (ZMod p) →+ H1 ↥I (ZMod p)` 是**加性**的（`Conjugation/Basic.lean:176`）。
若 `x ≠ 0` 生成整个加性群（`AddSubgroup.zmultiples x = ⊤`），则

```
y = n • x  ⟹  explicitConj1 I g y = n • explicitConj1 I g x = n • x = y
```

⟹ 「共轭作用平凡」（W4）化归为**一条方程** `explicitConj1 I g x = x`（对一切 `g`）。
配合 `Hyp759.natCard_h1Inertia_eq`（`Nat.card = p` 素数），`x ≠ 0` 自动生成 ⟹
W4 的剩余义务 = 「那一条方程」。

## 交付

| 声明 | 内容 |
|---|---|
| **`conj1_eq_of_fixes_zmultiples_top`** | ★★★★ `zmultiples x = ⊤` ＋ `∀ g, g·x = x` ⟹ `∀ g y, g·y = y` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ **W3 归约**：共轭作用是加性的，故只需在一个**加性生成元**上验证。

（`y = n • x` ⟹ `g·y = n • (g·x) = n • x = y`。） -/
theorem conj1_eq_of_fixes_zmultiples_top
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hgen : AddSubgroup.zmultiples x = ⊤)
    (hfix : ∀ g : AbsoluteGaloisGroup F,
      explicitConj1 (inertiaLoc F) g x = x)
    (g : AbsoluteGaloisGroup F) (y : H1 ↥(inertiaLoc F) (ZMod p)) :
    explicitConj1 (inertiaLoc F) g y = y := by
  have hy : y ∈ AddSubgroup.zmultiples x := by rw [hgen]; exact AddSubgroup.mem_top y
  rw [AddSubgroup.mem_zmultiples_iff] at hy
  obtain ⟨n, rfl⟩ := hy
  rw [map_zsmul, hfix g]

end L20261018

#print axioms L20261018.conj1_eq_of_fixes_zmultiples_top
