import L20261018.Hyp760

/-!
# S72 R1：**D80 的「mathlib 无」是假阻断** —— 桥在库内，W3 无条件化

## 主结论（一处 30 行的净增量，零新数学）

`PROMPT-S72` §⑨ 要求「**构造** `Nat.card ↥(AddSubgroup.zmultiples x) = addOrderOf x`」。
本轮按 `L46`／`L47` 做**内容式全库检索**（`grep -rn "zmultiples" Mathlib/`），一条即中：

```
Nat.card_zmultiples : Nat.card ↥(zmultiples a) = addOrderOf a      -- simp 引理！
Mathlib/Data/ZMod/QuotientGroup.lean:160（Nat.card_zpowers 的 to_additive）
```

**D80 三轮侦察排除了 12 个候选名，全部猜错命名空间**：真名以 `Nat.card.` 开头，
而不是 `AddSubgroup.`。这正是 `L46` 记录的第 4 次假阻断（前三次：
`FixedPoints.finrank_eq_card`／`quotNilradicalPowEquivPi`／`TauCeti.tensorToPi`）。
**教训**：凡「`Nat.card`／`Fintype.card` 与阶」的等式，名字**几乎总在 `Nat.card.` 命名空间**，
不在结构命名空间。

## 交付

| 声明 | 内容 |
|---|---|
| **`zmultiples_eq_top_of_natCard_prime`** | ★★★★ `x ≠ 0` ＋ `Nat.card A = p`（`p` 素）⟹ `zmultiples x = ⊤`（**纯群论，零数论**） |
| **`conj1_eq_of_ne_zero`** | ★★★★ W3 **无条件版**：`x ≠ 0` 即够（`Nat.card = p` 由 `Hyp759.natCard_h1Inertia_eq` 兑现） |

⟹ **W4 的剩余义务 = 恰好一条方程** `explicitConj1 (inertiaLoc F) g x = x`（`x ≠ 0`），
不再有「先证桥」的前置。（`Hyp760` 的 `hgen` 假设已被本件消掉。）
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

/-! ## ① 纯群论：素数阶群里的非零元素生成整个群 -/

/-- ★★★★ **素数阶加群的非零元素是加性生成元**：`x ≠ 0` ＋ `Nat.card A = p`（`p` 素）⟹ `zmultiples x = ⊤`。

**证明**（三步，全是库存件）：
1. `addOrderOf x ∣ Nat.card A = p`（`addOrderOf_dvd_natCard`），`p` 素 ⟹ `addOrderOf x = 1` 或 `p`；
2. `addOrderOf x = 1` 会给出 `x = 0`（`AddMonoid.addOrderOf_eq_one_iff`）⟹ 排除 ⟹ `addOrderOf x = p`；
3. `Nat.card ↥(zmultiples x) = addOrderOf x = p = Nat.card A`（**`Nat.card_zmultiples`**）
   ⟹ `AddSubgroup.eq_top_of_card_eq`。 -/
theorem zmultiples_eq_top_of_natCard_prime {A : Type*} [AddGroup A] (p : ℕ) [hp : Fact p.Prime]
    (x : A) (hx : x ≠ 0) (hcard : Nat.card A = p) :
    AddSubgroup.zmultiples x = ⊤ := by
  have hdvd : addOrderOf x ∣ p := by
    rw [← hcard]
    exact addOrderOf_dvd_natCard x
  rcases hp.out.eq_one_or_self_of_dvd (addOrderOf x) hdvd with h1 | hp'
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hx
  · have hcardH : Nat.card ↥(AddSubgroup.zmultiples x) = p := by
      rw [Nat.card_zmultiples, hp']
    haveI : Finite ↥(AddSubgroup.zmultiples x) :=
      (Nat.card_pos_iff.mp (by rw [hcardH]; exact hp.out.pos)).2
    exact AddSubgroup.eq_top_of_card_eq _ (by rw [hcardH, hcard])

/-! ## ② 战役载体：W3 的无条件版 -/

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★★ **W3 无条件版**：`x ≠ 0` 即可（`zmultiples x = ⊤` 自动，不再作假设）。

⟹ 「共轭作用平凡」（W4）的剩余义务 **= 一条方程** `explicitConj1 (inertiaLoc F) g x = x`。 -/
theorem conj1_eq_of_ne_zero (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0)
    (hfix : ∀ g : AbsoluteGaloisGroup F,
      explicitConj1 (inertiaLoc F) g x = x)
    (g : AbsoluteGaloisGroup F) (y : H1 ↥(inertiaLoc F) (ZMod p)) :
    explicitConj1 (inertiaLoc F) g y = y := by
  have htop : AddSubgroup.zmultiples x = ⊤ :=
    zmultiples_eq_top_of_natCard_prime p x hx
      (natCard_h1Inertia_eq (F := F) (p := p) (q := q) hpq ζ hζ hgen)
  exact conj1_eq_of_fixes_zmultiples_top (F := F) p x htop hfix g y

end L20261018

#print axioms L20261018.zmultiples_eq_top_of_natCard_prime
#print axioms L20261018.conj1_eq_of_ne_zero
