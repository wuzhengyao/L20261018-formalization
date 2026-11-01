import Hyp770

/-!
# S73 R3：★★★★★ **`H-conj1` 兑现——`F5` 第一半变为无条件**

## 是什么

`Hyp762.Conj1Trivial`（具名假设 **H-conj1**）自 S72 R2 起是 `prop:prelim-residue` 无条件化链条上
**唯一的剩余数学条件**（`Hyp767` 已把 `F5` 第一半做成「只差 `H-conj1`」）。本件把它**兑现**：

```lean
theorem conj1Trivial_of_tameChar (hpq : p ≠ q) : Conj1Trivial F p
```

**零新假设**——所有输入都是本战役既有件 ＋ TauCeti 库内件。

## 证明骨架（四步，全部已机检）

```
χ := tameCharLoc (Hyp770)      : ↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p)
  ✓ 非平凡（Hyp770.tameCharLoc_ne_one）
  ✓ Γ-共轭不变（Hyp770.tameCharLoc_conj）
  ⟹ x := H1EquivOfSmulEqSelf.symm (ofMul χ) : H1 ↥I (ZMod p)
  ✓ x ≠ 0（Equiv 单射 + χ ≠ 1）
  ✓ x ∈ H1ConjInvariants（mem_H1ConjInvariants_iff_of_smul_eq_self ⟸ χ 的共轭不变性）
  ⟹ explicitConj1 I g x = x  ∀ g（mem_H1ConjInvariants_iff）
  ⟹ Conj1Trivial（Hyp761.conj1_eq_of_ne_zero：Nat.card = p 素 ⟹ 一个非零不动点即够）
```

## 交付

| 声明 | 内容 |
|---|---|
| **`conj1Trivial_of_tameChar`** | ★★★★★ **`H-conj1` 无条件成立**（`Conj1Trivial F p`） |
| **`conjInvariants_eq_top`** | `H¹(I,ℤ/p)^Γ = ⊤`（`Hyp768` 的接口，现无条件） |
| **`coeffChangeEquiv_uncond`** | ★★★★★ **`F5` 第一半无条件**：`H¹(Γ⧸I, H¹(I,ℤ/p)) ≃+ H¹(Γ⧸I, ℤ/p)` |

## 诚实边界

* 载体仍是 `IsNonarchimedeanLocalField F`（完备）；论文 `F` 是 Hensel ⟹ **`C2` 仍待做**
  （与 `Hyp769`／`Hyp770` 同一条边界，**不是**本件引入的）。
* `coeffChangeEquiv_uncond` 仍带三条**技术实例**（`DiscreteTopology`／`IsTopologicalAddGroup`／
  `ContinuousSMul (Γ⧸I)`，`STARTUP` §3 已登记）；它们是**技术**，不是数学假设。
* 本件**不**动缺口 ②（`F5` 在显式模型的组装，须换载体，`D68`／`D69`）与缺口 ③（`hd_cup_pi`，GS 6.8.4）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★★★ **`H-conj1` 兑现（`Conj1Trivial` 无条件）**：`Γ` 在 `H¹(I, ℤ/p)` 上的共轭作用平凡。

**证明**：`χ := tameCharLoc` 非平凡且共轭不变（`Hyp770`）⟹ 它在 `H1EquivOfSmulEqSelf` 下的
对应类 `x` 非零且共轭不变（`mem_H1ConjInvariants_iff_of_smul_eq_self`）⟹ 由
`Hyp761.conj1_eq_of_ne_zero`（`Nat.card = p` 是素数 ⟹ 一个非零不动点即够）得全部。 -/
theorem conj1Trivial_of_tameChar (hpq : p ≠ q) : Conj1Trivial F p := by
  obtain ⟨ζ, hζ, hgen⟩ := exists_primitiveComponents (F := F)
  -- 系数作用在**环境群**与**子群**两层都是平凡的（`Hyp2` 的实例）
  have htrivG : ∀ (g : AbsoluteGaloisGroup F) (m : ZMod p), g • m = m := fun _ _ => rfl
  have htriv : ∀ (n : ↥(inertiaLoc F)) (m : ZMod p), n • m = m := fun _ _ => rfl
  set χ : ↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p) := tameCharLoc (F := F) p q hpq with hχ
  have hχne : χ ≠ 1 := tameCharLoc_ne_one (F := F) p q hpq
  set x : H1 ↥(inertiaLoc F) (ZMod p) :=
    (H1EquivOfSmulEqSelf (G := ↥(inertiaLoc F)) htriv).symm (Additive.ofMul χ) with hx
  refine conj1Trivial_of_ne_zero (F := F) (p := p) (q := q) hpq ζ hζ hgen x ?_ ?_
  · -- `x ≠ 0`：`H1EquivOfSmulEqSelf` 是加性等价，把 `χ ≠ 1` 搬成 `x ≠ 0`
    intro hx0
    apply hχne
    have h1 : (H1EquivOfSmulEqSelf (G := ↥(inertiaLoc F)) htriv) x = 0 := by rw [hx0]; rfl
    rw [hx] at h1
    simpa using h1
  · -- `x` 被共轭固定：由 `χ` 的共轭不变性经 `mem_H1ConjInvariants_iff_of_smul_eq_self`
    intro g
    have hmem : x ∈ H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) := by
      rw [mem_H1ConjInvariants_iff_of_smul_eq_self htrivG]
      intro g' n
      have hval : Additive.toMul ((H1EquivOfSmulEqSelf (G := ↥(inertiaLoc F)) htriv) x) = χ := by
        rw [hx]
        simp
      rw [hval]
      exact tameCharLoc_conj (F := F) p q hpq g' n
    exact (mem_H1ConjInvariants_iff (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)).mp hmem g

/-- ★★★★ **`H¹(I,ℤ/p)^Γ = ⊤`**（`Hyp768` 的接口形态，现无条件）。 -/
theorem conjInvariants_eq_top (hpq : p ≠ q) :
    H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) = ⊤ :=
  conjInvariants_eq_top_of_conj1Trivial (F := F) p (conj1Trivial_of_tameChar (F := F) p q hpq)

/-- ★★★★★ **`F5` 第一半（无条件）**：`H¹(Γ⧸I, H¹(I,ℤ/p)) ≃+ H¹(Γ⧸I, ℤ/p)`。

`Hyp767.coeffChangeEquiv` 的 `Conj1Trivial` 假设由 `conj1Trivial_of_tameChar` 兑现；
其余参数（生成元 `ζ`、非零元 `x`）照旧传入——它们是**构造**用的，不是假设。 -/
noncomputable def coeffChangeEquiv_uncond [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (H1 ↥(inertiaLoc F) (ZMod p))]
    (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) :
    H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p)) ≃+
      H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) :=
  coeffChangeEquiv (F := F) p q (conj1Trivial_of_tameChar (F := F) p q hpq) hpq ζ hζ hgen x hx

end L20261018

#print axioms L20261018.conj1Trivial_of_tameChar
#print axioms L20261018.conjInvariants_eq_top
#print axioms L20261018.coeffChangeEquiv_uncond
